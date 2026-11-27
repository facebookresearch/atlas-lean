/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.GeneralizedSchreierPadovan
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Counting maximal Schreier sets

The number of maximal Schreier sets with a given maximum has a binomial closed form and
satisfies the alternating binomial recurrence of Chu and Vasseur.
-/

namespace MetaMathlibExt.maximalSchreierCount_formula_and_recurrence

open Finset

/-- Count with an offset in the cardinality constraint, to track finite differences. -/
private def family (p q t n : ℕ) : Finset (Finset ℕ) :=
  (Icc 1 n).powerset.filter fun F =>
    n ∈ F ∧ ∃ a ∈ F, F ⊆ Icc a n ∧ q * a = p * (F.card + t)

private theorem mem_family {p q t n : ℕ} {F : Finset ℕ} :
    F ∈ family p q t n ↔
      n ∈ F ∧ ∃ a ∈ F, 0 < a ∧ F ⊆ Icc a n ∧ q * a = p * (F.card + t) := by
  simp only [family, mem_filter, mem_powerset, subset_iff, mem_Icc]
  grind

private theorem card_family_zero {p q : ℕ} (hq : 0 < q) (n : ℕ) :
    (family p q 0 n).card = maximalSchreierCount p q n := by
  unfold maximalSchreierCount
  congr 1
  ext F
  simp only [mem_family, mem_filter, mem_powerset, subset_iff, mem_Icc, Nat.add_zero]
  constructor
  · rintro ⟨hn, a, ha, hpos, hb, he⟩
    exact ⟨fun x hx => ⟨hpos.trans_le (hb hx).1, (hb hx).2⟩, hn,
      fun x hx => he ▸ Nat.mul_le_mul_left q (hb hx).1, a, ha, he⟩
  · rintro ⟨hb, hn, hmin, a, ha, he⟩
    refine ⟨hn, a, ha, (hb ha).1, fun x hx => ⟨?_, (hb hx).2⟩, he⟩
    exact (Nat.le_of_mul_le_mul_left (he.symm ▸ hmin x hx) hq)

private theorem reduced_indices {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (a b : ℕ) :
    q * a = p * b ↔ ∃ k, a = p / p.gcd q * k ∧ b = q / p.gcd q * k := by
  let g := p.gcd q
  let r := p / g
  let s := q / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left q hp
  have hs : 0 < s := Nat.div_pos (Nat.gcd_le_right p hq) hg
  have hrp : g * r = p := Nat.mul_div_cancel' (Nat.gcd_dvd_left p q)
  have hsq : g * s = q := Nat.mul_div_cancel' (Nat.gcd_dvd_right p q)
  have hc : r.Coprime s := Nat.coprime_div_gcd_div_gcd hg
  change q * a = p * b ↔ ∃ k, a = r * k ∧ b = s * k
  rw [← hsq, ← hrp, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_right_inj hg.ne']
  constructor
  · intro h
    obtain ⟨k, hk⟩ := hc.symm.dvd_of_dvd_mul_left (h ▸ dvd_mul_right s a)
    refine ⟨k, Nat.eq_of_mul_eq_mul_left hs ?_, hk⟩
    rw [h, hk, mul_left_comm]
  · rintro ⟨k, rfl, rfl⟩
    exact mul_left_comm ..

/-- Removing the two endpoints identifies a fiber with subsets of the open interval. -/
private theorem card_endpoints {a n b : ℕ} (han : a < n) (hb : 2 ≤ b) (S : Finset (Finset ℕ))
    (hS : ∀ F, F ∈ S ↔ a ∈ F ∧ n ∈ F ∧ F ⊆ Icc a n ∧ F.card = b) :
    S.card = (n - a - 1).choose (b - 2) := by
  rw [← Nat.card_Ioo a n, ← card_powersetCard]
  apply card_nbij' (fun F => (F.erase a).erase n) (fun T => insert a (insert n T))
  · intro F hF
    obtain ⟨ha, hn, hsub, hcard⟩ := (hS F).mp hF
    have hn' : n ∈ F.erase a := mem_erase.mpr ⟨han.ne', hn⟩
    simp only [mem_coe, mem_powersetCard, card_erase_of_mem hn', card_erase_of_mem ha, hcard]
    simp only [subset_iff, mem_erase, mem_Ioo, mem_Icc] at *
    grind
  · intro T hT
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hT
    have hn : n ∉ T := fun h => (mem_Ioo.mp (hsub h)).2.false
    have ha : a ∉ insert n T := by
      simp [han.ne, show a ∉ T from fun h => (mem_Ioo.mp (hsub h)).1.false]
    apply (hS _).mpr
    simp only [mem_insert, true_or, or_true, true_and, card_insert_of_notMem ha,
      card_insert_of_notMem hn, hcard]
    simp only [subset_iff, mem_insert, mem_Ioo, mem_Icc] at *
    grind
  · intro F hF
    obtain ⟨ha, hn, -, -⟩ := (hS F).mp hF
    ext x
    simp only [mem_insert, mem_erase]
    grind
  · intro T hT
    have hsub := (mem_powersetCard.mp hT).1
    ext x
    simp only [subset_iff, mem_Ioo, mem_erase, mem_insert] at *
    grind

private theorem formula {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (n : ℕ) :
    let r := p / p.gcd q
    let s := q / p.gcd q
    maximalSchreierCount p q n =
      ∑ k ∈ (Icc 1 ((n + 1) / (r + s))).filter (fun k => 2 ≤ s * k),
        (n - r * k - 1).choose (s * k - 2) + if s = 1 ∧ n = r then 1 else 0 := by
  intro r s
  have hg := Nat.gcd_pos_of_pos_left q hp
  have hr : 0 < r := Nat.div_pos (Nat.gcd_le_left q hp) hg
  have hs : 0 < s := Nat.div_pos (Nat.gcd_le_right p hq) hg
  let S := family p q 0 n
  have hmem (F : Finset ℕ) : F ∈ S ↔
      ∃ k, 0 < k ∧ F.card = s * k ∧ r * k ∈ F ∧ n ∈ F ∧ F ⊆ Icc (r * k) n := by
    rw [mem_family]
    simp only [Nat.add_zero, reduced_indices hp hq]
    constructor
    · rintro ⟨hn, a, ha, hpos, hsub, k, rfl, hcard⟩
      exact ⟨k, Nat.pos_of_mul_pos_left hpos, hcard, ha, hn, hsub⟩
    · rintro ⟨k, hk, hcard, ha, hn, hsub⟩
      exact ⟨hn, r * k, ha, Nat.mul_pos hr hk, hsub, k, rfl, hcard⟩
  -- For nonsingletons the size determines k and the two endpoints are distinct.
  let large := S.filter (fun F => 2 ≤ F.card)
  let indices := (Icc 1 ((n + 1) / (r + s))).filter (fun k => 2 ≤ s * k)
  have index_mem : Set.MapsTo (fun F : Finset ℕ => F.card / s) large indices := by
    intro F hF
    obtain ⟨hF, hb⟩ := mem_filter.mp hF
    obtain ⟨k, hk, hcard, ha, -, hsub⟩ := (hmem F).mp hF
    have hbound := card_le_card hsub
    have han := (mem_Icc.mp (hsub ha)).2
    rw [Nat.card_Icc, hcard] at hbound
    change F.card / s ∈ indices
    rw [hcard, Nat.mul_div_cancel_left _ hs]
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hk, (Nat.le_div_iff_mul_le (by omega)).mpr ?_⟩,
      hcard ▸ hb⟩
    rw [Nat.mul_comm, Nat.add_mul]
    omega
  have hlarge : large.card = ∑ k ∈ indices, (n - r * k - 1).choose (s * k - 2) := by
    rw [card_eq_sum_card_fiberwise index_mem]
    apply sum_congr rfl
    intro k hki
    obtain ⟨hki, hb⟩ := mem_filter.mp hki
    obtain ⟨hk, hbound⟩ := mem_Icc.mp hki
    have hkn := (Nat.le_div_iff_mul_le (by omega)).mp hbound
    rw [Nat.mul_comm, Nat.add_mul] at hkn
    apply card_endpoints (by omega) hb
    intro F
    change F ∈ (large.filter fun F => F.card / s = k) ↔ _
    simp only [large, mem_filter, hmem]
    constructor
    · rintro ⟨⟨⟨j, -, hc, ha, hn, hsub⟩, -⟩, hidx⟩
      rw [hc, Nat.mul_div_cancel_left _ hs] at hidx
      subst j
      exact ⟨ha, hn, hsub, hc⟩
    · rintro ⟨ha, hn, hsub, hc⟩
      exact ⟨⟨⟨k, hk, hc, ha, hn, hsub⟩, hc ▸ hb⟩, hc ▸ Nat.mul_div_cancel_left _ hs⟩
  have hsmall : (S.filter fun F => ¬2 ≤ F.card) =
      if s = 1 ∧ n = r then {{n}} else ∅ := by
    ext F
    simp only [mem_filter, hmem]
    constructor
    · rintro ⟨⟨k, hk, hc, ha, hn, -⟩, hb⟩
      have hpos := Nat.mul_pos hs hk
      have hone : s * k = 1 := by omega
      obtain ⟨hs', hk'⟩ : s = 1 ∧ k = 1 := by simpa using hone
      have ha' : r ∈ F := by simpa [hk'] using ha
      have hnr := card_le_one.mp (by omega : F.card ≤ 1) n hn r ha'
      rw [ite_eq_left ⟨hs', hnr⟩, mem_singleton]
      ext x
      simpa only [mem_singleton] using
        (show x ∈ F ↔ x = n from ⟨fun hx => card_le_one.mp (by omega) x hx n hn,
          fun h => h ▸ hn⟩)
    · split
      · rintro h
        obtain rfl := mem_singleton.mp h
        obtain ⟨hs', hn⟩ := ‹s = 1 ∧ n = r›
        refine ⟨⟨1, by decide, by simp [hs'], by simp [hn], by simp, by simp [hn]⟩, by simp⟩
      · simp
  rw [← card_family_zero hq,
    ← card_filter_add_card_filter_not (s := S) (fun F => 2 ≤ F.card), hsmall]
  change large.card + _ = _
  rw [hlarge]
  split <;> simp [indices]

/-- Above the singleton range, moving the maximum past no other element preserves the
cardinality and the minimum. -/
private theorem replace_max {p q t n m : ℕ} {F : Finset ℕ} (ht : t < q) (hpn : p < n)
    (hF : F ∈ family p q t n) (hbelow : ∀ x ∈ F, x ≠ n → x < m) :
    insert m (F.erase n) ∈ family p q t m := by
  obtain ⟨hn, a, ha, hpos, hsub, he⟩ := mem_family.mp hF
  have han : a ≠ n := by
    rintro rfl
    have hone : F = {a} := by
      ext x
      simp only [subset_iff, mem_Icc, mem_singleton] at *
      grind
    rw [hone, card_singleton] at he
    -- A singleton here would give q * n ≤ p * q despite p < n.
    have hle := Nat.mul_le_mul_left p (show 1 + t ≤ q by omega)
    have hlt := Nat.mul_lt_mul_of_pos_right hpn (show 0 < q by omega)
    rw [Nat.mul_comm q] at he
    omega
  have hm : m ∉ F.erase n := by
    intro h
    exact (hbelow m (mem_erase.mp h).2 (mem_erase.mp h).1).false
  have hcard := card_pos.mpr ⟨n, hn⟩
  apply mem_family.mpr
  refine ⟨mem_insert_self .., a, mem_insert_of_mem (mem_erase.mpr ⟨han, ha⟩), hpos, ?_, ?_⟩
  · intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_Icc.mpr ⟨(hbelow a ha han).le, le_rfl⟩
    · obtain ⟨hxn, hx⟩ := mem_erase.mp hx
      exact mem_Icc.mpr ⟨(mem_Icc.mp (hsub hx)).1, (hbelow x hx hxn).le⟩
  · rwa [card_insert_of_notMem hm, card_erase_of_mem hn, Nat.sub_add_cancel hcard]

private theorem difference_step {p q t m : ℕ} (ht : t < q) (hm : p < m) :
    (family p q t (m + 1)).card = (family p q t m).card + (family p q (t + 1) m).card := by
  let S := family p q t (m + 1)
  have withPrev : (S.filter fun F => m ∈ F).card = (family p q (t + 1) m).card := by
    apply card_nbij' (fun F => F.erase (m + 1)) (insert (m + 1))
    · intro F hF
      obtain ⟨hF, hmF⟩ := mem_filter.mp hF
      obtain ⟨hn, a, ha, hpos, hsub, he⟩ := mem_family.mp hF
      have ham := (mem_Icc.mp (hsub hmF)).1
      have hcard := card_pos.mpr ⟨m, hmF⟩
      refine mem_family.mpr ⟨mem_erase.mpr ⟨by omega, hmF⟩, a, mem_erase.mpr ⟨by omega, ha⟩,
        hpos, ?_, ?_⟩
      · simp only [subset_iff, mem_erase, mem_Icc] at *
        grind
      · rw [card_erase_of_mem hn, show F.card - 1 + (t + 1) = F.card + t by omega]
        exact he
    · intro F hF
      obtain ⟨hmF, a, ha, hpos, hsub, he⟩ := mem_family.mp hF
      have hnew : m + 1 ∉ F := fun h => (Nat.not_succ_le_self m) (mem_Icc.mp (hsub h)).2
      refine mem_filter.mpr ⟨mem_family.mpr ⟨mem_insert_self .., a, mem_insert_of_mem ha,
        hpos, ?_, ?_⟩, mem_insert_of_mem hmF⟩
      · simp only [subset_iff, mem_insert, mem_Icc] at *
        grind
      · rwa [card_insert_of_notMem hnew, show F.card + 1 + t = F.card + (t + 1) by omega]
    · intro F hF
      exact insert_erase (mem_family.mp (mem_filter.mp hF).1).1
    · intro F hF
      obtain ⟨-, a, -, -, hsub, -⟩ := mem_family.mp hF
      apply erase_insert
      intro h
      have := (mem_Icc.mp (hsub h)).2
      omega
  have withoutPrev : (S.filter fun F => m ∉ F).card = (family p q t m).card := by
    apply card_nbij' (fun F => insert m (F.erase (m + 1))) (fun F => insert (m + 1) (F.erase m))
    · intro F hF
      obtain ⟨hF, hmF⟩ := mem_filter.mp hF
      apply replace_max ht (by omega : p < m + 1) hF
      obtain ⟨-, a, -, -, hsub, -⟩ := mem_family.mp hF
      intro x hx hxn
      have := (mem_Icc.mp (hsub hx)).2
      grind
    · intro F hF
      refine mem_filter.mpr ⟨replace_max ht hm hF ?_, by simp⟩
      obtain ⟨-, a, -, -, hsub, -⟩ := mem_family.mp hF
      intro x hx _
      exact Nat.lt_succ_of_le (mem_Icc.mp (hsub hx)).2
    · intro F hF
      obtain ⟨hF, hmF⟩ := mem_filter.mp hF
      have hnF := (mem_family.mp hF).1
      ext x
      simp only [mem_insert, mem_erase]
      grind
    · intro F hF
      obtain ⟨hmF, a, -, -, hsub, -⟩ := mem_family.mp hF
      ext x
      simp only [mem_insert, mem_erase, subset_iff, mem_Icc] at *
      grind
  rw [← withPrev, ← withoutPrev, add_comm (card _), card_filter_add_card_filter_not]

/-- Translating every element by `p` adds `p*q` to the minimum constraint. -/
private theorem translate {p q : ℕ} (hp : 0 < p) (m : ℕ) :
    (family p q 0 m).card = (family p q q (m + p)).card := by
  let lift (F : Finset ℕ) := F.image (· + p)
  have hinj : Function.Injective (fun x : ℕ => x + p) := fun _ _ h => Nat.add_right_cancel h
  have hcard (F : Finset ℕ) : (lift F).card = F.card := card_image_of_injective _ hinj
  have hlift (F : Finset ℕ) : lift F ∈ family p q q (m + p) ↔ F ∈ family p q 0 m := by
    simp only [mem_family, hcard, lift, mem_image, Nat.add_zero]
    constructor
    · rintro ⟨⟨_, hm, heqm⟩, _, ⟨a, ha, rfl⟩, -, hsub, he⟩
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm q p] at he
      have he' : q * a = p * F.card := Nat.add_right_cancel he
      have hpos := Nat.mul_pos hp (card_pos.mpr ⟨a, ha⟩)
      refine ⟨hinj heqm ▸ hm, a, ha, ?_, ?_, he'⟩
      · exact Nat.pos_of_mul_pos_left (he'.symm ▸ hpos)
      · intro x hx
        have := mem_Icc.mp (hsub (mem_image_of_mem (fun x : ℕ => x + p) hx))
        exact mem_Icc.mpr ⟨by omega, by omega⟩
    · rintro ⟨hm, a, ha, hpos, hsub, he⟩
      refine ⟨⟨m, hm, rfl⟩, a + p, ⟨a, ha, rfl⟩, by omega, ?_, ?_⟩
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
        have := mem_Icc.mp (hsub hx)
        exact mem_Icc.mpr ⟨by omega, by omega⟩
      · rw [Nat.mul_add, Nat.mul_add, he, Nat.mul_comm q p]
  apply card_nbij lift (fun F hF => (hlift F).mpr hF)
  · intro F _ G _ h
    exact Finset.image_injective hinj h
  · intro G hG
    obtain ⟨-, a, ha, -, hsub, he⟩ := mem_family.mp hG
    have hnonneg : q * p < q * a := by
      have hpos := Nat.mul_pos hp (card_pos.mpr ⟨a, ha⟩)
      rw [he, Nat.mul_add, Nat.mul_comm q p]
      omega
    have hpa : p < a := Nat.lt_of_mul_lt_mul_left hnonneg
    let F := G.image (· - p)
    have hFG : lift F = G := by
      ext y
      simp only [lift, F, mem_image, subset_iff, mem_Icc] at *
      grind
    exact ⟨F, (hlift F).mp (hFG ▸ hG), hFG⟩

private theorem recurrence {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (n : ℕ) (hn : p + q + 1 ≤ n) :
    (maximalSchreierCount p q n : ℤ) =
      ∑ i ∈ Icc 1 q, (-1) ^ (i + 1) * (q.choose i : ℤ) * maximalSchreierCount p q (n - i) +
        maximalSchreierCount p q (n - (p + q)) := by
  let f (m : ℕ) : ℤ := maximalSchreierCount p q m
  have iter (t : ℕ) (ht : t ≤ q) (m : ℕ) (hm : p < m) :
      (fwdDiff 1)^[t] f m = (family p q t m).card := by
    induction t generalizing m with
    | zero => simp [f, card_family_zero hq]
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      change (fwdDiff 1)^[t] f (m + 1) - (fwdDiff 1)^[t] f m = _
      rw [ih (by omega) _ (by omega), ih (by omega) _ hm, difference_step (by omega : t < q) hm]
      simp
  -- Reflect the forward-difference sum to index terms by distance from n.
  let term (i : ℕ) := (-1 : ℤ) ^ i * q.choose i * f (n - i)
  have h := fwdDiff_iter_eq_sum_shift 1 f q (n - q)
  rw [← sum_range_reflect] at h
  have hsum : (fwdDiff 1)^[q] f (n - q) = ∑ i ∈ range (q + 1), term i := by
    refine h.trans (sum_congr rfl fun i hi => ?_)
    have hiq : i ≤ q := by simpa using hi
    simp only [Nat.add_sub_cancel, nsmul_eq_mul, mul_one, zsmul_eq_mul, Int.cast_id,
      Nat.cast_id, term]
    rw [Nat.choose_symm hiq, show q - (q - i) = i by omega,
      show n - q + (q - i) = n - i by omega]
  have hshift := translate (q := q) hp (n - (p + q))
  rw [show n - (p + q) + p = n - q by omega, card_family_zero hq] at hshift
  have hsplit : range (q + 1) = insert 0 (Icc 1 q) := by
    ext i
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [iter q le_rfl _ (by omega), ← hshift, hsplit, sum_insert (by simp)] at hsum
  have hzero : term 0 = f n := by simp [term]
  rw [hzero] at hsum
  have hsign : (∑ i ∈ Icc 1 q,
      (-1 : ℤ) ^ (i + 1) * q.choose i * maximalSchreierCount p q (n - i)) =
      -∑ i ∈ Icc 1 q, term i := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    simp [term, f, pow_succ]
  rw [hsign]
  change f n = _
  omega

end MetaMathlibExt.maximalSchreierCount_formula_and_recurrence

namespace MetaMathlibExt

/-- **Closed form and recurrence for maximal $(p, q)$-Schreier sets.** Let $p$ and $q$ be positive
integers, put $p' = p / \gcd(p, q)$ and $q' = q / \gcd(p, q)$, and for each $n$ let
$|M^{p/q}_n|$ be the number of maximal $(p, q)$-Schreier sets with maximum $n$, that is, of sets
$F \subseteq \{1, \dots, n\}$ with $n \in F$ and $q \min F = p |F|$. For each $n$, let $K_n$ be
the set of integers $k$ with $1 \le k \le \lfloor (n+1)/(p'+q') \rfloor$ and $q'k \ge 2$, and let
$\delta_n$ be $1$ if $q' = 1$ and $n = p'$, and $0$ otherwise. Then for every $n \ge 0$,

$$|M^{p/q}_n| = \sum_{k \in K_n} \binom{n - p'k - 1}{q'k - 2} + \delta_n,$$

and for every $n \ge p + q + 1$,

$$|M^{p/q}_n| = \sum_{i=1}^{q} (-1)^{i+1} \binom{q}{i} |M^{p/q}_{n-i}| + |M^{p/q}_{n-(p+q)}|.$$

The paper prints the first formula as a sum over all $1 \le k \le \lfloor (n+1)/(p'+q') \rfloor$,
without $\delta_n$, and only for $1 \le n \le p + q$. Read with binomial coefficients vanishing
at negative lower index, it fails at $p = q = n = 1$, where $|M^{1/1}_1| = 1$ but the sum is $0$;
the term $\delta_n$ counts the singleton $\{n\}$, as in equation (10) of the paper's proof of
Theorem 1.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Corollary 3
(`jis-2026-26.2.2-cor-3`). -/
public theorem maximalSchreierCount_formula_and_recurrence {p q : ℕ} (hp : 1 ≤ p)
    (hq : 1 ≤ q) :
    (∀ n, maximalSchreierCount p q n =
      ∑ k ∈ (Finset.Icc 1 ((n + 1) / (p / p.gcd q + q / p.gcd q))).filter
          (fun k => 2 ≤ q / p.gcd q * k),
        (n - p / p.gcd q * k - 1).choose (q / p.gcd q * k - 2) +
      if q / p.gcd q = 1 ∧ n = p / p.gcd q then 1 else 0) ∧
    ∀ n, p + q + 1 ≤ n →
      (maximalSchreierCount p q n : ℤ) =
        ∑ i ∈ Finset.Icc 1 q,
            (-1) ^ (i + 1) * (q.choose i : ℤ) * maximalSchreierCount p q (n - i) +
          maximalSchreierCount p q (n - (p + q)) := by
  exact ⟨maximalSchreierCount_formula_and_recurrence.formula hp hq,
    maximalSchreierCount_formula_and_recurrence.recurrence hp hq⟩

end MetaMathlibExt
