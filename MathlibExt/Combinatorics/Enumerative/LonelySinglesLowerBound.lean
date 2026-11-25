/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.Enumerative.LonelyMarriageableSingles
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import MathlibExt.Probability.BranchingProcess.TotalProgeny

/-!
# A lower bound for the lonely singles count

The theorem `lonelySinglesCount_ge_sum` counts two disjoint families of lonely partitions:
those with no singleton and those with one. Record the size of each block at its least
element, put zero at the other points and append a final zero. The cycle lemma rotates
any word of length `n + 1` and sum `n` into such a record. Choosing positions and
distributing block sizes by stars and bars gives the two binomial sums.
-/

namespace MetaMathlibExt

namespace lonelySinglesCount_ge_sum

open Finset
open MathlibExt.Probability.GaltonWatson

variable {n : ℕ}

-- The size of a block is stored only at its first point.
private def entry {s : Finset (Fin n)} (P : Finpartition s) (i : Fin n) : ℕ :=
  if ∀ j ∈ P.part i, i ≤ j then (P.part i).card else 0

private def uncrossed {s : Finset (Fin n)} (P : Finpartition s) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s, a < b → b < c → c < d →
    P.part a = P.part c → P.part b = P.part d → P.part a = P.part b

-- Taking a prescribed initial segment of a finite ordered set.
private lemma initial_segment (s : Finset (Fin n)) {k : ℕ} (hk : k ≤ s.card) :
    ∃ b ⊆ s, b.card = k ∧ ∀ u ∈ s, ∀ v ∈ b, u ≤ v → u ∈ b := by
  let e := s.orderIsoOfFin rfl
  let f := s.orderEmbOfCardLe hk
  refine ⟨univ.map f.toEmbedding, ?_, by simp, ?_⟩
  · intro i hi
    obtain ⟨j, -, rfl⟩ := mem_map.mp hi
    exact s.orderEmbOfFin_mem rfl _
  · intro u hu v hv huv
    obtain ⟨j, -, rfl⟩ := mem_map.mp hv
    let i := e.symm ⟨u, hu⟩
    have hi : i ≤ Fin.castLE hk j := by
      apply e.le_iff_le.mp
      change e (e.symm ⟨u, hu⟩) ≤ _
      rw [e.apply_symm_apply]
      exact huv
    have hil : i.val < k := lt_of_le_of_lt hi j.isLt
    refine mem_map.mpr ⟨⟨i.val, hil⟩, mem_univ _, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨u, hu⟩)

-- Remove the block starting at the rightmost nonzero entry. It is an interval in the
-- remaining ordered set, and removing it preserves all suffix capacity inequalities.
private lemma realize (s : Finset (Fin n)) (x : Fin n → ℕ)
    (hs : ∑ i ∈ s, x i = s.card)
    (hcap : ∀ t, ∑ i ∈ s.filter (t ≤ ·), x i ≤ (s.filter (t ≤ ·)).card) :
    ∃ P : Finpartition s, uncrossed P ∧ ∀ i ∈ s, entry P i = x i := by
  classical
  by_cases hem : (s.filter (fun i => 0 < x i)).Nonempty
  · let a := (s.filter (fun i => 0 < x i)).max' hem
    have ha := mem_filter.mp (max'_mem _ hem)
    change a ∈ s ∧ 0 < x a at ha
    have hz (i) (hi : i ∈ s) (hai : a < i) : x i = 0 := by
      by_contra! hp
      exact hai.not_ge (le_max' _ _ (mem_filter.mpr ⟨hi, Nat.pos_of_ne_zero hp⟩))
    let tail := s.filter (a ≤ ·)
    have hsize : x a ≤ tail.card :=
      (single_le_sum (f := x) (fun _ _ => Nat.zero_le _) (mem_filter.mpr ⟨ha.1, le_rfl⟩)).trans
        (hcap a)
    obtain ⟨B, hB, hcard, hinit⟩ := initial_segment tail hsize
    have hmin (i) (hi : i ∈ B) := (mem_filter.mp (hB hi)).2
    have hBs : B ⊆ s := hB.trans (filter_subset _ _)
    have hne : B.Nonempty := card_pos.mp (hcard ▸ ha.2)
    obtain ⟨v, hv⟩ := hne
    have haB := hinit a (mem_filter.mpr ⟨ha.1, le_rfl⟩) v hv (hmin v hv)
    have hsum : ∑ i ∈ B, x i = x a := by
      apply sum_eq_single_of_mem a haB
      intro i hi hia
      exact hz i (hBs hi) (lt_of_le_of_ne (hmin i hi) (Ne.symm hia))
    let r := s \ B
    have hrs : ∑ i ∈ r, x i = r.card := by
      have := sum_sdiff hBs (f := x)
      dsimp [r]
      rw [card_sdiff_of_subset hBs]
      omega
    have hrcap (t) : ∑ i ∈ r.filter (t ≤ ·), x i ≤ (r.filter (t ≤ ·)).card := by
      by_cases ht : t ≤ a
      · have hsub : B ⊆ s.filter (t ≤ ·) :=
          fun i hi => mem_filter.mpr ⟨hBs hi, ht.trans (hmin i hi)⟩
        have heq : r.filter (t ≤ ·) = s.filter (t ≤ ·) \ B := by
          ext i
          simp [r, and_assoc, and_comm]
        rw [heq, card_sdiff_of_subset hsub]
        have := sum_sdiff hsub (f := x)
        have := hcap t
        omega
      · rw [sum_eq_zero]
        · exact Nat.zero_le _
        · intro i hi
          obtain ⟨hir, hti⟩ := mem_filter.mp hi
          exact hz i (mem_sdiff.mp hir).1 (lt_of_not_ge ht |>.trans_le hti)
    obtain ⟨Q, hQ, hentry⟩ := realize r x hrs hrcap
    let P : Finpartition s := Q.extend (b := B) (ne_empty_of_mem haB)
      disjoint_sdiff_self_left (sdiff_union_of_subset hBs)
    have partB (i) (hi : i ∈ B) : P.part i = B :=
      P.part_eq_of_mem (mem_insert_self _ _) hi
    have partR (i) (hi : i ∈ s) (hb : i ∉ B) : P.part i = Q.part i := by
      have hir : i ∈ r := mem_sdiff.mpr ⟨hi, hb⟩
      exact P.part_eq_of_mem (mem_insert_of_mem (Q.part_mem.mpr hir)) (Q.mem_part hir)
    have convex {i j k : Fin n} (hi : i ∈ B) (hj : j ∈ s) (hk : k ∈ B)
        (hij : i < j) (hjk : j < k) : j ∈ B :=
      hinit j (mem_filter.mpr ⟨hj, (hmin i hi).trans hij.le⟩) k hk hjk.le
    refine ⟨P, ?_, ?_⟩
    · intro i hi j hj k hk l hl hij hjk hkl hik hjl
      have same {u v : Fin n} (h : P.part u = P.part v) : u ∈ B ↔ v ∈ B := by
        rw [← P.part_eq_iff_mem (t := B) (mem_insert_self _ _), h,
          P.part_eq_iff_mem (mem_insert_self _ _)]
      by_cases hib : i ∈ B
      · have hjb := convex hib hj ((same hik).mp hib) hij hjk
        rw [partB i hib, partB j hjb]
      · have hkb := mt (same hik).mpr hib
        have hjb : j ∉ B := fun hjb => hkb (convex hjb hk ((same hjl).mp hjb) hjk hkl)
        have hlb := mt (same hjl).mpr hjb
        rw [partR i hi hib, partR k hk hkb] at hik
        rw [partR j hj hjb, partR l hl hlb] at hjl
        rw [partR i hi hib, partR j hj hjb]
        exact hQ i (mem_sdiff.mpr ⟨hi, hib⟩) j (mem_sdiff.mpr ⟨hj, hjb⟩) k
          (mem_sdiff.mpr ⟨hk, hkb⟩) l (mem_sdiff.mpr ⟨hl, hlb⟩) hij hjk hkl hik hjl
    · intro i hi
      by_cases hib : i ∈ B
      · rw [entry, partB i hib]
        by_cases hia : i = a
        · subst i
          split_ifs
          exact hcard
        · have hai := lt_of_le_of_ne (hmin i hib) (Ne.symm hia)
          simp [show ¬ (∀ j ∈ B, i ≤ j) from fun h => hai.not_ge (h a haB), hz i hi hai]
      · simpa only [entry, partR i hi hib] using hentry i (mem_sdiff.mpr ⟨hi, hib⟩)
  · have hz (i) (hi : i ∈ s) : x i = 0 := by
      by_contra! h
      exact hem ⟨i, mem_filter.mpr ⟨hi, Nat.pos_of_ne_zero h⟩⟩
    have he : s = ∅ := card_eq_zero.mp ((sum_eq_zero hz).symm.trans hs).symm
    subst s
    exact ⟨⊥, by simp [uncrossed], by simp⟩
termination_by s.card
decreasing_by
  rw [card_sdiff_of_subset hBs]
  have := card_le_card hBs
  omega

private def code (P : _root_.NoncrossingPartition n) : Fin (n + 1) → ℕ :=
  Fin.lastCases 0 (entry P.val)

private lemma realize_passage (x : Fin (n + 1) → ℕ) (hx : ∑ i, x i = n)
    (hp : IsFirstPassage 1 (n + 1) x) : ∃ P, code P = x := by
  have prefix_bound (t : Fin (n + 1)) : t.val ≤ ∑ i with i < t, x i := by
    have := hp t.val (mem_range.mpr t.isLt)
    change t.val < 1 + ∑ i with i < t, x i at this
    omega
  have splitSum (t : Fin (n + 1)) :
      (∑ i with i < t, x i) + (∑ i with t ≤ i, x i) = n := by
    simpa only [not_lt] using (sum_filter_add_sum_filter_not univ (· < t) x).trans hx
  have last : x (Fin.last n) = 0 := by
    have := prefix_bound (Fin.last n)
    have := splitSum (Fin.last n)
    have hle := single_le_sum (f := x) (fun _ _ => Nat.zero_le _)
      (mem_filter.mpr ⟨mem_univ (Fin.last n), le_rfl⟩ : Fin.last n ∈ univ.filter (Fin.last n ≤ ·))
    simp only [Fin.val_last] at *
    omega
  let y (i : Fin n) := x i.castSucc
  have hy : ∑ i, y i = n := by simpa [Fin.sum_univ_castSucc, last, y] using hx
  have cap (t : Fin n) : ∑ i ∈ univ.filter (t ≤ ·), y i ≤ (univ.filter (t ≤ ·)).card := by
    have hpre := prefix_bound t.castSucc
    have hsum := splitSum t.castSucc
    have heq : (∑ i with t.castSucc ≤ i, x i) = ∑ i with t ≤ i, y i := by
      simp [sum_filter, Fin.sum_univ_castSucc, y, last]
    rw [heq] at hsum
    have hc : (univ.filter (t ≤ ·)).card = n - t.val := by
      rw [show univ.filter (t ≤ ·) = Ici t by ext i; simp]
      exact Fin.card_Ici t
    rw [hc]
    change t.val ≤ _ at hpre
    omega
  obtain ⟨P, hP, he⟩ := realize univ y (by simpa using hy) cap
  refine ⟨⟨P, ?_⟩, ?_⟩
  · rintro ⟨a, b, c, d, hab, hbc, hcd, hac, hbd, hne⟩
    exact hne (hP a (mem_univ _) b (mem_univ _) c (mem_univ _) d (mem_univ _) hab hbc hcd hac hbd)
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [code] using last.symm
    · simpa [code] using he j (mem_univ _)

private def ones (x : Fin (n + 1) → ℕ) := univ.filter fun i => x i = 1

private def large (x : Fin (n + 1) → ℕ) := univ.filter fun i => 2 ≤ x i

private def profile (x : Fin (n + 1) → ℕ) : ℕ × ℕ :=
  ((ones x).card, (large x).card + (ones x).card)

private lemma profile_perm (x : Fin (n + 1) → ℕ) (e : Equiv.Perm (Fin (n + 1))) :
    profile (x ∘ e) = profile x := by
  have card (p : ℕ → Prop) [DecidablePred p] :
      (univ.filter (fun i => p (x (e i)))).card = (univ.filter (fun i => p (x i))).card := by
    simp only [card_filter]
    exact Equiv.sum_comp e (fun i => if p (x i) then 1 else 0)
  simp only [profile, ones, large, Function.comp_apply, card (· = 1), card (2 ≤ ·)]

private def lonely (n : ℕ) :=
  univ.filter fun P : _root_.NoncrossingPartition n => ¬ IsMarriageableSingles P.val

private def fiber (n : ℕ) (p : ℕ × ℕ) :=
  (lonely n).filter fun P => profile (code P) = p

private lemma mem_lonely {P : _root_.NoncrossingPartition n} (h : (ones (code P)).card ≤ 1) :
    P ∈ lonely n := by
  refine mem_filter.mpr ⟨mem_univ _, ?_⟩
  rintro ⟨i, j, hij, hi, hj, -⟩
  have single (a : Fin n) (ha : P.val.part a = {a}) : a.castSucc ∈ ones (code P) := by
    apply mem_filter.mpr ⟨mem_univ _, ?_⟩
    simp [code, entry, ha]
  have hsub : {i.castSucc, j.castSucc} ⊆ ones (code P) :=
    insert_subset (single i hi) (singleton_subset_iff.mpr (single j hj))
  have := card_le_card hsub
  simp [hij] at this
  omega

-- A word with at most one unit entry is recovered from a lonely partition and a rotation.
private def words (n : ℕ) (p : ℕ × ℕ) :=
  (Nat.antidiagonalTuple (n + 1) n).filter (fun x => profile x = p)

private lemma words_le (p : ℕ × ℕ) (hp : p.1 ≤ 1) :
    (words n p).card ≤ (n + 1) * (fiber n p).card := by
  classical
  suffices (words n p).card ≤ ((univ : Finset (Fin (n + 1))) ×ˢ fiber n p).card by
    simpa using this
  apply card_le_card_of_surjOn (fun (r, P) => code P ∘ (Equiv.addRight r).symm)
  intro x hx
  obtain ⟨hx, hprof⟩ := mem_filter.mp hx
  have hsum := Nat.mem_antidiagonalTuple.mp hx
  have hr := card_filter_isFirstPassage_rotate (k := 1) le_rfl x (by omega)
  obtain ⟨r, hr⟩ := card_pos.mp (hr ▸ Nat.zero_lt_one)
  obtain ⟨hr, hpass⟩ := mem_filter.mp hr
  let i : Fin (n + 1) := ⟨r, mem_range.mp hr⟩
  let e := Equiv.addRight i
  have hrot : rotate x r = x ∘ e := rfl
  rw [hrot] at hpass
  obtain ⟨P, hP⟩ := realize_passage (x ∘ e) ((Equiv.sum_comp e x).trans hsum) hpass
  have hpr : profile (code P) = p := by rw [hP, profile_perm, hprof]
  have hsmall : (ones (code P)).card ≤ 1 := (congrArg Prod.fst hpr).le.trans hp
  refine ⟨(i, P), mem_product.mpr ⟨mem_univ _, mem_filter.mpr ⟨mem_lonely hsmall, hpr⟩⟩, ?_⟩
  change code P ∘ e.symm = x
  rw [hP]
  funext j
  simp

-- Pick the positions of the large blocks and of the singletons. Distribute the
-- remaining units among the large blocks by stars and bars.
private abbrev Packing (n : ℕ) :=
  Σ _ : Finset (Fin (n + 1)), Finset (Fin (n + 1)) × (Fin (n + 1) →₀ ℕ)

private def packings (n k j u : ℕ) : Finset (Packing n) :=
  (univ.powersetCard k).sigma fun S => Sᶜ.powersetCard j ×ˢ S.finsuppAntidiag u

private def pack (d : Packing n) (i : Fin (n + 1)) : ℕ :=
  (if i ∈ d.1 then d.2.2 i + 2 else 0) + if i ∈ d.2.1 then 1 else 0

private lemma packing_spec {k j u : ℕ} {d : Packing n} (hd : d ∈ packings n k j u) :
    (large (pack d) = d.1 ∧ ones (pack d) = d.2.1) ∧
      d.1.card = k ∧ d.2.1.card = j ∧ ∑ i, pack d i = u + 2 * k + j := by
  obtain ⟨hs, ht, hf⟩ := (mem_sigma.mp hd).imp_right mem_product.mp
  obtain ⟨-, hsk⟩ := mem_powersetCard.mp hs
  obtain ⟨hts, htj⟩ := mem_powersetCard.mp ht
  have hdis (i) (hi : i ∈ d.2.1) : i ∉ d.1 := mem_compl.mp (hts hi)
  refine ⟨⟨?_, ?_⟩, hsk, htj, ?_⟩
  · ext i
    rw [large, mem_filter]
    simp only [mem_univ, true_and, pack]
    split_ifs <;> grind
  · ext i
    rw [ones, mem_filter]
    simp only [mem_univ, true_and, pack]
    specialize hdis i
    split_ifs <;> grind
  · simp only [pack, sum_add_distrib, ← sum_filter, filter_mem_eq_inter, univ_inter,
      sum_add_distrib, sum_const, smul_eq_mul, mul_one, hsk, htj, (mem_finsuppAntidiag.mp hf).1]
    omega

private lemma card_packings_le {k j u : ℕ} (h : u + 2 * k + j = n) :
    (packings n k j u).card ≤ (words n (j, k + j)).card := by
  classical
  apply card_le_card_of_injOn pack
  · intro d hd
    obtain ⟨⟨hl, ho⟩, hk, hj, hs⟩ := packing_spec hd
    exact mem_filter.mpr ⟨Nat.mem_antidiagonalTuple.mpr (hs.trans h),
      by simp [profile, hl, ho, hk, hj]⟩
  · rintro ⟨S, T, f⟩ hd ⟨S', T', g⟩ hd' hfg
    obtain ⟨⟨hl, ho⟩, -⟩ := packing_spec hd
    obtain ⟨⟨hl', ho'⟩, -⟩ := packing_spec hd'
    obtain rfl : S = S' := hl.symm.trans ((congrArg large hfg).trans hl')
    obtain rfl : T = T' := ho.symm.trans ((congrArg ones hfg).trans ho')
    have hsup := (mem_finsuppAntidiag.mp (mem_product.mp (mem_sigma.mp hd).2).2).2
    have hsup' := (mem_finsuppAntidiag.mp (mem_product.mp (mem_sigma.mp hd').2).2).2
    congr 2
    ext i
    by_cases hi : i ∈ S
    · simpa [pack, hi] using congrFun hfg i
    · have hf := Finsupp.notMem_support_iff.mp (mt (@hsup i) hi)
      have hg := Finsupp.notMem_support_iff.mp (mt (@hsup' i) hi)
      exact hf.trans hg.symm

private lemma count_bound {k j u : ℕ} (hk : 0 < k) (hj : j ≤ 1) (h : u + 2 * k + j = n) :
    (n + 1).choose k * ((n + 1 - k).choose j * (k + u - 1).choose (k - 1)) ≤
      (n + 1) * (fiber n (j, k + j)).card := by
  have hcard : (packings n k j u).card =
      (n + 1).choose k * ((n + 1 - k).choose j * (k + u - 1).choose (k - 1)) := by
    rw [packings, card_sigma]
    apply (sum_const_nat (m := (n + 1 - k).choose j * (k + u - 1).choose (k - 1)) ?_).trans
    · simp
    · intro S hS
      have hsk := (mem_powersetCard.mp hS).2
      rw [card_product, card_powersetCard, card_compl, Fintype.card_fin,
        card_finsuppAntidiag_nat_eq_choose, hsk,
        Nat.choose_symm_of_eq_add (show k + u - 1 = u + (k - 1) by omega)]
  exact hcard ▸ (card_packings_le h).trans (words_le (j, k + j) hj)

private lemma no_singleton_bound {m : ℕ} (hm : m ∈ Icc 1 (n / 2)) :
    1 / ((n : ℚ) - m + 1) * zeroExtendedChoose n m *
      zeroExtendedChoose ((n : ℤ) - m - 1) ((m : ℤ) - 1) ≤ (fiber n (0, m)).card := by
  obtain ⟨hm₀, hm₁⟩ := mem_Icc.mp hm
  have hc := count_bound (n := n) (k := m) (j := 0) (u := n - 2 * m)
    (by omega) (by decide) (by omega)
  simp only [Nat.choose_zero_right, one_mul, Nat.add_zero,
    show m + (n - 2 * m) - 1 = n - m - 1 by omega] at hc
  have hn : n.choose m * (n - m - 1).choose (m - 1) ≤ (n + 1 - m) * (fiber n (0, m)).card := by
    refine Nat.le_of_mul_le_mul_left ?_ (Nat.succ_pos n)
    calc
      _ = (n + 1 - m) * ((n + 1).choose m * (n - m - 1).choose (m - 1)) := by
        rw [← mul_assoc, mul_comm (n + 1), Nat.choose_mul_succ_eq]
        ac_rfl
      _ ≤ _ := by simpa [mul_left_comm] using Nat.mul_le_mul_left (n + 1 - m) hc
  rw [show (n : ℤ) - m - 1 = ↑(n - m - 1 : ℕ) by omega,
    show (m : ℤ) - 1 = ↑(m - 1 : ℕ) by omega, zeroExtendedChoose_natCast,
    zeroExtendedChoose_natCast]
  have hd : (0 : ℚ) < (n + 1 - m : ℕ) := by exact_mod_cast (show 0 < n + 1 - m by omega)
  have heq : ((n + 1 - m : ℕ) : ℚ) = n - (m : ℚ) + 1 := by
    rw [Nat.cast_sub (by omega : m ≤ n + 1), Nat.cast_add, Nat.cast_one]
    ring
  rw [← heq, div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul, div_le_iff₀ hd]
  rw [mul_comm (n + 1 - m)] at hn
  exact_mod_cast hn

private lemma one_singleton_bound {m : ℕ} (hm : m ∈ Icc 2 ((n + 1) / 2)) :
    (zeroExtendedChoose n ((m : ℤ) - 1) *
        zeroExtendedChoose ((n : ℤ) - m - 1) ((m : ℤ) - 2) : ℚ) ≤ (fiber n (1, m)).card := by
  obtain ⟨hm₀, hm₁⟩ := mem_Icc.mp hm
  have hc := count_bound (n := n) (k := m - 1) (j := 1) (u := n - 2 * (m - 1) - 1)
    (by omega) (by decide) (by omega)
  rw [Nat.choose_one_right, ← mul_assoc, ← Nat.choose_mul_succ_eq, mul_comm _ (n + 1),
    mul_assoc, show m - 1 + (n - 2 * (m - 1) - 1) - 1 = n - m - 1 by omega,
    show m - 1 + 1 = m by omega] at hc
  have h := Nat.le_of_mul_le_mul_left hc (by omega)
  rw [show (n : ℤ) - m - 1 = ↑(n - m - 1 : ℕ) by omega,
    show (m : ℤ) - 1 = ↑(m - 1 : ℕ) by omega,
    show (m : ℤ) - 2 = ↑(m - 2 : ℕ) by omega, zeroExtendedChoose_natCast,
    zeroExtendedChoose_natCast]
  exact_mod_cast h

private lemma add_fibers_le (s t : Finset ℕ) :
    (∑ m ∈ s, (fiber n (0, m)).card) + (∑ m ∈ t, (fiber n (1, m)).card) ≤ lonelySinglesCount n := by
  let A := ({0} : Finset ℕ) ×ˢ s
  let B := ({1} : Finset ℕ) ×ˢ t
  have hd : Disjoint A B := by
    apply disjoint_left.mpr
    simp [A, B]
  have h := sum_card_fiberwise_eq_card_filter (lonely n) (A ∪ B) (fun P => profile (code P))
  calc
    _ = ∑ p ∈ A ∪ B, (fiber n p).card := by
      rw [sum_union hd]
      simp [A, B]
    _ ≤ _ := h.le.trans (card_le_card (filter_subset _ _))

end lonelySinglesCount_ge_sum

open lonelySinglesCount_ge_sum in
set_option linter.unusedVariables false in
/-- **Lower bound for the number of lonely singles partitions.** For every $n \ge 2$, the number
$L_n$ of lonely singles partitions of $\{0, \dots, n-1\}$ satisfies
$$
L_n \ge \sum_{m=1}^{\lfloor n/2 \rfloor} \frac{1}{n-m+1} \binom{n}{m} \binom{n-m-1}{m-1} +
\sum_{m=2}^{\lfloor (n+1)/2 \rfloor} \binom{n}{m-1} \binom{n-m-1}{m-2},
$$
where a binomial coefficient $\binom{a}{b}$ with $a < 0$ or $b < 0$ is taken to be $0$.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Proposition 26
(`jis-2025-25.1.1-prop-26`). -/
public theorem lonelySinglesCount_ge_sum (n : ℕ) (hn : 2 ≤ n) :
    (∑ m ∈ Finset.Icc 1 (n / 2), 1 / ((n : ℚ) - m + 1) * zeroExtendedChoose n m *
        zeroExtendedChoose ((n : ℤ) - m - 1) ((m : ℤ) - 1)) +
      (∑ m ∈ Finset.Icc 2 ((n + 1) / 2),
        (zeroExtendedChoose n ((m : ℤ) - 1) * zeroExtendedChoose ((n : ℤ) - m - 1) ((m : ℤ) - 2) :
          ℚ)) ≤
      lonelySinglesCount n := by
  apply (add_le_add (Finset.sum_le_sum fun m hm => no_singleton_bound hm)
    (Finset.sum_le_sum fun m hm => one_singleton_bound hm)).trans
  exact_mod_cast add_fibers_le (n := n) (Finset.Icc 1 (n / 2)) (Finset.Icc 2 ((n + 1) / 2))

end MetaMathlibExt
