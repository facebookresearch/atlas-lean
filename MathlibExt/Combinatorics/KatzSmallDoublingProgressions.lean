/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Data.Int.Interval
import Mathlib.NumberTheory.Bertrand
import MathlibExt.Combinatorics.Additive.Szemeredi

/-!
# Arithmetic progressions in sets of small doubling

Katz's small-doubling conjecture follows by counting progressions in a prime cyclic model
and lifting the resulting progression pairs to the integers.
-/

@[expose] public section

open scoped Pointwise
open Finset

namespace MathlibExt.Combinatorics.KatzSmallDoublingProgressionsWanted

/-- **Sumset of a finite set of integers.** For a finite set $A \subseteq \mathbb{Z}$, the sumset
$A + A = \{a + b : a, b \in A\}$, a finite set of integers.

Source: [AIM-COMBINATORICS-0211],
AIM Problem Lists, Recent trends in additive combinatorics, item 1.5,
`aim-combinatorics-notes.json notes[210]`. -/
def katzSumset (A : Finset ℤ) : Finset ℤ :=
  Finset.image (fun p : ℤ × ℤ => p.1 + p.2) (Finset.product A A)

/-- **Arithmetic progressions in a finite set of integers, as pairs.** For a natural number $k$
and a finite set $A \subseteq \mathbb{Z}$, the set of pairs $(a, d)$ of integers such that
$a + i d \in A$ for every natural number $i < k$. The pair $(a, d)$ stands for the $k$-term
arithmetic progression $a, a + d, \dots, a + (k - 1)d$; the difference $d$ may be zero or
negative.

Source: [AIM-COMBINATORICS-0211],
AIM Problem Lists, Recent trends in additive combinatorics, item 1.5,
`aim-combinatorics-notes.json notes[210]`. -/
def katzAPSet (k : ℕ) (A : Finset ℤ) : Set (ℤ × ℤ) :=
  {p : ℤ × ℤ | ∀ i : ℕ, i < k → p.1 + (i : ℤ) * p.2 ∈ A}

/-- **Katz's question on progressions in sets of small doubling.** For a finite set
$A \subseteq \mathbb{Z}$ write $A + A = \{a + b : a, b \in A\}$. This is the statement that for
every natural number $k \ge 3$ and every real number $C \ge 2$ there is a real number $c > 0$ such
that every finite set $A \subseteq \mathbb{Z}$ with $|A + A| < C|A|$ has at least $c|A|^2$ pairs
$(a, d)$ of integers with $a + i d \in A$ for all natural numbers $i < k$.

Each pair $(a, d)$ is a $k$-term arithmetic progression $a, a + d, \dots, a + (k - 1)d$ in $A$;
pairs with $d = 0$ or $d < 0$ are counted too. The question is Problem 1.5 of the AIM problem
list on additive combinatorics, posed by N. Katz.

Source: [AIM-COMBINATORICS-0211], AIM Problem Lists, Recent
trends in additive combinatorics, item 1.5,
`aim-combinatorics-notes.json notes[210]`,
https://aimath.org/WWN/additivecomb/additivecomb.pdf. -/
def conjecture : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ C : ℝ, 2 ≤ C → ∃ c : ℝ, 0 < c ∧ ∀ A : Finset ℤ,
    (Finset.card (katzSumset A) : ℝ) < C * (Finset.card A : ℝ) →
    c * ((Finset.card A : ℝ) ^ 2) ≤ (Set.ncard (katzAPSet k A) : ℝ)

/-- A cyclic model that reflects equality of two-term sums from the integer set. -/
private lemma exists_modelling_map {A : Finset ℤ} (hA : A.Nonempty) :
    ∃ q : ℕ, q.Prime ∧ q ≤ 20 * ((A + A) - (A + A)).card ∧
      ∃ f : ℤ → ZMod q, ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
        f a + f b = f c + f d → a + b = c + d := by
  classical
  let D := (A + A) - (A + A)
  have hD : D.Nonempty := (hA.add hA).sub (hA.add hA)
  obtain ⟨q, hqPrime, hq, hqUpper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (10 * D.card) (by positivity)
  let _ : Fact q.Prime := ⟨hqPrime⟩
  obtain ⟨p, hp, hpPrime⟩ := Nat.exists_infinite_primes (max q (D.sup Int.natAbs) + 1)
  let _ : Fact p.Prime := ⟨hpPrime⟩
  have hpq : q < p := by omega
  have hpD : D.sup Int.natAbs < p := by omega
  -- Sums of two canonical residues differ by at most 2p. Exclude every multiplier
  -- that could make such a difference divisible by q for a nonzero original difference.
  let L := (2 * p) / q
  let J := Icc (- (L : ℤ)) (L : ℤ)
  let bad := ((D.erase 0) ×ˢ J).image fun (z, j) ↦ ((q : ZMod p) * (j : ZMod p)) / (z : ZMod p)
  have hJ : J.card = 2 * L + 1 := by
    dsimp [J]
    rw [Int.card_Icc]
    omega
  have hL : L * q ≤ 2 * p := (Nat.le_div_iff_mul_le hqPrime.pos).mp le_rfl
  have hLD : 10 * (L * D.card) ≤ 2 * p := by
    calc
      _ = L * (10 * D.card) := by ring
      _ ≤ L * q := Nat.mul_le_mul_left _ hq.le
      _ ≤ _ := hL
  have hbad : bad.card < p := by
    calc
      bad.card ≤ (D.erase 0).card * J.card := card_image_le.trans_eq (card_product ..)
      _ ≤ D.card * J.card := Nat.mul_le_mul_right _ (card_erase_le ..)
      _ < p := by rw [hJ, Nat.mul_add, show D.card * (2 * L) = 2 * (L * D.card) by ring]; omega
  have hlt : bad.card < (univ : Finset (ZMod p)).card := by simpa [ZMod.card] using hbad
  obtain ⟨r, hr⟩ : ∃ r, r ∉ bad := by
    by_contra! h
    exact hlt.not_ge (card_le_card fun x _ ↦ h x)
  let v (a : ℤ) := (r * (a : ZMod p)).val
  have hqBound : q ≤ 20 * D.card := by omega
  refine ⟨q, hqPrime, hqBound, (fun a ↦ (v a : ZMod q)), ?_⟩
  intro a ha b hb c hc d hd he
  by_contra hn
  let z := a + b - (c + d)
  have hzD : z ∈ D := sub_mem_sub (add_mem_add ha hb) (add_mem_add hc hd)
  have hz : z ≠ 0 := sub_ne_zero.mpr hn
  have hzp : (z : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h
    have hle : p ≤ z.natAbs := by
      simpa using Nat.le_of_dvd (Int.natAbs_pos.mpr hz) (Int.natAbs_dvd_natAbs.mpr h)
    exact ((Finset.le_sup (f := Int.natAbs) hzD).trans_lt hpD).not_ge hle
  let w := (v a : ℤ) + v b - ((v c : ℤ) + v d)
  have hwq : (w : ZMod q) = 0 := by
    simpa [w, sub_eq_zero] using he
  obtain ⟨j, hj⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).1 hwq
  have hw : w.natAbs ≤ 2 * p := by
    have hva : v a < p := ZMod.val_lt _
    have hvb : v b < p := ZMod.val_lt _
    have hvc : v c < p := ZMod.val_lt _
    have hvd : v d < p := ZMod.val_lt _
    dsimp [w]
    omega
  have hjL : j.natAbs ≤ L := by
    apply (Nat.le_div_iff_mul_le hqPrime.pos).2
    rw [hj, Int.natAbs_mul, Int.natAbs_natCast] at hw
    simpa [Nat.mul_comm] using hw
  have hjJ : j ∈ J := by
    apply mem_Icc.mpr
    omega
  have hwp : (w : ZMod p) = r * (z : ZMod p) := by
    simp [w, z, v]
    ring
  apply hr
  refine mem_image.mpr ⟨(z, j), mem_product.mpr ⟨mem_erase.mpr ⟨hz, hzD⟩, hjJ⟩, ?_⟩
  apply (div_eq_iff hzp).2
  rw [← hwp, hj]
  push_cast
  rfl

private lemma card_double_diff_le {A : Finset ℤ} (hA : A.Nonempty) {K : ℕ}
    (hK : (A + A).card ≤ K * A.card) :
    ((A + A) - (A + A)).card ≤ K ^ 4 * A.card := by
  have hr : ((A + A).card / (A.card : ℚ≥0)) ≤ K := by
    apply (div_le_iff₀ (by exact_mod_cast hA.card_pos)).mpr
    exact_mod_cast hK
  have h := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hA A 2 2
  rw [two_nsmul, show 2 + 2 = 4 by decide] at h
  exact_mod_cast h.trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hr 4) (by positivity))

private noncomputable def cyclicProgressions {q : ℕ} [NeZero q] (k : ℕ)
    (B : Finset (ZMod q)) : Finset (ZMod q × ZMod q) := by
  classical
  exact univ.filter fun w ↦ ∀ i : ℕ, i < k → w.1 + (i : ZMod q) * w.2 ∈ B

private lemma mem_cyclicProgressions {q : ℕ} [NeZero q] {k : ℕ} {B : Finset (ZMod q)}
    {w : ZMod q × ZMod q} :
    w ∈ cyclicProgressions k B ↔ ∀ i : ℕ, i < k → w.1 + (i : ZMod q) * w.2 ∈ B := by
  classical
  simp [cyclicProgressions]

private def window {q : ℕ} (N : ℕ) (B : Finset (ZMod q)) (w : ZMod q × ZMod q) :
    Finset ℕ := (range N).filter fun i : ℕ ↦ w.1 + (i : ZMod q) * w.2 ∈ B

private lemma sum_card_windows {q : ℕ} [NeZero q] (N : ℕ) (B : Finset (ZMod q)) :
    ∑ w : ZMod q × ZMod q, (window N B w).card = N * (q * B.card) := by
  classical
  simp_rw [window, card_filter]
  rw [sum_comm]
  have hcount (i : ℕ) :
      (∑ w : ZMod q × ZMod q, if w.1 + (i : ZMod q) * w.2 ∈ B then 1 else 0) =
        q * B.card := by
    rw [← card_filter]
    refine (card_bijective (fun w : ZMod q × ZMod q ↦ (w.2, w.1 + (i : ZMod q) * w.2))
      (show Function.Bijective _ from ?_)
      (t := univ ×ˢ B) (by simp)).trans ?_
    · exact (show Function.LeftInverse
        (fun v : ZMod q × ZMod q ↦ (v.2 - (i : ZMod q) * v.1, v.1))
        (fun w : ZMod q × ZMod q ↦ (w.2, w.1 + (i : ZMod q) * w.2)) from
          fun w ↦ by simp).injective.bijective_of_finite
    · simp [ZMod.card]
  simp_rw [hcount]
  simp

/-- Averaging the densities of affine windows gives a quadratic progression count. -/
private lemma many_cyclicProgressions {q N k : ℕ} [Fact q.Prime] {δ : ℝ}
    (hN : 0 < N) (hNq : N ≤ q) (hk : 2 ≤ k) (hδ : 0 < δ)
    (hSz : ∀ T : Finset ℕ, T ⊆ range N → (δ / 2) * (N : ℝ) ≤ T.card →
      ∃ a e : ℕ, 0 < e ∧ ∀ i : ℕ, i < k → a + i * e ∈ T)
    (B : Finset (ZMod q)) (hB : δ * (q : ℝ) ≤ B.card) :
    (δ / (2 * (N : ℝ) ^ 2)) * (q : ℝ) ^ 2 ≤ (cyclicProgressions k B).card := by
  classical
  -- Each window below the threshold contributes at most half the average density bound.
  let G : Finset (ZMod q × ZMod q) :=
    univ.filter fun w ↦ (δ / 2) * (N : ℝ) ≤ (window N B w).card
  have hsum :
      ∑ w : ZMod q × ZMod q, ((window N B w).card : ℝ) = (N : ℝ) * (q * B.card) := by
    exact_mod_cast sum_card_windows N B
  have htotal :
      ∑ w : ZMod q × ZMod q, ((window N B w).card : ℝ) ≤
        (δ / 2 * (N : ℝ)) * (q : ℝ)^2 + (G.card : ℝ) * N := by
    calc
      _ ≤ ∑ w : ZMod q × ZMod q, (δ / 2 * (N : ℝ) +
          if (δ / 2) * (N : ℝ) ≤ (window N B w).card then (N : ℝ) else 0) := by
        apply sum_le_sum
        intro w _
        split_ifs with h
        · have hwindow : (window N B w).card ≤ N := by
            simpa [window] using card_filter_le (range N)
              (fun i : ℕ ↦ w.1 + (i : ZMod q) * w.2 ∈ B)
          have hwindowReal : ((window N B w).card : ℝ) ≤ N := by exact_mod_cast hwindow
          exact hwindowReal.trans (le_add_of_nonneg_left (by positivity))
        · simpa only [add_zero] using (lt_of_not_ge h).le
      _ = _ := by
        rw [sum_add_distrib, ← sum_filter]
        simp [G, ZMod.card, pow_two, mul_comm]
  have hG : δ / 2 * (q : ℝ)^2 ≤ G.card := by
    have h := mul_le_mul_of_nonneg_left hB
      (show 0 ≤ (N : ℝ) * q by positivity)
    rw [hsum] at htotal
    apply le_of_mul_le_mul_left _ (show 0 < (N : ℝ) by exact_mod_cast hN)
    linarith only [h, htotal]
  have hex (w : G) :
      ∃ a e : ℕ, a < N ∧ e < N ∧ 0 < e ∧
        ∀ i : ℕ, i < k → w.val.1 + ((a + i * e : ℕ) : ZMod q) * w.val.2 ∈ B := by
    have hg := (mem_filter.mp w.property).2
    obtain ⟨a, e, he, hw⟩ := hSz _ (filter_subset _ _) hg
    have hlt : a + e < N := by
      simpa [window] using (mem_filter.mp (hw 1 (by omega))).1
    exact ⟨a, e, by omega, by omega, he, fun i hi ↦ (mem_filter.mp (hw i hi)).2⟩
  choose a e ha he hePos hw using hex
  -- The chosen progression and the two indices specifying it recover the affine window.
  let T := cyclicProgressions k B ×ˢ (range N ×ˢ range N)
  let F (w : G) : T :=
    ⟨((w.val.1 + (a w : ZMod q) * w.val.2, (e w : ZMod q) * w.val.2), a w, e w),
      mem_product.mpr ⟨mem_cyclicProgressions.mpr (fun i hi ↦ by
        convert hw w i hi using 1
        push_cast
        ring), mem_product.mpr ⟨mem_range.mpr (ha w), mem_range.mpr (he w)⟩⟩⟩
  have hF : Function.Injective F := by
    intro w v h
    have hpair := congrArg Subtype.val h
    dsimp only [F] at hpair
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨⟨hx, hs⟩, hae, hee⟩ := hpair
    rw [← hee] at hs
    have hne : (e w : ZMod q) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      exact fun h ↦ (lt_of_lt_of_le (he w) hNq).not_ge (Nat.le_of_dvd (hePos w) h)
    have hs' := mul_left_cancel₀ hne hs
    rw [hae, hs'] at hx
    exact Subtype.ext (Prod.ext (add_right_cancel hx) hs')
  have hcard : (G.card : ℝ) ≤ (cyclicProgressions k B).card * ((N : ℝ) ^ 2) := by
    have h := Fintype.card_le_of_injective F hF
    simpa [T, Fintype.card_coe, pow_two, ← Nat.cast_le (α := ℝ)] using h
  have hNreal : 0 < (N : ℝ) ^ 2 := by positivity
  calc
    _ = (δ / 2 * (q : ℝ) ^ 2) / (N : ℝ) ^ 2 := by ring
    _ ≤ _ := (div_le_iff₀ hNreal).mpr (hG.trans hcard)

private lemma katzAPSet_finite {k : ℕ} (hk : 2 ≤ k) (A : Finset ℤ) :
    (katzAPSet k A).Finite := by
  let f (w : ℤ × ℤ) := (w.1, w.1 + w.2)
  refine Set.Finite.of_injOn (f := f) (t := (A : Set ℤ) ×ˢ (A : Set ℤ)) ?_ ?_
    (A.finite_toSet.prod A.finite_toSet)
  · intro w hw
    exact ⟨by simpa [f] using hw 0 (by omega), by simpa [f] using hw 1 (by omega)⟩
  · intro w _ v _ h
    have h₀ := congrArg Prod.fst h
    have h₁ := congrArg Prod.snd h
    change w.1 = v.1 at h₀
    change w.1 + w.2 = v.1 + v.2 at h₁
    rw [h₀] at h₁
    exact Prod.ext h₀ (add_left_cancel h₁)

private lemma card_le_katzAPSet {k : ℕ} (hk : 2 ≤ k) (A : Finset ℤ) :
    A.card ≤ (katzAPSet k A).ncard := by
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard_of_injOn (fun a : ℤ ↦ (a, (0 : ℤ)))
    (fun a ha i hi ↦ by simpa using ha)
    (fun a _ b _ h ↦ congrArg Prod.fst h) (katzAPSet_finite hk A)

private lemma model_injOn {q : ℕ} {f : ℤ → ZMod q} {A : Finset ℤ} (hA : A.Nonempty)
    (hf : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, f a + f b = f c + f d → a + b = c + d) :
    Set.InjOn f (A : Set ℤ) := by
  obtain ⟨x, hx⟩ := hA
  intro a ha b hb h
  exact add_right_cancel (hf a ha x hx b hb x hx (by rw [h]))

private lemma lift_progressions {q k : ℕ} [NeZero q] (hk : 2 ≤ k)
    {A : Finset ℤ} {f : ℤ → ZMod q}
    (hf : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, f a + f b = f c + f d → a + b = c + d) :
    (cyclicProgressions k (A.image f)).card ≤ (katzAPSet k A).ncard := by
  classical
  let g := Function.invFunOn f (A : Set ℤ)
  have hg {x : ZMod q} (hx : x ∈ A.image f) : g x ∈ A ∧ f (g x) = x :=
    Function.invFunOn_pos (mem_image.mp hx)
  let lift (w : ZMod q × ZMod q) := (g w.1, g (w.1 + w.2) - g w.1)
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn lift ?_ ?_ (katzAPSet_finite hk A)
  · intro w hw i hi
    have hm := mem_cyclicProgressions.mp hw
    let x (j : ℕ) := g (w.1 + (j : ZMod q) * w.2)
    have hmem (j : ℕ) (hj : j < k) : x j ∈ A := (hg (hm j hj)).1
    -- Consecutive triples retain their midpoint identity under the lift.
    have heq (j : ℕ) (hj : j + 2 < k) : x j + x (j + 2) = x (j + 1) + x (j + 1) := by
      apply hf _ (hmem j (by omega)) _ (hmem (j + 2) hj)
        _ (hmem (j + 1) (by omega)) _ (hmem (j + 1) (by omega))
      dsimp [x]
      rw [(hg (hm j (by omega))).2, (hg (hm (j + 2) hj)).2, (hg (hm (j + 1) (by omega))).2]
      push_cast
      ring
    have hline (j : ℕ) : j < k → x j = x 0 + (j : ℤ) * (x 1 - x 0) := by
      induction j using Nat.twoStepInduction with
      | zero => simp
      | one => intro; ring
      | more j ih₀ ih₁ =>
        intro hj
        have h := heq j hj
        rw [ih₀ (by omega), ih₁ (by omega)] at h
        push_cast at h ⊢
        linarith only [h]
    have hx := hmem i hi
    rw [hline i hi] at hx
    simpa [lift, x] using hx
  · intro w hw v hv h
    have hw' := mem_cyclicProgressions.mp hw
    have hv' := mem_cyclicProgressions.mp hv
    have hstart : g w.1 = g v.1 := congrArg Prod.fst h
    have hnext : g (w.1 + w.2) = g (v.1 + v.2) := by
      simpa [lift] using congrArg (fun p : ℤ × ℤ ↦ p.1 + p.2) h
    have hs : w.1 = v.1 := by
      simpa [(hg (by simpa using hw' 0 (by omega))).2,
        (hg (by simpa using hv' 0 (by omega))).2] using congrArg f hstart
    have hn : w.1 + w.2 = v.1 + v.2 := by
      simpa [(hg (by simpa using hw' 1 (by omega))).2,
        (hg (by simpa using hv' 1 (by omega))).2] using congrArg f hnext
    rw [hs] at hn
    exact Prod.ext hs (add_left_cancel hn)

private lemma card_katzSumset (A : Finset ℤ) : (katzSumset A).card = (A + A).card := rfl

/--
**Sets of small doubling contain many arithmetic progressions.** For a finite set
$A \subseteq \mathbb{Z}$ write $A + A = \{a + b : a, b \in A\}$. For every natural number $k \ge 3$
and every real number $C \ge 2$ there is a real number $c > 0$ such that every finite set
$A \subseteq \mathbb{Z}$ with $|A + A| < C|A|$ has at least $c|A|^2$ pairs $(a, d)$ of integers
with $a + i d \in A$ for all natural numbers $i < k$.

This answers Katz's Problem 1.5 affirmatively. On the AIM additive-combinatorics list B. Green
observes that a large subset of $A$ is Freiman-isomorphic to a dense subset of
$\mathbb{Z}/p\mathbb{Z}$ (Ruzsa's lemma), and Szemerédi's theorem with Varnavides averaging gives
$\gg_{k,C} |A|^2$ $k$-term progressions. The pairs with $d = 0$ counted here cover small sets.

Source: AIM
workshop problem list, Additive combinatorics (additivecomb.pdf), Problem 1.5 (N. Katz) and
remark by B. Green, https://aimath.org/WWN/additivecomb/additivecomb.pdf. Moved from
`OpenConjectures/Combinatorics/KatzSmallDoublingProgressions`.
-/
public theorem conjecture_holds : conjecture := by
  classical
  intro k hk C hC
  have hk₂ : 2 ≤ k := by omega
  obtain ⟨K, hK⟩ := exists_nat_ge C
  have hKpos : 0 < (K : ℝ) := by linarith
  let δ : ℝ := 1 / (20 * (K : ℝ) ^ 4)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N₀, hSz⟩ :=
    Additive.SzemerediWanted.szemeredi k (by omega) (δ / 2) (by positivity)
  let N := N₀ + 1
  have hN : 0 < N := Nat.succ_pos _
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  let c := min (1 / (N : ℝ)) (δ / (2 * (N : ℝ) ^ 2))
  refine ⟨c, lt_min (by positivity) (by positivity), ?_⟩
  intro A hA
  have hAne : A.Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro rfl
    simp [katzSumset] at hA
  rw [card_katzSumset] at hA
  have hKA : (A + A).card ≤ K * A.card := by
    exact_mod_cast hA.le.trans (mul_le_mul_of_nonneg_right hK (by positivity))
  obtain ⟨q, hqPrime, hqUpper, f, hf⟩ := exists_modelling_map hAne
  let _ : Fact q.Prime := ⟨hqPrime⟩
  let B := A.image f
  have hBcard : B.card = A.card := card_image_of_injOn (model_injOn hAne hf)
  have hAq : A.card ≤ q := by
    rw [← hBcard]
    simpa [ZMod.card] using card_le_univ (s := B)
  by_cases hNq : N ≤ q
  · have hqSize : q ≤ (20 * K ^ 4) * A.card := by
      calc
        _ ≤ 20 * ((A + A) - (A + A)).card := hqUpper
        _ ≤ 20 * (K ^ 4 * A.card) := Nat.mul_le_mul_left _ (card_double_diff_le hAne hKA)
        _ = _ := by ring
    have hqSizeReal : (q : ℝ) ≤ (20 * (K : ℝ) ^ 4) * A.card := by exact_mod_cast hqSize
    have hB : δ * (q : ℝ) ≤ (B.card : ℝ) := by
      dsimp only [δ]
      rw [hBcard, div_mul_eq_mul_div, one_mul]
      exact (div_le_iff₀ (by positivity)).2 (by simpa [mul_comm] using hqSizeReal)
    calc
      c * (A.card : ℝ) ^ 2 ≤ (δ / (2 * (N : ℝ) ^ 2)) * (q : ℝ) ^ 2 := by
        gcongr
        exact min_le_right _ _
      _ ≤ ((cyclicProgressions k B).card : ℝ) :=
        many_cyclicProgressions hN hNq hk₂ hδ (hSz N (Nat.le_succ N₀)) B hB
      _ ≤ _ := by exact_mod_cast lift_progressions hk₂ hf
  · have hSmall : (A.card : ℝ) ≤ N := by
      exact_mod_cast hAq.trans (le_of_lt (lt_of_not_ge hNq))
    have hCoef : (1 / (N : ℝ)) * (A.card : ℝ) ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul]
      exact (div_le_one hNreal).2 hSmall
    calc
      c * (A.card : ℝ) ^ 2 ≤ (1 / (N : ℝ)) * (A.card : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ = ((1 / (N : ℝ)) * (A.card : ℝ)) * A.card := by ring
      _ ≤ (A.card : ℝ) := by
        simpa using mul_le_mul_of_nonneg_right hCoef (show 0 ≤ (A.card : ℝ) by positivity)
      _ ≤ _ := by exact_mod_cast card_le_katzAPSet hk₂ A

end MathlibExt.Combinatorics.KatzSmallDoublingProgressionsWanted
