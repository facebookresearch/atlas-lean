/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Kleitman's theorem on signed sums in the plane

`signedSumsInUnitDiscBound_holds` bounds the number of sign vectors whose sum falls in an open
unit disc by the middle binomial coefficient.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.StrongLittlewoodOffordErdosProblem498Wanted

/-- **Strong Littlewood–Offord bound in the plane.** The statement that for every natural
number $n$, all complex numbers $z_1, \dots, z_n$ with $|z_i| \ge 1$ for every $i$, and every
open disc $D$ of radius $1$ in $\mathbb{C}$, at most $\binom{n}{\lfloor n/2 \rfloor}$ of the
$2^n$ sign vectors $(\varepsilon_1, \dots, \varepsilon_n) \in \{1, -1\}^n$ satisfy
$\sum_i \varepsilon_i z_i \in D$ (Erdős Problem 498). -/
def signedSumsInUnitDiscBound : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ), (∀ i, 1 ≤ ‖z i‖) → ∀ c : ℂ,
    {ε : Fin n → Bool | ∑ i, (if ε i then (1 : ℂ) else -1) * z i ∈ Metric.ball c 1}.ncard ≤
      n.choose (n / 2)

open Finset

variable {ι : Type*}

-- Count the subsets whose imbalance lies in the middle k ranks.
private def window (k : ℕ) (d : ℤ) : ℕ := if -(k : ℤ) < d ∧ d ≤ k then 1 else 0

private def middleCount (I : Finset ι) (k : ℕ) : ℕ :=
  ∑ s ∈ I.powerset, window k (I.card - 2 * (s.card : ℤ))

private lemma middleCount_insert [DecidableEq ι] {i : ι} {I : Finset ι} (hi : i ∉ I)
    {k : ℕ} (hk : 0 < k) :
    middleCount (insert i I) k = middleCount I (k + 1) + middleCount I (k - 1) := by
  unfold middleCount
  rw [sum_powerset_insert hi, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro s hs
  have his := notMem_mono (mem_powerset.mp hs) hi
  simp only [card_insert_of_notMem hi, card_insert_of_notMem his, Nat.cast_add, Nat.cast_one,
    window, Nat.cast_sub (show 1 ≤ k by omega)]
  split_ifs <;> omega

private lemma middleCount_one (I : Finset ι) :
    middleCount I 1 = I.card.choose (I.card / 2) := by
  have h (s : Finset ι) :
      window 1 (I.card - 2 * (s.card : ℤ)) = if s.card = I.card / 2 then 1 else 0 := by
    unfold window
    split_ifs <;> omega
  simp only [middleCount, h, ← card_filter, ← powersetCard_eq_filter, card_powersetCard]

-- If p has maximal projection in direction v, p + v is at least ‖v‖ away from every old point.
private lemma exists_far_translate (S : Finset ℂ) (hS : S.Nonempty) (v : ℂ) (hv : 2 ≤ ‖v‖) :
    ∃ p ∈ S, ∀ x ∈ S, 2 ≤ dist (p + v) x := by
  obtain ⟨p, hp, hmax⟩ := S.exists_max_image (inner ℝ v) hS
  refine ⟨p, hp, fun x hx => ?_⟩
  have h := real_inner_le_norm v (p + v - x)
  rw [inner_sub_right, inner_add_right, real_inner_self_eq_norm_sq] at h
  have hprod : ‖v‖ * ‖v‖ ≤ ‖v‖ * ‖p + v - x‖ := by
    rw [← sq]
    linarith [hmax x hx]
  rw [dist_eq_norm]
  exact hv.trans (le_of_mul_le_mul_left hprod (by linarith))

open scoped Classical in
private noncomputable def discCount (I : Finset ι) (v : ι → ℂ) (c x : ℂ) : ℕ :=
  ∑ s ∈ I.powerset, if x + ∑ i ∈ s, v i ∈ Metric.ball c 1 then 1 else 0

private lemma discCount_insert [DecidableEq ι] {i : ι} {I : Finset ι} (hi : i ∉ I)
    (v : ι → ℂ) (c x : ℂ) :
    discCount (insert i I) v c x = discCount I v c x + discCount I v c (x + v i) := by
  classical
  unfold discCount
  rw [sum_powerset_insert hi]
  congr 1
  apply sum_congr rfl
  intro s hs
  rw [sum_insert (notMem_mono (mem_powerset.mp hs) hi), add_assoc]

-- Count all translates of a separated set S simultaneously. The two copies S and S + v
-- can be regrouped by moving one point from S + v to S. The resulting separated sets
-- have sizes k + 1 and k - 1, the same recurrence as for the middle ranks.
private lemma discCount_le_middle (v : ι → ℂ) (hv : ∀ i, 2 ≤ ‖v i‖) (c : ℂ)
    (I : Finset ι) (S : Finset ℂ) (t : ℂ)
    (hsep : (S : Set ℂ).Pairwise fun x y => 2 ≤ dist x y) :
    ∑ x ∈ S, discCount I v c (x + t) ≤ middleCount I S.card := by
  classical
  induction I using Finset.induction_on generalizing S t with
  | empty =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp [middleCount, window]
    have hk : (0 : ℤ) < S.card := by exact_mod_cast hS.card_pos
    simp only [discCount, middleCount, powerset_empty, sum_singleton, sum_empty, add_zero,
      card_empty, Nat.cast_zero, mul_zero, sub_zero, window, neg_lt_zero.mpr hk, hk.le, and_self,
      ite_true, ← card_filter]
    apply card_le_one.mpr
    intro x hx y hy
    obtain ⟨hxS, hx⟩ := mem_filter.mp hx
    obtain ⟨hyS, hy⟩ := mem_filter.mp hy
    by_contra hne
    have hxy := dist_triangle (x + t) c (y + t)
    rw [dist_add_right] at hxy
    linarith [hsep hxS hyS hne, Metric.mem_ball.mp hx, Metric.mem_ball'.mp hy]
  | @insert i I hi ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp
    obtain ⟨p, hp, hfar⟩ := exists_far_translate S hS (v i) (hv i)
    have hnew : p + v i ∉ S := by
      intro h
      have hbad := hfar _ h
      norm_num at hbad
    have hlarge := ih (insert (p + v i) S) t (by
      rw [coe_insert]
      exact hsep.insert fun x hx _ => ⟨hfar x hx, (dist_comm (p + v i) x) ▸ hfar x hx⟩)
    have hsmall := ih (S.erase p) (t + v i) (hsep.mono (erase_subset _ _))
    rw [card_insert_of_notMem hnew, sum_insert hnew, add_right_comm p (v i) t] at hlarge
    rw [card_erase_of_mem hp] at hsmall
    simp only [discCount_insert hi, sum_add_distrib, middleCount_insert hi hS.card_pos]
    have herase := sum_erase_add S (fun x => discCount I v c (x + (t + v i))) hp
    simp only [← add_assoc] at hsmall herase
    omega

/--
**Kleitman's theorem on signed sums in the plane.** For every natural number $n$, all complex
numbers $z_1, \dots, z_n$ with $|z_i| \ge 1$ for every $i$, and every open disc $D$ of radius $1$
in $\mathbb{C}$, at most $\binom{n}{\lfloor n/2 \rfloor}$ of the $2^n$ sign vectors
$(\varepsilon_1, \dots, \varepsilon_n) \in \{1, -1\}^n$ satisfy $\sum_i \varepsilon_i z_i \in D$.

Kleitman proved this bound for complex $z_i$ (later for vectors in any Hilbert space); Erdős had
proved it for real $z_i$.

Source: T. F. Bloom, Erdős Problems, Problem
#498, https://www.erdosproblems.com/498 (status PROVED (LEAN)); resolution: D. J. Kleitman, On a
lemma of Littlewood and Offord on the distribution of certain sums, Math. Z. (1965), 251-259,
erdosproblems.com/498: solved in the affirmative by Kleitman; generalized to Hilbert spaces
(Kleitman 1970), https://www.erdosproblems.com/498.
-/
theorem signedSumsInUnitDiscBound_holds : signedSumsInUnitDiscBound := by
  classical
  intro n z hz c
  let support (ε : Fin n → Bool) := univ.filter fun i => ε i = true
  have hinj : Function.Injective support := by
    intro ε δ h
    funext i
    have hi := Finset.ext_iff.mp h i
    simpa [support] using hi
  have hsum (ε : Fin n → Bool) :
      -(∑ i, z i) + ∑ i ∈ support ε, 2 * z i = ∑ i, (if ε i then (1 : ℂ) else -1) * z i := by
    simp only [support, sum_filter, ← sum_neg_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    cases ε i <;> simp
    ring
  have hd (i : Fin n) : 2 ≤ ‖2 * z i‖ := by
    rw [norm_mul, Complex.norm_two]
    linarith [hz i]
  have h := discCount_le_middle (fun i => 2 * z i) hd c univ {0} (-(∑ i, z i)) (by simp)
  simp only [sum_singleton, zero_add, card_singleton, middleCount_one, card_univ, Fintype.card_fin,
    discCount, ← card_filter] at h
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  refine le_trans (card_le_card_of_injOn support ?_ hinj.injOn) h
  intro ε hε
  exact mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), (hsum ε).symm ▸ (mem_filter.mp hε).2⟩

end MathlibExt.Combinatorics.StrongLittlewoodOffordErdosProblem498Wanted
