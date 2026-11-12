/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.ExpectedUtility.VonNeumannMorgenstern
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Expected utility: uniqueness up to positive affine transformations

Two Bernoulli utilities that are expected-utility representations of the same preference over
lotteries on a finite outcome type differ by a positive affine transformation. No axioms on the
preference and no nondegeneracy are assumed: if one representation is constant, so is the other.
Ordinal transformations of deterministic utility are a different matter: an increasing nonlinear
transformation of a Bernoulli utility generally changes the ranking of lotteries.

## Main results

* `IsExpectedUtilityRepresentation.exists_pos_affine`: `v = a u + b` with `a > 0`.

## References

* D. Gonçalves, *ECON0106 Microeconomics, 5. Expected Utility*, UCL lecture notes (2025):
  Definition 1 and Theorem 1(ii).
-/

namespace MathlibExt.Economics.ExpectedUtility

open Convexity

/-- Uniqueness of expected-utility representations (Gonçalves, Theorem 1(ii)): two Bernoulli
utilities representing the same preference over lotteries differ by a positive affine
transformation. No nondegeneracy is assumed: if `u` is constant, so is `v`. -/
theorem IsExpectedUtilityRepresentation.exists_pos_affine {X : Type*} [Fintype X]
    {R : StdSimplex ℝ X → StdSimplex ℝ X → Prop} {u v : X → ℝ}
    (hu : IsExpectedUtilityRepresentation R u) (hv : IsExpectedUtilityRepresentation R v) :
    ∃ a b : ℝ, 0 < a ∧ ∀ x, v x = a * u x + b := by
  have key : ∀ p q : StdSimplex ℝ X,
      (expectedUtility u q ≤ expectedUtility u p ↔
        expectedUtility v q ≤ expectedUtility v p) :=
    fun p q => (hu p q).symm.trans (hv p q)
  have keyEq : ∀ p q : StdSimplex ℝ X,
      (expectedUtility u p = expectedUtility u q ↔
        expectedUtility v p = expectedUtility v q) := by
    intro p q
    constructor
    · intro h
      apply le_antisymm
      · exact (key q p).mp (le_of_eq h)
      · exact (key p q).mp (le_of_eq h.symm)
    · intro h
      apply le_antisymm
      · exact (key q p).mpr (le_of_eq h)
      · exact (key p q).mpr (le_of_eq h.symm)
  rcases isEmpty_or_nonempty X with hEmpty | hNonempty
  · exact ⟨1, 0, one_pos, fun x => IsEmpty.elim hEmpty x⟩
  · have ord : ∀ x y : X, (u x ≤ u y ↔ v x ≤ v y) := by
      intro x y
      have h := key (StdSimplex.single y) (StdSimplex.single x)
      simp only [expectedUtility_single] at h
      exact h
    have eqv : ∀ x y : X, (u x = u y ↔ v x = v y) := by
      intro x y
      constructor
      · intro h
        apply le_antisymm
        · exact (ord x y).mp (le_of_eq h)
        · exact (ord y x).mp (le_of_eq h.symm)
      · intro h
        apply le_antisymm
        · exact (ord x y).mpr (le_of_eq h)
        · exact (ord y x).mpr (le_of_eq h.symm)
    by_cases hConst : ∀ x y, u x = u y
    · obtain ⟨x0⟩ := hNonempty
      have hv_const : ∀ x y, v x = v y := fun x y => (eqv x y).mp (hConst x y)
      refine ⟨1, v x0 - u x0, one_pos, ?_⟩
      intro x
      have hu_eq : u x = u x0 := hConst x x0
      have hv_eq : v x = v x0 := hv_const x x0
      rw [hv_eq, hu_eq]
      ring
    · have huniv : Finset.univ.Nonempty :=
        Finset.univ_nonempty_iff.mpr hNonempty
      obtain ⟨xb, _, hxb⟩ := Finset.exists_max_image Finset.univ u huniv
      obtain ⟨xw, _, hxw⟩ := Finset.exists_min_image Finset.univ u huniv
      have hlt : u xw < u xb := by
        by_contra hcon
        have hle : u xb ≤ u xw := le_of_not_gt hcon
        have heq : u xb = u xw :=
          le_antisymm hle (hxb xw (Finset.mem_univ xw))
        have hall : ∀ x y, u x = u y := by
          intro x y
          have hx : u x = u xw := le_antisymm
            (by rw [← heq]; exact hxb x (Finset.mem_univ x))
            (hxw x (Finset.mem_univ x))
          have hy : u y = u xw := le_antisymm
            (by rw [← heq]; exact hxb y (Finset.mem_univ y))
            (hxw y (Finset.mem_univ y))
          exact hx.trans hy.symm
        exact hConst hall
      have huv : v xw < v xb := by
        have h1 : v xw ≤ v xb :=
          (ord xw xb).mp (hxw xb (Finset.mem_univ xb))
        have h2 : ¬ v xb ≤ v xw := by
          intro hcontra
          have hu_contra : u xb ≤ u xw := (ord xb xw).mpr hcontra
          exact not_le_of_gt hlt hu_contra
        have hne : v xw ≠ v xb := fun heq => h2 (le_of_eq heq.symm)
        exact lt_of_le_of_ne h1 hne
      have hDu_pos : 0 < u xb - u xw := sub_pos.mpr hlt
      have hDv_pos : 0 < v xb - v xw := sub_pos.mpr huv
      have hDu_ne : u xb - u xw ≠ 0 := ne_of_gt hDu_pos
      set a : ℝ := (v xb - v xw) / (u xb - u xw) with ha_def
      set b : ℝ := v xw - a * u xw with hb_def
      have ha_pos : 0 < a := by rw [ha_def]; exact div_pos hDv_pos hDu_pos
      refine ⟨a, b, ha_pos, ?_⟩
      intro x
      have hx_lo : u xw ≤ u x := hxw x (Finset.mem_univ x)
      have hx_hi : u x ≤ u xb := hxb x (Finset.mem_univ x)
      set t : ℝ := (u x - u xw) / (u xb - u xw) with ht_def
      have ht0 : 0 ≤ t := by
        rw [ht_def]
        exact div_nonneg (sub_nonneg.mpr hx_lo) (le_of_lt hDu_pos)
      have ht1 : t ≤ 1 := by
        rw [ht_def, div_le_one hDu_pos]
        exact sub_le_sub_right hx_hi _
      have hEu_mix : expectedUtility u
          (mix t ht0 ht1 (StdSimplex.single xb) (StdSimplex.single xw)) = u x := by
        rw [expectedUtility_mix, expectedUtility_single, expectedUtility_single]
        have htD : t * (u xb - u xw) = u x - u xw := by
          rw [ht_def]
          exact div_mul_cancel₀ _ hDu_ne
        have hring : t * u xb + (1 - t) * u xw = t * (u xb - u xw) + u xw := by
          ring
        rw [hring, htD, sub_add_cancel]
      have hEq : expectedUtility u
          (mix t ht0 ht1 (StdSimplex.single xb) (StdSimplex.single xw))
          = expectedUtility u (StdSimplex.single x) := by
        rw [hEu_mix, expectedUtility_single]
      have hEqV := (keyEq _ _).mp hEq
      rw [expectedUtility_single] at hEqV
      have hEv_expand : expectedUtility v
          (mix t ht0 ht1 (StdSimplex.single xb) (StdSimplex.single xw))
          = t * v xb + (1 - t) * v xw := by
        rw [expectedUtility_mix, expectedUtility_single, expectedUtility_single]
      have hv_eq : v x = t * v xb + (1 - t) * v xw := by
        rw [← hEqV, hEv_expand]
      have hringV : t * v xb + (1 - t) * v xw = t * (v xb - v xw) + v xw := by
        ring
      have ht_eq : t * (v xb - v xw) = a * (u x - u xw) := by
        rw [ht_def, ha_def]
        ring
      rw [hv_eq, hringV, ht_eq, hb_def]
      ring

end MathlibExt.Economics.ExpectedUtility
