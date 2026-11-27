/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Decision.ValueOfInformation
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
# Tests for the expected value of information

The examples cover signed weights, a two-state medical test with positive information value,
and a singleton action set with zero information value.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Decision.ValueOfInformation

open MathlibExt.Probability.Decision.ValueOfInformation

/-- The nonnegativity bound holds even when one evidence outcome has negative weight. -/
example (U : Bool → Unit → ℝ) :
    0 ≤ evii (Finset.univ : Finset Bool) Finset.univ_nonempty
      (fun (_ : Unit) (e : Bool) => if e then (1 : ℝ) else -1) U := evii_nonneg

/-- Medical-test example with strictly positive value of imperfect
information. States `Ω = Fin 2` (`0` healthy, `1` disease), actions
`Fin 2` (`0` wait, `1` treat), evidence `ε = Fin 2` (`0` negative test,
`1` positive test). Joint weights (out of 100 patients): healthy/negative
81, healthy/positive 9, disease/negative 1, disease/positive 9. Utilities:
treating the healthy costs 1, treating disease gains 5, waiting gains 0
except untreated disease loses 10. The value of the test is `66`, in the
unnormalized units of the weights, in particular strictly positive. -/
theorem medical_test_evii :
    evii (Finset.univ : Finset (Fin 2)) (Finset.univ_nonempty)
        (![![81, 9], ![1, 9]] : Fin 2 → Fin 2 → ℝ)
        (![![0, -10], ![-1, 5]] : Fin 2 → Fin 2 → ℝ) = 66 := by
  have h_sum : ∀ (f : Fin 2 → ℝ), (∑ x : Fin 2, f x) = f 0 + f 1 := by
    intro f
    have h : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
    rw [h]
    rw [Finset.sum_insert (by decide : (0 : Fin 2) ∉ ({1} : Finset (Fin 2)))]
    rw [Finset.sum_singleton]
  have h_sup : ∀ (f : Fin 2 → ℝ) (hne : (Finset.univ : Finset (Fin 2)).Nonempty),
      (Finset.univ : Finset (Fin 2)).sup' hne f = max (f 0) (f 1) := by
    intro f hne
    apply le_antisymm
    · apply Finset.sup'_le
      intro a _
      have h_cases : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
      cases h_cases a with
      | inl h0 =>
        rw [h0]
        exact le_max_left _ _
      | inr h1 =>
        rw [h1]
        exact le_max_right _ _
    · apply max_le
      · exact Finset.le_sup' f (Finset.mem_univ 0)
      · exact Finset.le_sup' f (Finset.mem_univ 1)
  simp only [evii, informedValue, commitValue, h_sum, h_sup]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- Seeing evidence cannot change the decision when only one action is feasible. -/
example (w : Bool → Bool → ℝ) (hw : ∀ i j, 0 ≤ w i j) (U : Unit → Bool → ℝ) :
    evii ({()} : Finset Unit) (by simp) w U = 0 := by
  apply (evii_eq_zero_iff hw).2
  refine ⟨(), by simp, ?_⟩
  intro e _ a _
  cases a
  exact le_rfl

end MathlibExtTest.Probability.Decision.ValueOfInformation
