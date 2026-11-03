/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.FStatisticsBasis

@[expose] public section

open MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics
  MathlibExt.Biology.PopulationGenetics.FStatisticsBasis

namespace MathlibExtTest.Biology.PopulationGenetics.FStatisticsBasis

/-! ### Dimension counts -/

/-- Three populations: `V_F` has dimension `3`. -/
example : Module.finrank ℝ (fSpace (Fin 3)) = 3 := by
  rw [finrank_fSpace]
  decide

/-- Four populations: `V_F` has dimension `6`. -/
example : Module.finrank ℝ (fSpace (Fin 4)) = 6 := by
  rw [finrank_fSpace]
  decide

/-- Boundary: one population carries no f-statistic (`V_F = 0`). -/
example : Module.finrank ℝ (fSpace (Fin 1)) = 0 := by
  rw [finrank_fSpace]
  decide

/-! ### The two bases on four populations -/

example : LinearIndependent ℝ
    (fun q : {q : Fin 4 × Fin 4 // q.1 < q.2} => f2Form q.1.1 q.1.2) :=
  linearIndependent_f2Form

example : LinearIndependent ℝ
    (fun q : {q : Fin 4 × Fin 4 // q.1 ≤ q.2 ∧ q.1 ≠ 0 ∧ q.2 ≠ 0} => f3Form 0 q.1.1 q.1.2) :=
  linearIndependent_f3Form 0

/-- Every `f4` form lies in the span of the `f3` basis with base population `0`. -/
example : f4Form (0 : Fin 4) 1 2 3 ∈ Submodule.span ℝ
    (Set.range fun q : {q : Fin 4 × Fin 4 // q.1 ≤ q.2 ∧ q.1 ≠ 0 ∧ q.2 ≠ 0} =>
      f3Form 0 q.1.1 q.1.2) := by
  rw [span_f3Form]
  exact f4Form_mem_fSpace 0 1 2 3

/-- The change of basis used in the proof: `f2 1 2 = f3(0; 1, 1) + f3(0; 2, 2) - 2 f3(0; 1, 2)`,
checked at a concrete frequency vector. -/
example : f2Form (1 : Fin 3) 2 ![1/5, 1/2, 9/10] =
    f3Form 0 1 1 ![1/5, 1/2, 9/10] + f3Form 0 2 2 ![1/5, 1/2, 9/10] -
      2 * f3Form 0 1 2 ![1/5, 1/2, 9/10] := by
  simp [f2Form, f3Form, f4Form]
  norm_num

/-! ### Integration of linear combinations -/

/-- On a Dirac measure, `f4 = (f2 A D + f2 B C - f2 A C - f2 B D) / 2` as an integrated linear
combination of `f2` forms. -/
example : ∫ ω, (∑ i : Fin 4, (![1/2, 1/2, -1/2, -1/2] i : ℝ) •
      f2Form (![0, 1, 0, 1] i : Fin 3) (![2, 2, 2, 0] i)) (fun X => (fun (X : Fin 3) (_ : Unit) =>
        ![1/5, 1/2, 9/10] X) X ω) ∂(Measure.dirac ()) =
    ∑ i : Fin 4, (![1/2, 1/2, -1/2, -1/2] i : ℝ) *
      f2 (Measure.dirac ()) (fun (X : Fin 3) (_ : Unit) => ![1/5, 1/2, 9/10] X)
        (![0, 1, 0, 1] i) (![2, 2, 2, 0] i) :=
  integral_sum_smul_f2Form (fun _ => MemLp.of_discrete) _ _ _ _

#print axioms finrank_fSpace
#print axioms span_f3Form
#print axioms linearIndependent_f3Form

end MathlibExtTest.Biology.PopulationGenetics.FStatisticsBasis
