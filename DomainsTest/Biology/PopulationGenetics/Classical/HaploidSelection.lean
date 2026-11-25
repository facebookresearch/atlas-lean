/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Classical.HaploidSelection
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt.Biology.PopulationGenetics.Selection

namespace MathlibExtTest.Biology.PopulationGenetics.Classical.HaploidSelection

/-- Frequencies in the two-type example. -/
noncomputable def p₂ : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- Fitnesses in the two-type example. -/
noncomputable def w₂ : Fin 2 → ℝ := ![2, 1]

/-- At generation zero the closed form returns the initial frequency. -/
example : (fun p => select p w₂)^[0] p₂ 0 = 1 / 2 := by
  rw [iterate_select (w := w₂) (p₀ := p₂)]
  · norm_num [p₂, w₂, Fin.sum_univ_two]
  · intro i
    fin_cases i <;> norm_num [w₂]
  · intro i
    fin_cases i <;> norm_num [p₂]
  · norm_num [p₂, Fin.sum_univ_two]

/-- After two generations, type `0` has frequency
`(1/2 * 2^2) / (1/2 * 2^2 + 1/2 * 1^2) = 4/5`. -/
example : (fun p => select p w₂)^[2] p₂ 0 = 4 / 5 := by
  rw [iterate_select (w := w₂) (p₀ := p₂)]
  · norm_num [p₂, w₂, Fin.sum_univ_two]
  · intro i
    fin_cases i <;> norm_num [w₂]
  · intro i
    fin_cases i <;> norm_num [p₂]
  · norm_num [p₂, Fin.sum_univ_two]

/-- A type absent initially stays absent: with `p₀ = (0, 1)`, type `0`
remains at frequency `0` after three generations even though it is fitter. -/
example : (fun p => select p w₂)^[3] ![0, 1] 0 = 0 := by
  rw [iterate_select (w := w₂) (p₀ := ![0, 1])]
  · norm_num [w₂, Fin.sum_univ_two]
  · intro i
    fin_cases i <;> norm_num [w₂]
  · intro i
    fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_two]

/-- Frequencies in the absent-fitter regression: type `2` is absent. -/
noncomputable def p₃ : Fin 3 → ℝ := ![1 / 2, 1 / 2, 0]

/-- Fitnesses in the absent-fitter regression: the absent type `2` is the
fittest in the ambient type. -/
noncomputable def w₃ : Fin 3 → ℝ := ![2, 1, 3]

/-- Regression: maximality is needed only among initially present types.
Although the absent type `2` has fitness `3 > 2`, it remains absent and the
initially present type `0` goes to fixation. -/
example :
    Filter.Tendsto (fun t : ℕ => (fun p => select p w₃)^[t] p₃) Filter.atTop
      (nhds (Pi.single (0 : Fin 3) 1)) := by
  refine tendsto_iterate_select_pi_single (w := w₃) (p₀ := p₃) ?_ ?_ ?_ 0 ?_ ?_
  · intro i
    fin_cases i <;> norm_num [w₃]
  · intro i
    fin_cases i <;> norm_num [p₃]
  · norm_num [p₃, Fin.sum_univ_three]
  · norm_num [p₃]
  · intro j hj hjk
    fin_cases j
    · exact (hjk rfl).elim
    · norm_num [w₃]
    · norm_num [p₃] at hj

end MathlibExtTest.Biology.PopulationGenetics.Classical.HaploidSelection
