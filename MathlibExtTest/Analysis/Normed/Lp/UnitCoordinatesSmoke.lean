/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Analysis.Normed.Lp.UnitCoordinates
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases

/-!
# Nonconstant unit phases on a nonzero square-summable vector

The two coordinates `(3,4i)` have L² norm five. Multiplication by the
unit phases `(i,-i)` gives `(3i,4)`, while inverse multiplication of the
original vector gives `(-3i,-4)`. The forward and inverse maps preserve
the norm and recombine to the original vector. An empty index has only zero.
-/

noncomputable section

open scoped ENNReal

namespace MathlibExtTest.UnitCoordinates

open MathlibExt.Analysis.Normed.Lp

private abbrev Space := lp (fun _ : Fin 2 => ℂ) 2

private def phases (i : Fin 2) : ℂ := if i = 0 then Complex.I else -Complex.I

private theorem phases_unit (i : Fin 2) : ‖phases i‖ = 1 := by
  fin_cases i <;> simp [phases]

private def input : Space := lp.single 2 0 (3 : ℂ) + lp.single 2 1 (4 * Complex.I)

private abbrev phaseEquiv := unitCoordinateEquiv phases phases_unit

private theorem input_norm : ‖input‖ = 5 := by
  have hs := lp.norm_sum_single (p := 2) (by norm_num)
    (fun i : Fin 2 => if i = 0 then (3 : ℂ) else 4 * Complex.I) Finset.univ
  norm_num [Fin.sum_univ_two, norm_mul, Real.rpow_two] at hs
  have hsq : ‖input‖ ^ 2 = 25 := by simpa only [input] using hs
  nlinarith [norm_nonneg input]

example : ‖input‖ = 5 ∧ input ≠ 0 := by
  refine ⟨input_norm, ?_⟩
  intro h
  have hn := input_norm
  rw [h, norm_zero] at hn
  norm_num at hn

example : phaseEquiv input 0 = 3 * Complex.I ∧ phaseEquiv input 1 = 4 := by
  simp only [unitCoordinateEquiv_apply]
  norm_num [phases, input, mul_comm, mul_left_comm, Complex.I_mul_I]
  rw [← mul_assoc, Complex.I_mul_I]; norm_num

example : phaseEquiv.symm input 0 = -3 * Complex.I ∧ phaseEquiv.symm input 1 = -4 := by
  simp only [unitCoordinateEquiv_symm_apply]
  norm_num [phases, input, mul_comm, mul_left_comm, Complex.I_mul_I]
  rw [← mul_assoc, Complex.I_mul_I]; norm_num

example : ‖phaseEquiv input‖ = 5 ∧ ‖phaseEquiv.symm input‖ = 5 := by
  rw [phaseEquiv.norm_map, phaseEquiv.symm.norm_map, input_norm]
  exact ⟨rfl, rfl⟩

example : phaseEquiv.symm (phaseEquiv input) = input ∧
    phaseEquiv (phaseEquiv.symm input) = input :=
  ⟨phaseEquiv.symm_apply_apply input, phaseEquiv.apply_symm_apply input⟩

private def emptyPhases : Fin 0 → ℂ := fun i => Fin.elim0 i
private theorem empty_unit (i : Fin 0) : ‖emptyPhases i‖ = 1 := Fin.elim0 i

example (x : lp (fun _ : Fin 0 => ℂ) 2) :
    unitCoordinateEquiv emptyPhases empty_unit x = x ∧ ‖x‖ = 0 := by
  have hx : x = 0 := by
    apply lp.ext
    funext i
    exact Fin.elim0 i
  simp [hx]

end MathlibExtTest.UnitCoordinates
