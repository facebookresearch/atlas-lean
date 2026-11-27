/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.QuadraticForm.PfisterIsotropicSubspace
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# A concrete rational hyperbolic Pfister form

The one-fold Pfister form with parameter one is `x_empty²-x_singleton²`.
Its carrier has dimension two and its radical is zero. The two coordinate
vectors represent one and minus one; the nonzero diagonal vector is
isotropic, and coordinates three and two represent five. Roundness gives
an actual isometry-equivalence after scaling by five. The successor map
recovers those two coordinates. Empty parameter and empty carrier edges
retain dimensions one and zero, respectively.
-/

noncomputable section

open scoped BigOperators

namespace MathlibExtTest.ConcretePfister

private abbrev Carrier := Finset (Fin 1) → ℚ
private def parameters : Fin 1 → ℚˣ := fun _ => 1
private abbrev hyperbolic := QuadraticForm.pfister ℚ parameters
private def diagonal : Carrier := fun _ => 1
private def firstVector : Carrier := fun s => if s = ∅ then 1 else 0
private def secondVector : Carrier := fun s => if s = {0} then 1 else 0
private def fiveVector : Carrier := fun s => if s = ∅ then 3 else 2

private theorem subsets_one : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by
  decide

private theorem hyperbolic_apply (x : Carrier) :
    hyperbolic x = (x ∅) ^ 2 - (x {0}) ^ 2 := by
  rw [QuadraticForm.pfister_apply, subsets_one]
  simp [QuadraticForm.pfisterWeight, parameters, pow_two]; ring

private theorem diagonal_isotropic : hyperbolic diagonal = 0 := by
  rw [hyperbolic_apply]
  norm_num [diagonal]

private theorem diagonal_nonzero : diagonal ≠ 0 := by
  intro h
  have hc := congrArg (fun x : Carrier => x ∅) h
  norm_num [diagonal] at hc

private theorem not_anisotropic : ¬ hyperbolic.Anisotropic := by
  intro h
  exact diagonal_nonzero (h diagonal diagonal_isotropic)

private theorem represents_five : hyperbolic fiveVector = 5 := by
  rw [hyperbolic_apply]
  norm_num [fiveVector]

example : hyperbolic firstVector = 1 ∧ hyperbolic secondVector = -1 ∧
    hyperbolic diagonal = 0 ∧ diagonal ≠ 0 := by
  rw [hyperbolic_apply, hyperbolic_apply]
  norm_num [firstVector, secondVector]
  exact ⟨diagonal_isotropic, diagonal_nonzero⟩

example : Module.finrank ℚ Carrier = 2 ∧ hyperbolic.radical = ⊥ ∧ hyperbolic.Nondegenerate := by
  refine ⟨?_, QuadraticForm.pfister_radical ℚ parameters,
    QuadraticForm.pfister_nondegenerate ℚ parameters⟩
  simp

example : ¬ hyperbolic.Anisotropic ∧ hyperbolic.HasHalfDimensionalTotallyIsotropicSubspace :=
  ⟨not_anisotropic,
    QuadraticForm.pfister_hasHalfDimensionalTotallyIsotropicSubspace ℚ parameters not_anisotropic⟩

example : ∃ W : Submodule ℚ Carrier,
    Module.finrank ℚ W = 1 ∧ hyperbolic.IsTotallyIsotropic W := by
  obtain ⟨W, hdim, hiso⟩ :=
    QuadraticForm.pfister_exists_halfDimensionalTotallyIsotropic ℚ parameters not_anisotropic
  exact ⟨W, by simpa using hdim, hiso⟩

example : hyperbolic fiveVector = 5 ∧ ((5 : ℚ) • hyperbolic).Equivalent hyperbolic := by
  refine ⟨represents_five, ?_⟩
  exact (QuadraticForm.pfister_isRound ℚ parameters 5 (by norm_num)).mp
    ⟨fiveVector, represents_five⟩

example :
    (QuadraticForm.pfisterSuccLinearEquiv ℚ 0 fiveVector).1 ∅ = 3 ∧
      (QuadraticForm.pfisterSuccLinearEquiv ℚ 0 fiveVector).2 ∅ = 2 ∧
      (QuadraticForm.pfisterSuccLinearEquiv ℚ 0).symm
        (QuadraticForm.pfisterSuccLinearEquiv ℚ 0 fiveVector) = fiveVector := by
  rw [QuadraticForm.pfisterSuccLinearEquiv_apply_fst,
    QuadraticForm.pfisterSuccLinearEquiv_apply_snd]
  norm_num [QuadraticForm.pfisterLowerIndex, QuadraticForm.pfisterUpperIndex, fiveVector]

private def noParameters : Fin 0 → ℚˣ := fun i => Fin.elim0 i

example : QuadraticForm.pfister ℚ noParameters (fun _ => (3 : ℚ)) = 9 ∧
    Module.finrank ℚ (Finset (Fin 0) → ℚ) = 1 := by
  constructor
  · rw [QuadraticForm.pfister_apply]
    norm_num [QuadraticForm.pfisterWeight]
    have hempty : (default : Finset (Fin 0)) = ∅ := by
      ext i
      exact Fin.elim0 i
    rw [hempty]
    simp
  · simp

example :
    (0 : QuadraticForm ℚ (Fin 0 → ℚ)).HasHalfDimensionalTotallyIsotropicSubspace := by
  refine ⟨inferInstance, ⊥, ?_, ?_⟩
  · intro x hx
    simp
  · simp

end MathlibExtTest.ConcretePfister
