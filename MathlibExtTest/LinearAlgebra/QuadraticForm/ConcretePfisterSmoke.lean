/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.QuadraticForm.PfisterIsotropicSubspace
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Concrete rational and characteristic-two quasi-Pfister forms

Over `ℚ`, the one-fold Pfister form with parameter one is `x_empty²-x_singleton²`.
Its carrier has dimension two and its radical is zero. The two coordinate
vectors represent one and minus one; the nonzero diagonal vector is
isotropic, and coordinates three and two represent five. Roundness gives
an actual isometry-equivalence after scaling by five. The successor map
recovers those two coordinates. Empty parameter and empty carrier edges
retain dimensions one and zero, respectively. Over `ZMod 2`, the same one-slot
subset form is totally singular, its radical is the diagonal line, and it
remains round as a quasi-Pfister form.
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

section CharacteristicTwo

private abbrev BinaryCarrier := Finset (Fin 1) → ZMod 2
private def binaryParameters : Fin 1 → (ZMod 2)ˣ := fun _ => 1
private abbrev binaryQuasiPfister := QuadraticForm.pfister (ZMod 2) binaryParameters
private def binaryDiagonal : BinaryCarrier := fun _ => 1

private theorem binary_apply (x : BinaryCarrier) :
    binaryQuasiPfister x = (x ∅) ^ 2 + (x {0}) ^ 2 := by
  have hneg : -(1 : ZMod 2) = 1 := by decide
  rw [QuadraticForm.pfister_apply, subsets_one]
  simp [QuadraticForm.pfisterWeight, binaryParameters, hneg, pow_two]

private theorem binary_frobenius (x : BinaryCarrier) :
    binaryQuasiPfister x = (x ∅ + x {0}) ^ 2 := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [binary_apply, add_sq]
  simp [htwo]

private theorem binary_add (x y : BinaryCarrier) :
    binaryQuasiPfister (x + y) = binaryQuasiPfister x + binaryQuasiPfister y := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp only [binary_apply, Pi.add_apply, add_sq, htwo, zero_mul, add_zero]
  ring

private theorem binary_polar_zero : binaryQuasiPfister.polarBilin = 0 := by
  refine LinearMap.ext fun (x : BinaryCarrier) => ?_
  refine LinearMap.ext fun (y : BinaryCarrier) => ?_
  change binaryQuasiPfister (x + y) - binaryQuasiPfister x - binaryQuasiPfister y = 0
  rw [binary_add]
  ring

private theorem binary_value_zero_iff (x : BinaryCarrier) :
    binaryQuasiPfister x = 0 ↔ x ∅ = x {0} := by
  rw [binary_frobenius, sq_eq_zero_iff]
  rw [← ZModModule.sub_eq_add (x ∅) (x {0}), sub_eq_zero]

private theorem binary_mem_radical_iff (x : BinaryCarrier) :
    x ∈ binaryQuasiPfister.radical ↔ x ∅ = x {0} := by
  rw [QuadraticMap.mem_radical_iff']
  constructor
  · intro h
    exact (binary_value_zero_iff x).mp h.1
  · intro h
    have hx : binaryQuasiPfister x = 0 := (binary_value_zero_iff x).mpr h
    exact ⟨hx, fun y => by rw [binary_add, hx, zero_add]⟩

private theorem binaryDiagonal_mem_radical :
    binaryDiagonal ∈ binaryQuasiPfister.radical :=
  (binary_mem_radical_iff binaryDiagonal).mpr rfl

private theorem binaryDiagonal_nonzero : binaryDiagonal ≠ 0 := by
  intro h
  have hc := congrArg (fun x : BinaryCarrier => x ∅) h
  change (1 : ZMod 2) = 0 at hc
  exact one_ne_zero hc

private theorem binary_radical_line :
    binaryQuasiPfister.radical = Submodule.span (ZMod 2) {binaryDiagonal} := by
  apply le_antisymm
  · intro x hx
    have hcoords := (binary_mem_radical_iff x).mp hx
    have hvector : x = (x ∅) • binaryDiagonal := by
      funext s
      have hs : s = ∅ ∨ s = {0} := by
        have hmem : s ∈ (Finset.univ : Finset (Finset (Fin 1))) := Finset.mem_univ s
        rw [subsets_one] at hmem
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
      rcases hs with rfl | rfl <;> simp [binaryDiagonal, hcoords]
    rw [hvector]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact binaryDiagonal_mem_radical

private theorem binary_not_nondegenerate : ¬ binaryQuasiPfister.Nondegenerate := by
  intro h
  have hmem : binaryDiagonal ∈ (⊥ : Submodule (ZMod 2) BinaryCarrier) :=
    h.radical_eq_bot ▸ binaryDiagonal_mem_radical
  exact binaryDiagonal_nonzero ((Submodule.mem_bot (ZMod 2)).mp hmem)

-- In characteristic two this actual subset form is round and totally singular.
-- Its nonzero diagonal radical witnesses that it is degenerate.
example : binaryQuasiPfister.IsRound ∧ binaryQuasiPfister.polarBilin = 0 ∧
    binaryQuasiPfister.radical = Submodule.span (ZMod 2) {binaryDiagonal} ∧
    binaryDiagonal ∈ binaryQuasiPfister.radical ∧ binaryDiagonal ≠ 0 ∧
    ¬ binaryQuasiPfister.Nondegenerate := by
  exact ⟨QuadraticForm.pfister_isRound (ZMod 2) binaryParameters,
    binary_polar_zero, binary_radical_line, binaryDiagonal_mem_radical,
    binaryDiagonal_nonzero, binary_not_nondegenerate⟩

example (x : BinaryCarrier) :
    binaryQuasiPfister x = (x ∅ + x {0}) ^ 2 ∧
      (x ∈ binaryQuasiPfister.radical ↔ x ∅ = x {0}) :=
  ⟨binary_frobenius x, binary_mem_radical_iff x⟩

end CharacteristicTwo

end MathlibExtTest.ConcretePfister
