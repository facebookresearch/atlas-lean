/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricCoefficientMaps
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricShuffleCoordinates
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.ZMod.Basic
public meta import Mathlib.Tactic.FinCases
public meta import Mathlib.Tactic.NormNum

/-!
# Hochschild maps and proper shuffles over a ring with zero divisors

The ground ring is `ℤ/6` and the algebra and coefficients are `ℤ/6[X]`.
Substitution `X ↦ X + 1` changes both the algebra and coefficient entries.
Multiplication by two changes only the coefficient head. These maps retain
the boundary and normalization squares without a flatness hypothesis.

The degree-zero shuffle retains the coefficient unit. The crossing of two
degree-one words has sign minus one and interchanges their tensor entries.
Proper both-positive relations leave degree one unchanged, and coefficient
maps retain their original representatives in that quotient.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open ModuleCat.Algebra.Hochschild
open ModuleCat.Algebra.Hochschild.Symmetric
open AlgebraicTopology.EilenbergZilber
open scoped TensorProduct BigOperators

namespace MathlibExtTest.Algebra.Homology.HochschildExport

private abbrev R := ZMod 6

private abbrev A := Polynomial R

private abbrev substitution : A →ₙₐ[R] A :=
  AlgHom.toNonUnitalAlgHom (Polynomial.aeval (Polynomial.X + 1 : A))

private abbrev coefficientSubstitution : A →ₗ[R] A := (substitution : A →ₗ[R] A)

private lemma substitution_X : substitution Polynomial.X = (Polynomial.X + 1 : A) := by
  change Polynomial.aeval (Polynomial.X + 1 : A) Polynomial.X = Polynomial.X + 1
  exact Polynomial.aeval_X _

private lemma substitution_one : substitution (1 : A) = 1 := by
  change Polynomial.aeval (Polynomial.X + 1 : A) (1 : A) = 1
  exact Polynomial.aeval_one _

private lemma substitution_left (a m : A) :
    coefficientSubstitution (a • m) = substitution a • coefficientSubstitution m := by
  change substitution (a * m) = substitution a * substitution m
  exact substitution.map_mul a m

private lemma substitution_right (a m : A) :
    coefficientSubstitution (MulOpposite.op a • m) =
      MulOpposite.op (substitution a) • coefficientSubstitution m := by
  change substitution (m * a) = substitution m * substitution a
  exact substitution.map_mul m a

private abbrev twiceCoefficient : A →ₗ[A] A := (2 : A) • LinearMap.id

private lemma twiceCoefficient_one : twiceCoefficient (1 : A) = 2 := by
  change (2 : A) * 1 = 2
  exact mul_one _

private abbrev emptyWord : Fin 0 → A := Fin.elim0

private abbrev crossing : Shuffle 1 1 where
  perm := Equiv.swap (0 : Fin 2) 1
  isShuffle := by
    constructor <;> intro i j hij
    · have h : i = j := Subsingleton.elim _ _
      simp [h] at hij
    · have h : i = j := Subsingleton.elim _ _
      simp [h] at hij

example : (2 : R) ≠ 0 ∧ (3 : R) ≠ 0 ∧ (2 : R) * 3 = 0 := by decide

example : substitution Polynomial.X = (Polynomial.X + 1 : A) ∧
    substitution Polynomial.X ≠ (Polynomial.X : A) := by
  constructor
  · exact substitution_X
  · rw [substitution_X]
    intro h
    have hOne : (1 : A) = 0 :=
      add_left_cancel (show (Polynomial.X : A) + 1 = Polynomial.X + 0 by
        simpa only [add_zero] using h)
    have hR : (1 : R) = 0 := by
      simpa only [map_one, map_zero] using
        congrArg (Polynomial.aeval (0 : R)) hOne
    exact (by decide : (1 : R) ≠ 0) hR

example :
    ((liftedMap substitution coefficientSubstitution substitution_left substitution_right).f 1).hom
      (ULift.up (Polynomial.X : A) ⊗ₜ[R] PiTensorProduct.tprod R (fun _ : Fin 1 => (1 : A))) =
        ULift.up (Polynomial.X + 1 : A) ⊗ₜ[R]
          PiTensorProduct.tprod R (fun _ : Fin 1 => (1 : A)) := by
  have hHead : coefficientSubstitution (Polynomial.X : A) = Polynomial.X + 1 := by
    change substitution Polynomial.X = Polynomial.X + 1
    exact substitution_X
  have hWord : (fun _ : Fin 1 => substitution (1 : A)) = fun _ : Fin 1 => (1 : A) := by
    funext i
    exact substitution_one
  exact (liftedMap_f_tprod substitution coefficientSubstitution substitution_left
    substitution_right 1 (Polynomial.X : A) (fun _ : Fin 1 => (1 : A))).trans
      (congrArg₂ (fun (m : A) (word : Fin 1 → A) =>
        ULift.up m ⊗ₜ[R] PiTensorProduct.tprod R word) hHead hWord)

example :
    (boundary R A A 1).hom
      (linearMap substitution coefficientSubstitution 2
        ((Polynomial.X : A) ⊗ₜ[R]
          PiTensorProduct.tprod R (fun _ : Fin 2 => (Polynomial.X + 1 : A)))) =
      linearMap substitution coefficientSubstitution 1
        ((boundary R A A 1).hom
          ((Polynomial.X : A) ⊗ₜ[R]
            PiTensorProduct.tprod R (fun _ : Fin 2 => (Polynomial.X + 1 : A)))) := by
  exact DFunLike.congr_fun
    (linearMap_boundary_comm substitution coefficientSubstitution substitution_left
      substitution_right 1) _

example :
    ((algebraRawCoefficientMap R A twiceCoefficient).f 1).hom
      ((1 : A) ⊗ₜ[R] PiTensorProduct.tprod R (fun _ : Fin 1 => (Polynomial.X : A))) =
      (2 : A) ⊗ₜ[R] PiTensorProduct.tprod R (fun _ : Fin 1 => (Polynomial.X : A)) := by
  let t : TensorPower R 1 A := PiTensorProduct.tprod R (fun _ : Fin 1 => (Polynomial.X : A))
  have hMap := DFunLike.congr_fun (algebraRawCoefficientMap_f R A twiceCoefficient 1)
    ((1 : A) ⊗ₜ[R] t)
  have hLevel := algebraCoefficientLevelMap_tmul R A twiceCoefficient 1 (1 : A) t
  exact hMap.trans (hLevel.trans
    (congrArg (fun m : A => m ⊗ₜ[R] t) twiceCoefficient_one))

example :
    algebraRawCoefficientMap R A twiceCoefficient ≫ algebraNormalizationProjection R A A =
      algebraNormalizationProjection R A A ≫
        algebraNormalizedCoefficientMap R A twiceCoefficient :=
  algebraNormalizationProjection_coefficient R A twiceCoefficient

example :
    signedRawShuffle R A A 0 0
      ((ULift.up (1 : A) ⊗ₜ[R] PiTensorProduct.tprod R emptyWord) ⊗ₜ[R]
        ((Polynomial.X : A) ⊗ₜ[R] PiTensorProduct.tprod R emptyWord)) =
      (Polynomial.X : A) ⊗ₜ[R] PiTensorProduct.tprod R emptyWord := by
  rw [signedRawShuffle_zero_zero, diagonalRaw_tprod]
  simp only [one_smul]
  exact congrArg (fun word : Fin 0 → A =>
    (Polynomial.X : A) ⊗ₜ[R] PiTensorProduct.tprod R word) (Subsingleton.elim _ _)

example :
    signedRawShuffle R A A 1 1
      ((ULift.up (1 : A) ⊗ₜ[R]
        PiTensorProduct.tprod R (fun _ : Fin 1 => (Polynomial.X : A))) ⊗ₜ[R]
        ((1 : A) ⊗ₜ[R] PiTensorProduct.tprod R (fun _ : Fin 1 => (1 : A)))) =
      ∑ s : Shuffle 1 1, shuffleSignZ s •
        ((1 : A) ⊗ₜ[R] PiTensorProduct.tprod R
          (fun i => Fin.append (fun _ : Fin 1 => (Polynomial.X : A))
            (fun _ : Fin 1 => (1 : A)) (s.perm.symm i))) := by
  simpa only [ULift.down_up, one_smul] using
    signedRawShuffle_tprod R A A 1 1 (ULift.up (1 : A)) (1 : A)
      (fun _ : Fin 1 => (Polynomial.X : A)) (fun _ : Fin 1 => (1 : A))

example : shuffleSignZ crossing = -1 := by
  simp [shuffleSignZ, shuffleSign]

example :
    rawShuffleTerm R A A crossing
      ((ULift.up (1 : A) ⊗ₜ[R]
        PiTensorProduct.tprod R (fun _ : Fin 1 => (Polynomial.X : A))) ⊗ₜ[R]
        ((1 : A) ⊗ₜ[R] PiTensorProduct.tprod R (fun _ : Fin 1 => (1 : A)))) =
      (1 : A) ⊗ₜ[R] PiTensorProduct.tprod R
        (fun i : Fin 2 => if i = 0 then (1 : A) else Polynomial.X) := by
  rw [rawShuffleTerm_tprod]
  simp only [one_smul]
  apply congrArg (fun word : Fin 2 → A => (1 : A) ⊗ₜ[R] PiTensorProduct.tprod R word)
  funext i
  fin_cases i
  · change Fin.append (fun _ : Fin 1 => (Polynomial.X : A))
      (fun _ : Fin 1 => (1 : A)) (Fin.natAdd 1 (0 : Fin 1)) = 1
    exact Fin.append_right _ _ _
  · change Fin.append (fun _ : Fin 1 => (Polynomial.X : A))
      (fun _ : Fin 1 => (1 : A)) (Fin.castAdd 1 (0 : Fin 1)) = Polynomial.X
    exact Fin.append_left _ _ _

example : algebraPositiveRelations R A A 1 = ⊥ :=
  algebraPositiveRelations_low R A A 1 (by decide)

example :
    ((algebraPositiveCoefficientMap R A twiceCoefficient).f 1).hom
      ((algebraPositiveRelations R A A 1).mkQ
        ((1 : A) ⊗ₜ[R] PiTensorProduct.tprod R (fun _ : Fin 1 => (Polynomial.X : A)))) =
      (algebraPositiveRelations R A A 1).mkQ
        ((2 : A) ⊗ₜ[R] PiTensorProduct.tprod R (fun _ : Fin 1 => (Polynomial.X : A))) := by
  let t : TensorPower R 1 A := PiTensorProduct.tprod R (fun _ : Fin 1 => (Polynomial.X : A))
  have hMap := algebraPositiveCoefficientMap_f_mkQ R A twiceCoefficient 1 ((1 : A) ⊗ₜ[R] t)
  have hLevel := algebraCoefficientLevelMap_tmul R A twiceCoefficient 1 (1 : A) t
  have hWord : algebraCoefficientLevelMap R A twiceCoefficient 1 ((1 : A) ⊗ₜ[R] t) =
      (2 : A) ⊗ₜ[R] t :=
    hLevel.trans (congrArg (fun m : A => m ⊗ₜ[R] t) twiceCoefficient_one)
  exact hMap.trans (congrArg (algebraPositiveRelations R A A 1).mkQ hWord)

end MathlibExtTest.Algebra.Homology.HochschildExport
