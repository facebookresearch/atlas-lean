/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.PrismaticDividedFrobenius
import MathlibExt.AlgebraicGeometry.CrystallinePrismaticSite
import MathlibExt.AlgebraicGeometry.PrismaticPeriodFrames

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MathlibExt.RingTheory
open MathlibExt.AlgebraicGeometry.PrismaticNygaardTowers
open MathlibExt.AlgebraicGeometry.PrismaticNygaardModels
open MathlibExt.AlgebraicGeometry.PrismaticDividedFrobenius
open MathlibExt.AlgebraicGeometry.CrystallinePrismaticSite

namespace MathlibExtTest.PrismaticSyntomicShifts

abbrev A := PadicInt 2

theorem regularTwo : Function.Injective (fun x : A ↦ (2 : A) * x) :=
  fun _ _ h ↦ mul_left_cancel₀ (by norm_num : (2 : A) ≠ 0) h

def twoDomain : Domain 2 A (2 : A) 1 :=
  ⟨2, by
    change DeltaRing.frobenius 2 A 2 ∈ (Ideal.span {(2 : A)}) ^ 1
    rw [baseFrobenius]
    simp⟩

example : dividedValue 2 A (2 : A) 1 twoDomain = 1 := by
  apply power_mul_injective A (2 : A) regularTwo 1
  change (2 : A) ^ 1 * dividedValue 2 A (2 : A) 1 twoDomain = (2 : A) ^ 1 * 1
  rw [divisor_mul_value, baseFrobenius]
  norm_num [twoDomain]

example : (phi 2 A (2 : A) regularTwo 1 - can 2 A (2 : A) 1).f 0
    (sourceGenerator 2 A (2 : A) 1 twoDomain) = targetGenerator A (-1) := by
  apply (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    ((ModuleCat.uliftFunctor.{1, 0} ℤ).obj (ModuleCat.of ℤ A))).toLinearEquiv.injective
  change ULift.up (dividedValue 2 A (2 : A) 1 twoDomain) - ULift.up (2 : A) =
    ULift.up (-1 : A)
  have h : dividedValue 2 A (2 : A) 1 twoDomain = 1 := by
    apply power_mul_injective A (2 : A) regularTwo 1
    change (2 : A) ^ 1 * dividedValue 2 A (2 : A) 1 twoDomain = (2 : A) ^ 1 * 1
    rw [divisor_mul_value, baseFrobenius]
    norm_num [twoDomain]
  rw [h]
  apply ULift.ext
  norm_num

def oneDomain : Domain 2 A (2 : A) 0 :=
  ⟨1, by change DeltaRing.frobenius 2 A 1 ∈ (Ideal.span {(2 : A)}) ^ 0; simp⟩

/-- The negative twist multiplies the true Frobenius by the actual divisor. -/
example : (phiSigned 2 A (2 : A) regularTwo (-1)).f 0
    (sourceGenerator 2 A (2 : A) 0 oneDomain) = targetGenerator A 2 := by
  apply (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    ((ModuleCat.uliftFunctor.{1, 0} ℤ).obj (ModuleCat.of ℤ A))).toLinearEquiv.injective
  change ULift.up ((2 : A) * dividedValue 2 A (2 : A) 0 oneDomain) = ULift.up (2 : A)
  have h : dividedValue 2 A (2 : A) 0 oneDomain = 1 := by
    have hd := divisor_mul_value 2 A (2 : A) 0 oneDomain
    simpa [oneDomain, baseFrobenius] using hd
  rw [h]
  apply ULift.ext
  simp

/-- The fiber includes the genuine nonzero source in degree zero. -/
example : ¬ IsZero ((localSyntomic 2 A (2 : A) regularTwo 0).X 0) := by
  intro h
  change IsZero ((CochainComplex.mappingCone
    (phi 2 A (2 : A) regularTwo 0 - can 2 A (2 : A) 0)).X (-1)) at h
  have hs := ((CochainComplex.mappingCone.isZero_X_iff _ (-1)).mp h).1
  have hm := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    ((ModuleCat.uliftFunctor.{1, 0} ℤ).obj
      (ModuleCat.of ℤ (Domain 2 A (2 : A) 0)))).isZero_iff.mp hs
  have hs : Subsingleton (ULift.{1} (Domain 2 A (2 : A) 0)) :=
    ModuleCat.isZero_iff_subsingleton.mp hm
  have he : (ULift.up oneDomain : ULift.{1} (Domain 2 A (2 : A) 0)) = 0 :=
    hs.elim _ _
  exact one_ne_zero (congrArg (fun x ↦ x.down.val) he)

/-- The same fiber includes the genuine nonzero target in degree one. -/
example : ¬ IsZero ((localSyntomic 2 A (2 : A) regularTwo 0).X 1) := by
  intro h
  change IsZero ((CochainComplex.mappingCone
    (phi 2 A (2 : A) regularTwo 0 - can 2 A (2 : A) 0)).X 0) at h
  have ht := ((CochainComplex.mappingCone.isZero_X_iff _ 0).mp h).2
  have hm := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    ((ModuleCat.uliftFunctor.{1, 0} ℤ).obj (ModuleCat.of ℤ A))).isZero_iff.mp ht
  have hs : Subsingleton (ULift.{1} A) := ModuleCat.isZero_iff_subsingleton.mp hm
  have he : (ULift.up (1 : A) : ULift.{1} A) = 0 := hs.elim _ _
  exact one_ne_zero (congrArg ULift.down he)

#print axioms MathlibExt.AlgebraicGeometry.PrismaticDividedFrobenius.dividedLinear
#print axioms MathlibExt.AlgebraicGeometry.PrismaticPeriodFrames.Generator.vector

end MathlibExtTest.PrismaticSyntomicShifts
