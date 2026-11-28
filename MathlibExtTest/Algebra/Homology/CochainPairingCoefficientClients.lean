/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Homology.CochainGradedPairingDifferential
import MathlibExt.Algebra.Homology.CochainGradedPairingHomologyLaws
import Mathlib.Algebra.Algebra.Bilinear
import MathlibExt.CategoryTheory.NatIso.ComparisonCoherence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.LinearAlgebra.Matrix.StdBasis
meta import Mathlib.Tactic.NormNum
meta import Mathlib.Tactic.FinCases

/-!
# Nonzero cohomology products and restriction of coefficients

Constant zero-differential cochains on an arbitrary algebra give a graded
cohomology product in every degree. The cycle/homology coordinates identify
that product with algebra multiplication. Scalar coefficient maps satisfy the
joint naturality square; restricting the resulting morphism to integer scalars
keeps its action on carriers, without assuming that tensor products or homology
commute with a change of scalars.

The concrete algebra is the noncommutative two-by-two integer matrix algebra.
Multiplying the two off-diagonal matrix units in degrees one and two gives the
first diagonal unit; reversing the inputs gives the other diagonal unit. Thus
the product, its coefficient naturality and the restricted map are nonzero.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct

noncomputable section
universe u

namespace MathlibExtTest.CochainPairingCoefficient

section General

variable (R : Type u) [CommRing R] (A : Type u) [Ring A] [Algebra R A]

private abbrev M := ModuleCat.of R A

/-- The coefficients occur in every natural degree, with zero differentials. -/
private abbrev K : CochainComplex (ModuleCat.{u} R) ℕ where
  X _ := M R A
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

private def pairing : CochainGradedPairing (K R A) (K R A) (K R A) where
  pair _ _ := ModuleCat.ofHom (LinearMap.mul' R A)
  leibniz _ _ := by
    simp only [K, MonoidalPreadditive.zero_tensor, MonoidalPreadditive.tensor_zero,
      comp_zero, zero_comp, zsmul_zero, add_zero]

private def cycleIso (n : ℕ) : (K R A).cycles n ≅ M R A :=
  (K R A).iCyclesIso n (n + 1) (by simp) rfl

private def classIso (n : ℕ) : (K R A).cycles n ≅ (K R A).homology n :=
  (K R A).isoHomologyπ ((ComplexShape.up ℕ).prev n) n rfl rfl

private def coordinate (n : ℕ) : (K R A).homology n ≅ M R A :=
  (classIso R A n).symm ≪≫ cycleIso R A n

private def cycle (n : ℕ) (x : A) : (K R A).cycles n := (cycleIso R A n).inv.hom x
private def cls (n : ℕ) (x : A) : (K R A).homology n :=
  ((K R A).homologyπ n).hom (cycle R A n x)

private lemma cycle_inclusion (n : ℕ) (x : A) :
    ((K R A).iCycles n).hom (cycle R A n x) = x := by
  have h := congrArg (fun f => f.hom x)
    ((K R A).iCyclesIso_inv_hom_id n (n + 1) (by simp) rfl)
  change ((K R A).iCycles n).hom
    (((K R A).iCyclesIso n (n + 1) (by simp) rfl).inv.hom x) = x at h
  exact h

private lemma coordinate_pi (n : ℕ) (z : (K R A).cycles n) :
    (coordinate R A n).hom.hom (((K R A).homologyπ n).hom z) =
      ((K R A).iCycles n).hom z := by
  have h := congrArg (fun f => f.hom z)
    ((K R A).isoHomologyπ_hom_inv_id ((ComplexShape.up ℕ).prev n) n rfl rfl)
  have h' : (classIso R A n).inv.hom (((K R A).homologyπ n).hom z) = z := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply, classIso] using h
  change (cycleIso R A n).hom.hom
    ((classIso R A n).inv.hom (((K R A).homologyπ n).hom z)) = _
  rw [h']
  rfl

private lemma class_coordinate (n : ℕ) (x : A) :
    (coordinate R A n).hom.hom (cls R A n x) = x :=
  (coordinate_pi R A n (cycle R A n x)).trans (cycle_inclusion R A n x)

/-- The actual graded cohomology pairing multiplies the two represented coefficients. -/
private lemma product_coordinate (p q : ℕ) (x y : A) :
    (coordinate R A (p + q)).hom.hom
      (((pairing R A).pairHomology p q).hom (cls R A p x ⊗ₜ[R] cls R A q y)) = x * y := by
  dsimp only [cls]
  rw [CochainGradedPairing.pairHomology_π_apply R (pairing R A) p q,
    coordinate_pi, CochainGradedPairing.pairCycles_i_apply R (pairing R A) p q,
    cycle_inclusion, cycle_inclusion]
  rfl

private abbrev coefficient (a : R) : K R A ⟶ K R A where
  f _ := ModuleCat.ofHom (a • LinearMap.id)
  comm' _ _ _ := by simp [K]

private lemma coefficient_f (a : R) (i : ℕ) :
    (coefficient R A a).f i = a • 𝟙 (M R A) := rfl

private lemma coefficient_pairing (a b : R) (i j : ℕ) :
    (pairing R A).pair i j ≫ (coefficient R A (a * b)).f (i + j) =
      ((coefficient R A a).f i ⊗ₘ (coefficient R A b).f j) ≫
        (pairing R A).pair i j := by
  simp only [coefficient_f, MonoidalCategory.tensorHom_def,
    MonoidalLinear.smul_whiskerRight, MonoidalLinear.whiskerLeft_smul,
    MonoidalCategory.id_whiskerRight, MonoidalCategory.whiskerLeft_id,
    Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id, smul_smul]

/-- Genuine joint coefficient naturality, with output scalar `a*b`. -/
example (a b : R) (p q : ℕ) :
    (pairing R A).pairHomology p q ≫ homologyMap (coefficient R A (a * b)) (p + q) =
      (homologyMap (coefficient R A a) p ⊗ₘ homologyMap (coefficient R A b) q) ≫
        (pairing R A).pairHomology p q :=
  (CochainGradedPairing.pairHomology_naturality
    (pairing R A) (pairing R A) (coefficient R A a) (coefficient R A b)
    (coefficient R A (a * b)) (coefficient_pairing R A a b) p q).symm

/-- The actual restriction functor forgets only the scalar structure. -/
private def restrictedCarriers : ModuleCat.{u} R ⥤ Type u :=
  ModuleCat.restrictScalars (Int.castRingHom R) ⋙ forget (ModuleCat.{u} ℤ)

/-- The general comparison API recovers the nonzero product class after scalar restriction. -/
example (p q : ℕ) (x y : A) :
    (restrictedCarriers R).map (coordinate R A (p + q)).inv (x * y) =
      ((pairing R A).pairHomology p q).hom (cls R A p x ⊗ₜ[R] cls R A q y) := by
  apply Functor.map_iso_inv_point (restrictedCarriers R) (coordinate R A (p + q))
    (((pairing R A).pairHomology p q).hom (cls R A p x ⊗ₜ[R] cls R A q y)) (x * y)
  exact product_coordinate R A p q x y

end General

private abbrev ZMatrix := Matrix (Fin 2) (Fin 2) ℤ
private def leftUnit : ZMatrix := Matrix.single 0 1 1
private def rightUnit : ZMatrix := Matrix.single 1 0 1

example : ((coordinate ℤ ZMatrix 3).hom.hom
    (((pairing ℤ ZMatrix).pairHomology 1 2).hom
      (cls ℤ ZMatrix 1 leftUnit ⊗ₜ[ℤ] cls ℤ ZMatrix 2 rightUnit))) 0 0 = 1 := by
  have h := congrArg (fun m : ZMatrix => m 0 0)
    (product_coordinate ℤ ZMatrix 1 2 leftUnit rightUnit)
  norm_num [leftUnit, rightUnit, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single] at h
  exact h

example : ((coordinate ℤ ZMatrix 3).hom.hom
    (((pairing ℤ ZMatrix).pairHomology 1 2).hom
      (cls ℤ ZMatrix 1 rightUnit ⊗ₜ[ℤ] cls ℤ ZMatrix 2 leftUnit))) 0 0 = 0 := by
  have h := congrArg (fun m : ZMatrix => m 0 0)
    (product_coordinate ℤ ZMatrix 1 2 rightUnit leftUnit)
  norm_num [leftUnit, rightUnit, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single] at h
  exact h

example : ((pairing ℤ ZMatrix).pairHomology 1 2).hom
    (cls ℤ ZMatrix 1 leftUnit ⊗ₜ[ℤ] cls ℤ ZMatrix 2 rightUnit) ≠ 0 := by
  intro h
  have hc := product_coordinate ℤ ZMatrix 1 2 leftUnit rightUnit
  rw [h, map_zero] at hc
  have he := congrArg (fun m : ZMatrix => m 0 0) hc
  norm_num [leftUnit, rightUnit, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single] at he
  exact zero_ne_one (show (0 : ℤ) = 1 from he)

end MathlibExtTest.CochainPairingCoefficient
