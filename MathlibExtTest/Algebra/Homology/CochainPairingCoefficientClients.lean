/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Homology.CochainGradedPairingDifferential
import MathlibExt.CategoryTheory.NatIso.ComparisonCoherence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
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
private def K : CochainComplex (ModuleCat.{u} R) ℕ where
  X _ := M R A
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

private def pairing : CochainGradedPairing (K R A) (K R A) (K R A) where
  pair _ _ := ModuleCat.ofHom (LinearMap.mul' R A)
  leibniz _ _ := by simp [K]

private def cycleIso (n : ℕ) : (K R A).cycles n ≅ M R A :=
  (K R A).iCyclesIso n (n + 1) rfl rfl

private def classIso (n : ℕ) : (K R A).cycles n ≅ (K R A).homology n :=
  (K R A).isoHomologyπ ((ComplexShape.up ℕ).prev n) n rfl rfl

private def coordinate (n : ℕ) : (K R A).homology n ≅ M R A :=
  (classIso R A n).symm ≪≫ cycleIso R A n

private def cycle (n : ℕ) (x : A) : (K R A).cycles n := (cycleIso R A n).inv.hom x
private def cls (n : ℕ) (x : A) : (K R A).homology n :=
  ((K R A).homologyπ n).hom (cycle R A n x)

private lemma cycle_inclusion (n : ℕ) (x : A) :
    ((K R A).iCycles n).hom (cycle R A n x) = x :=
  ConcreteCategory.congr_hom
    ((K R A).iCyclesIso_inv_hom_id n (n + 1) rfl rfl) x

private lemma class_coordinate (n : ℕ) (x : A) :
    (coordinate R A n).hom.hom (cls R A n x) = x := by
  have h : (classIso R A n).inv.hom
      (((K R A).homologyπ n).hom (cycle R A n x)) = cycle R A n x := by
    simpa only [ConcreteCategory.id_apply] using
      ConcreteCategory.congr_hom (classIso R A n).hom_inv_id (cycle R A n x)
  have hi := cycle_inclusion R A n x
  change (cycleIso R A n).hom.hom
    ((classIso R A n).inv.hom (((K R A).homologyπ n).hom (cycle R A n x))) = x
  exact (congrArg (cycleIso R A n).hom.hom h).trans hi

/-- The actual graded cohomology pairing multiplies the two represented coefficients. -/
private lemma product_coordinate (p q : ℕ) (x y : A) :
    (coordinate R A (p + q)).hom.hom
      (((pairing R A).pairHomology p q).hom (cls R A p x ⊗ₜ[R] cls R A q y)) = x * y := by
  rw [CochainGradedPairing.pairHomology_π_apply]
  have h := CochainGradedPairing.pairCycles_i_apply R (pairing R A) p q
    (cycle R A p x) (cycle R A q y)
  have hp : (classIso R A (p + q)).inv.hom
      (((K R A).homologyπ (p + q)).hom
        (((pairing R A).pairCycles p q).hom (cycle R A p x ⊗ₜ[R] cycle R A q y))) =
      ((pairing R A).pairCycles p q).hom (cycle R A p x ⊗ₜ[R] cycle R A q y) := by
    simpa only [ConcreteCategory.id_apply] using
      ConcreteCategory.congr_hom (classIso R A (p + q)).hom_inv_id
        (((pairing R A).pairCycles p q).hom (cycle R A p x ⊗ₜ[R] cycle R A q y))
  change (cycleIso R A (p + q)).hom.hom
    ((classIso R A (p + q)).inv.hom
      (((K R A).homologyπ (p + q)).hom
        (((pairing R A).pairCycles p q).hom (cycle R A p x ⊗ₜ[R] cycle R A q y)))) = x * y
  rw [hp]
  change ((K R A).iCycles (p + q)).hom
    (((pairing R A).pairCycles p q).hom (cycle R A p x ⊗ₜ[R] cycle R A q y)) = x * y
  rw [h, cycle_inclusion, cycle_inclusion]
  rfl

private def coefficient (a : R) : K R A ⟶ K R A where
  f _ := ModuleCat.ofHom (a • LinearMap.id)
  comm' _ _ _ := by simp [K]

/-- Genuine joint coefficient naturality, with output scalar `a*b`. -/
example (a b : R) (p q : ℕ) :
    (pairing R A).pairHomology p q ≫ homologyMap (coefficient R A (a * b)) (p + q) =
      (homologyMap (coefficient R A a) p ⊗ₘ homologyMap (coefficient R A b) q) ≫
        (pairing R A).pairHomology p q := by
  symm
  apply CochainGradedPairing.pairHomology_naturality
    (pairing R A) (pairing R A) (coefficient R A a) (coefficient R A b)
    (coefficient R A (a * b))
  intro i j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      change (a * b) • (x * y) = (a • x) * (b • y)
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]

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
private def leftUnit : ZMatrix := Matrix.stdBasisMatrix 0 1 1
private def rightUnit : ZMatrix := Matrix.stdBasisMatrix 1 0 1

example : ((coordinate ℤ ZMatrix 3).hom.hom
    (((pairing ℤ ZMatrix).pairHomology 1 2).hom
      (cls ℤ ZMatrix 1 leftUnit ⊗ₜ[ℤ] cls ℤ ZMatrix 2 rightUnit))) 0 0 = 1 := by
  rw [product_coordinate]
  norm_num [leftUnit, rightUnit, Matrix.mul_apply, Fin.sum_univ_two]

example : ((coordinate ℤ ZMatrix 3).hom.hom
    (((pairing ℤ ZMatrix).pairHomology 1 2).hom
      (cls ℤ ZMatrix 1 rightUnit ⊗ₜ[ℤ] cls ℤ ZMatrix 2 leftUnit))) 0 0 = 0 := by
  rw [product_coordinate]
  norm_num [leftUnit, rightUnit, Matrix.mul_apply, Fin.sum_univ_two]

example : ((pairing ℤ ZMatrix).pairHomology 1 2).hom
    (cls ℤ ZMatrix 1 leftUnit ⊗ₜ[ℤ] cls ℤ ZMatrix 2 rightUnit) ≠ 0 := by
  intro h
  have hc := product_coordinate ℤ ZMatrix 1 2 leftUnit rightUnit
  rw [h, map_zero] at hc
  have he := congrArg (fun m : ZMatrix => m 0 0) hc
  norm_num [leftUnit, rightUnit, Matrix.mul_apply, Fin.sum_univ_two] at he

end MathlibExtTest.CochainPairingCoefficient
