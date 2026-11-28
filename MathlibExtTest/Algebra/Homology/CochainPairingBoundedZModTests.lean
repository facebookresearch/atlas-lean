/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.CochainGradedPairingHomologyLaws
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedFunctor
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Data.ZMod.Basic
public meta import Mathlib.Tactic.NormNum

/-!
# Nonzero cochain pairings over a ring with zero divisors

The constant cochain complex with coefficient ring `ZMod 6` has zero differentials and
multiplication as its graded pairing. Its homology classes retain their literal coefficients.
The degree-one class of two and degree-two class of three are nonzero, while their product is
zero. A second product has nonzero coordinate two. The degree-zero unit class and its image
under multiplication by three use the canonical homology pairing laws.

A genuine bounded integer cochain complex has the same nonzero coefficient module at degree
zero. Its single-term isomorphism detects the nonzero coefficient three.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct

namespace CochainPairingBoundedZModTests

private abbrev R := ZMod 6

private abbrev K : CochainComplex (ModuleCat R) ℕ where
  X _ := ModuleCat.of R R
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

private abbrev data (n : ℕ) : (K.sc n).LeftHomologyData :=
  ShortComplex.LeftHomologyData.ofZeros (K.sc n) (by rfl) (by rfl)

private def cycle (n : ℕ) (a : R) : K.cycles n :=
  (K.iCyclesIso n (n + 1) (by simp) (by rfl)).inv.hom a

private theorem cycle_value (n : ℕ) (a : R) : (K.iCycles n).hom (cycle n a) = a :=
  ConcreteCategory.congr_hom
    (K.iCyclesIso_inv_hom_id n (n + 1) (by simp) (by rfl)) a

private def classOf (n : ℕ) (a : R) : K.homology n :=
  (K.homologyπ n).hom (cycle n a)

private def detector (n : ℕ) : K.homology n →ₗ[R] R :=
  (data n).homologyIso.hom.hom

private theorem detector_pi (n : ℕ) (z : K.cycles n) :
    detector n ((K.homologyπ n).hom z) = (K.iCycles n).hom z := by
  have h₁ := (data n).homologyπ_comp_homologyIso_hom
  have h₂ := (data n).cyclesIso_hom_comp_i
  have h : K.homologyπ n ≫ (data n).homologyIso.hom = K.iCycles n :=
    h₁.trans (by
      simpa only [data, ShortComplex.LeftHomologyData.ofZeros_H,
        ShortComplex.LeftHomologyData.ofZeros_i, ShortComplex.LeftHomologyData.ofZeros_π,
        HomologicalComplex.iCycles] using h₂)
  have hv := congrArg (fun f => f.hom z) h
  change (data n).homologyIso.hom.hom ((K.homologyπ n).hom z) =
    (K.iCycles n).hom z at hv
  exact hv

private theorem detector_class (n : ℕ) (a : R) : detector n (classOf n a) = a := by
  rw [classOf, detector_pi, cycle_value]

private theorem detector_injective (n : ℕ) : Function.Injective (detector n) :=
  (ModuleCat.mono_iff_injective (data n).homologyIso.hom).mp (by infer_instance)

private def pairing : CochainGradedPairing K K K where
  pair _ _ := ModuleCat.ofHom (TensorProduct.lid R R).toLinearMap
  leibniz _ _ := by
    simp only [K, MonoidalPreadditive.zero_tensor, MonoidalPreadditive.tensor_zero,
      comp_zero, zero_comp, zsmul_zero, add_zero]

private theorem pair_coordinate (p q : ℕ) (a b : R) :
    detector (p + q)
      ((pairing.pairHomology p q).hom (classOf p a ⊗ₜ[R] classOf q b)) = a * b := by
  dsimp only [classOf]
  rw [CochainGradedPairing.pairHomology_π_apply, detector_pi,
    CochainGradedPairing.pairCycles_i_apply, cycle_value, cycle_value]
  change (TensorProduct.lid R R) (a ⊗ₜ[R] b) = a * b
  simp [smul_eq_mul]

example : classOf 1 (2 : R) ≠ 0 := by
  intro h
  have h' := congrArg (detector 1) h
  rw [detector_class, map_zero] at h'
  exact (by decide : (2 : R) ≠ 0) h'

example : classOf 2 (3 : R) ≠ 0 := by
  intro h
  have h' := congrArg (detector 2) h
  rw [detector_class, map_zero] at h'
  exact (by decide : (3 : R) ≠ 0) h'

example :
    (pairing.pairHomology 1 2).hom (classOf 1 (2 : R) ⊗ₜ[R] classOf 2 (3 : R)) = 0 := by
  apply detector_injective 3
  have h := pair_coordinate 1 2 (2 : R) (3 : R)
  have hprod : (2 : R) * 3 = 0 := by decide
  exact h.trans (hprod.trans (map_zero (detector 3)).symm)

example :
    (pairing.pairHomology 1 2).hom (classOf 1 (1 : R) ⊗ₜ[R] classOf 2 (2 : R)) ≠ 0 := by
  intro h
  have h' := congrArg (detector 3) h
  have hc := pair_coordinate 1 2 (1 : R) (2 : R)
  have hz := hc.symm.trans h'
  have htwo : (2 : R) ≠ 0 := by decide
  apply htwo
  simpa only [one_mul, map_zero] using hz

example :
    detector 0 (CochainGradedPairing.homologyUnitClass R (cycle 0 (1 : R))) = 1 := by
  change detector 0 (classOf 0 (1 : R)) = 1
  exact detector_class 0 1

private def scale (a : R) : K ⟶ K where
  f _ := ModuleCat.ofHom (a • (LinearMap.id : R →ₗ[R] R))
  comm' _ _ _ := by simp [K]

example :
    detector 0 ((homologyMap (scale (3 : R)) 0).hom
      (CochainGradedPairing.homologyUnitClass R (cycle 0 (1 : R)))) = 3 := by
  rw [CochainGradedPairing.homologyUnitClass_map]
  change detector 0 ((K.homologyπ 0).hom
    ((cyclesMap (scale (3 : R)) 0).hom (cycle 0 (1 : R)))) = 3
  rw [detector_pi]
  have h := congrArg (fun f => f.hom (cycle 0 (1 : R)))
    (cyclesMap_i (scale (3 : R)) 0)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [cycle_value] at h
  change (K.iCycles 0).hom ((cyclesMap (scale (3 : R)) 0).hom
    (cycle 0 (1 : R))) = (3 : R)
  have hscale : ((scale (3 : R)).f 0).hom (1 : R) = (3 : R) := by rfl
  exact h.trans hscale

private abbrev singleTerm : CochainComplex (ModuleCat R) ℤ :=
  (HomologicalComplex.single (ModuleCat R) (ComplexShape.up ℤ) 0).obj (ModuleCat.of R R)

private def boundedSingle : CochainComplex.Bounded (ModuleCat R) :=
  CochainComplex.Bounded.of (ModuleCat R) singleTerm 0 0 (by
    intro j hj
    apply HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of R R)
    rcases hj with hj | hj
    · exact ne_of_lt hj
    · exact ne_of_gt hj)

private def singleIso : boundedSingle.obj.X 0 ≅ ModuleCat.of R R :=
  HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)

private def singleValue : boundedSingle.obj.X 0 := singleIso.inv.hom (3 : R)

private theorem single_coordinate : singleIso.hom.hom singleValue = 3 :=
  ConcreteCategory.congr_hom singleIso.inv_hom_id (3 : R)

example : singleValue ≠ 0 := by
  intro h
  have h' := congrArg singleIso.hom.hom h
  rw [single_coordinate, map_zero] at h'
  exact (by decide : (3 : R) ≠ 0) h'

end CochainPairingBoundedZModTests
