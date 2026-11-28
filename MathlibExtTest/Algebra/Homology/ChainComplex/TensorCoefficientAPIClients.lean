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

public import MathlibExt.Algebra.Homology.ChainComplex.TensorCoefficient.Regular
public import MathlibExtTest.Algebra.Homology.ChainComplex.TensorCoefficientZMod

/-!
# Regular coefficients, chain-map transport and six-term tensor sequences

The nonsplit ZMod 4 coefficient sequence and multiplication-by-two complex give a nonzero
connecting arrow. The regular-coefficient unitor retains the scalar three on a pure tensor
and induces the same degree-zero class. A nonidentity negation isomorphism tests chain-map
transport and coefficient naturality.

The six-term sequence and its coefficient-map morphism use the literal connecting arrow,
with naturality in both the coefficient sequence and the fixed complex. The terminal
homology map is an epimorphism by the short exact sequence, without a coefficient-flatness
assumption.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open MathlibExtTest.TensorCoefficientZMod

namespace TensorCoefficientAPIClients

private abbrev R := R4

private def zeroTermIso : originalComplex.X 0 ≅ regular := eqToIso (by rfl)

private def zeroCoordinate (a : R) : originalComplex.X 0 := zeroTermIso.inv.hom a

private theorem zeroCoordinate_value (a : R) : zeroTermIso.hom.hom (zeroCoordinate a) = a :=
  ConcreteCategory.congr_hom zeroTermIso.inv_hom_id a

private def binaryValue : binaryComplex.X 0 →ₗ[R] binary :=
  (TensorProduct.rid R (ZMod 2)).toLinearMap.comp
    (TensorProduct.map (LinearMap.id : binary →ₗ[R] binary) zeroTermIso.hom.hom)

example :
    zeroTermIso.hom.hom
      (((ChainComplex.TensorCoefficient.regularIso R originalComplex).hom.f 0).hom
        ((3 : R) ⊗ₜ[R] zeroCoordinate 1)) = 3 := by
  rw [ChainComplex.TensorCoefficient.regularIso_tmul, map_smul, zeroCoordinate_value]
  simp

example :
    (ChainComplex.TensorCoefficient.regularHomologyIso R originalComplex 0).hom.hom
        ((ChainComplex.homologyZeroClass regularComplex).hom
          ((3 : R) ⊗ₜ[R] zeroCoordinate 1)) =
      (ChainComplex.homologyZeroClass originalComplex).hom (zeroCoordinate 3) := by
  change (HomologicalComplex.homologyMap
    (ChainComplex.TensorCoefficient.regularIso R originalComplex).hom 0).hom _ = _
  have h : ChainComplex.homologyZeroClass regularComplex ≫
      HomologicalComplex.homologyMap
        (ChainComplex.TensorCoefficient.regularIso R originalComplex).hom 0 =
      (ChainComplex.TensorCoefficient.regularIso R originalComplex).hom.f 0 ≫
        ChainComplex.homologyZeroClass originalComplex :=
    ChainComplex.homologyZeroClass_naturality
      (ChainComplex.TensorCoefficient.regularIso R originalComplex).hom
  have hv := congrArg
    (fun g : regularComplex.X 0 ⟶ originalComplex.homology 0 =>
      g ((3 : R) ⊗ₜ[R] zeroCoordinate 1)) h
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hv
  change (HomologicalComplex.homologyMap
    (ChainComplex.TensorCoefficient.regularIso R originalComplex).hom 0).hom
      ((ChainComplex.homologyZeroClass regularComplex).hom
        ((3 : R) ⊗ₜ[R] zeroCoordinate 1)) =
    (ChainComplex.homologyZeroClass originalComplex).hom
      (((ChainComplex.TensorCoefficient.regularIso R originalComplex).hom.f 0).hom
        ((3 : R) ⊗ₜ[R] zeroCoordinate 1)) at hv
  have hc : (3 : R) • zeroCoordinate 1 = zeroCoordinate 3 := by
    apply (ModuleCat.mono_iff_injective zeroTermIso.hom).mp inferInstance
    change zeroTermIso.hom.hom ((3 : R) • zeroCoordinate 1) =
      zeroTermIso.hom.hom (zeroCoordinate 3)
    rw [map_smul, zeroCoordinate_value, zeroCoordinate_value]
    simp
  have hterm :
      (ChainComplex.TensorCoefficient.regularIso R originalComplex).hom.f 0
        ((3 : R) ⊗ₜ[R] zeroCoordinate 1) = zeroCoordinate 3 := by
    change ((ChainComplex.TensorCoefficient.regularIso R originalComplex).hom.f 0).hom _ = _
    rw [ChainComplex.TensorCoefficient.regularIso_tmul]
    exact hc
  simpa only [hterm] using hv

private def negativeComplexIso : originalComplex ≅ originalComplex where
  hom := -𝟙 originalComplex
  inv := -𝟙 originalComplex
  hom_inv_id := by simp
  inv_hom_id := by simp

example :
    binaryValue
      ((((ChainComplex.TensorCoefficient.map R negativeComplexIso.hom).app binary).f 0).hom
        ((1 : ZMod 2) ⊗ₜ[R] zeroCoordinate 1)) = 1 := by
  rw [ChainComplex.TensorCoefficient.map_chain_tmul]
  have hn : (negativeComplexIso.hom.f 0).hom (zeroCoordinate 1) = -zeroCoordinate 1 := by
    simp [negativeComplexIso, HomologicalComplex.neg_f_apply]
  rw [hn]
  simp only [binaryValue]
  decide

example :
    binaryValue
      ((((ChainComplex.TensorCoefficient.mapIso R negativeComplexIso).hom.app binary).f 0).hom
        ((1 : ZMod 2) ⊗ₜ[R] zeroCoordinate 1)) = 1 := by
  change binaryValue
    ((((ChainComplex.TensorCoefficient.map R negativeComplexIso.hom).app binary).f 0).hom _) = 1
  rw [ChainComplex.TensorCoefficient.map_chain_tmul]
  have hn : (negativeComplexIso.hom.f 0).hom (zeroCoordinate 1) = -zeroCoordinate 1 := by
    simp [negativeComplexIso, HomologicalComplex.neg_f_apply]
  rw [hn]
  simp only [binaryValue]
  decide

private def regularValue : regularComplex.X 0 →ₗ[R] R :=
  (TensorProduct.lid R R).toLinearMap.comp
    (TensorProduct.map (LinearMap.id : R →ₗ[R] R) zeroTermIso.hom.hom)

-- In ZMod 4 the nonidentity negation is observable as the distinct coefficient three.
example :
    regularValue
      ((((ChainComplex.TensorCoefficient.mapIso R negativeComplexIso).hom.app regular).f 0).hom
        ((1 : R) ⊗ₜ[R] zeroCoordinate 1)) = 3 := by
  change regularValue
    ((((ChainComplex.TensorCoefficient.map R negativeComplexIso.hom).app regular).f 0).hom _) = 3
  rw [ChainComplex.TensorCoefficient.map_chain_tmul]
  have hn : (negativeComplexIso.hom.f 0).hom (zeroCoordinate 1) = -zeroCoordinate 1 := by
    simp [negativeComplexIso, HomologicalComplex.neg_f_apply]
  rw [hn]
  simp only [regularValue]
  decide

example :
    (ChainComplex.TensorCoefficient.map R negativeComplexIso.hom).app regular ≫
        (ChainComplex.TensorCoefficient.functor R originalComplex).map quotient =
      (ChainComplex.TensorCoefficient.functor R originalComplex).map quotient ≫
        (ChainComplex.TensorCoefficient.map R negativeComplexIso.hom).app binary :=
  ((ChainComplex.TensorCoefficient.map R negativeComplexIso.hom).naturality quotient).symm

private def window : ComposableArrows (ModuleCat.{0} R) 5 :=
  ChainComplex.TensorCoefficient.sixTermSequence R originalComplex
    originalComplex_terms_flat sequence sequence_shortExact 0

example : window.Exact :=
  ChainComplex.TensorCoefficient.sixTermSequence_exact R originalComplex
    originalComplex_terms_flat sequence sequence_shortExact 0

example : window.map' 2 3 =
    ChainComplex.TensorCoefficient.connecting R originalComplex
      originalComplex_terms_flat sequence sequence_shortExact 0 := rfl

example : window.map' 2 3 ≠ 0 := by
  change ChainComplex.TensorCoefficient.connecting R originalComplex
    originalComplex_terms_flat sequence sequence_shortExact 0 ≠ 0
  exact connecting_ne_zero

private def sequenceNegation : sequence ⟶ sequence := -𝟙 sequence

example : window ⟶ window :=
  ChainComplex.TensorCoefficient.sixTermSequenceMap R originalComplex originalComplex_terms_flat
    sequenceNegation sequence_shortExact sequence_shortExact 0

example :
    ChainComplex.TensorCoefficient.connecting R originalComplex
        originalComplex_terms_flat sequence sequence_shortExact 0 ≫
        (ChainComplex.TensorCoefficient.homologyFunctor R originalComplex 0).map
          sequenceNegation.τ₁ =
      (ChainComplex.TensorCoefficient.homologyFunctor R originalComplex 1).map
        sequenceNegation.τ₃ ≫
        ChainComplex.TensorCoefficient.connecting R originalComplex
          originalComplex_terms_flat sequence sequence_shortExact 0 :=
  ChainComplex.TensorCoefficient.connecting_naturality_sequence R originalComplex
    originalComplex_terms_flat sequenceNegation sequence_shortExact sequence_shortExact 0

example :
    (ChainComplex.TensorCoefficient.mapShortComplex R originalComplex
      negativeComplexIso.hom sequence).τ₁ =
      (ChainComplex.TensorCoefficient.map R negativeComplexIso.hom).app binary := rfl

example :
    ChainComplex.TensorCoefficient.connecting R originalComplex
        originalComplex_terms_flat sequence sequence_shortExact 0 ≫
        HomologicalComplex.homologyMap
          ((ChainComplex.TensorCoefficient.map R negativeComplexIso.hom).app binary) 0 =
      HomologicalComplex.homologyMap
          ((ChainComplex.TensorCoefficient.map R negativeComplexIso.hom).app binary) 1 ≫
        ChainComplex.TensorCoefficient.connecting R originalComplex
          originalComplex_terms_flat sequence sequence_shortExact 0 :=
  ChainComplex.TensorCoefficient.connecting_naturality_complex R originalComplex
    negativeComplexIso.hom originalComplex_terms_flat originalComplex_terms_flat
    sequence sequence_shortExact 0

example : Epi ((ChainComplex.TensorCoefficient.homologyFunctor R originalComplex 0).map quotient) :=
  ChainComplex.TensorCoefficient.homologyMap_zero_epi R originalComplex
    sequence sequence_shortExact

end TensorCoefficientAPIClients
