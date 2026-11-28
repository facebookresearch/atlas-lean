/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.FlatGenericFibreDense
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Tests for `MathlibExt.AlgebraicGeometry.FlatGenericFibreDense`
-/

open CategoryTheory Limits AlgebraicGeometry

#check @AlgebraicGeometry.specMap_algebraMap_fractionRing_apply
#check @AlgebraicGeometry.range_specMap_algebraMap_fractionRing
#check @AlgebraicGeometry.isDominant_specMap_algebraMap_fractionRing
#check @AlgebraicGeometry.isSchemeTheoreticallyDominant_pullback_fst_fractionRing
#check @AlgebraicGeometry.dense_preimage_genericPoint_of_flat
#check @AlgebraicGeometry.isOpenImmersion_and_isSchemeTheoreticallyDominant_pullback_fst

/-- `Spec ℚ ⟶ Spec ℤ` is dominant. -/
example : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) := inferInstance

/-- The generic point of `Spec ℤ` is dense in `Spec ℤ` (the identity is flat). -/
example : Dense ((𝟙 (Spec (CommRingCat.of ℤ))) ⁻¹' {genericPoint (Spec (CommRingCat.of ℤ))}) :=
  dense_preimage_genericPoint_of_flat _

/-- For a flat scheme over `ℤ_[p]`, the generic fibre over `ℚ_[p]` is a scheme-theoretically
dense open subscheme. -/
example (p : ℕ) [Fact p.Prime] {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℤ_[p])) [Flat f] :
    IsOpenImmersion (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap ℤ_[p] ℚ_[p])))) ∧
      IsSchemeTheoreticallyDominant
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap ℤ_[p] ℚ_[p])))) :=
  isOpenImmersion_and_isSchemeTheoreticallyDominant_pullback_fst ℚ_[p] f

/-- Sections of a flat `ℤ`-scheme inject into sections of its generic fibre over `ℚ`, and the
projection from the generic fibre is dominant (from scheme-theoretic dominance). -/
example {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℤ)) [Flat f] (U : X.Opens) :
    Function.Injective
        ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))).app U) ∧
      IsDominant (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))) := by
  have := isSchemeTheoreticallyDominant_pullback_fst_fractionRing ℚ f
  exact ⟨Scheme.Hom.app_injective _ U, inferInstance⟩
