/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKScalarClosure
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenOrdinaryHoHom

/-!
# Scalar suspension and the original Omega tests

The actual tensor/cotensor adjunction is Quillen for each cofibrant scalar.
Its ordinary level-homotopy Hom equivalence transports the original Omega
precomposition tests for cofibrant sources. Applying the original I replacement
functor to the whole arrow supplies the arbitrary-source version.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] Native.modelCategory

/-- The actual scalar tensor of an original test equivalence is a test equivalence
when its source objects are cofibrant. -/
theorem tensorMap_omegaTests_of_cofibrant (M : PointedCGWH.{u, v}) [IsCofibrant M]
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) (hf : omegaTests s f) :
    omegaTests s ((EnrichedFunctorCat.tensorLeft M).map f) := by
  intro E hE
  let _ : IsFibrant E := Native.allObjectsFibrant E
  let _ : (ScalarLeibniz.adjunction (A := I) M).IsQuillenAdjunction :=
    ScalarCompatibility.scalar_isQuillen M
  let eX := QuillenOrdinaryHoHom.homEquiv (ScalarLeibniz.adjunction M) X E
  let eY := QuillenOrdinaryHoHom.homEquiv (ScalarLeibniz.adjunction M) Y E
  have h := hf ((cotensor M).obj E) (cotensor_isOmega (B := B) s M E hE)
  constructor
  · intro g₁ g₂ hg
    apply eY.injective
    apply h.1
    have h₁ := QuillenOrdinaryHoHom.homEquiv_naturality_left
      (ScalarLeibniz.adjunction M) E f g₁
    have h₂ := QuillenOrdinaryHoHom.homEquiv_naturality_left
      (ScalarLeibniz.adjunction M) E f g₂
    exact h₁.symm.trans ((congrArg eX hg).trans h₂)
  · intro g
    obtain ⟨a, ha⟩ := h.2 (eX g)
    refine ⟨eY.symm a, ?_⟩
    apply eX.injective
    change QuillenOrdinaryHoHom.homEquiv (ScalarLeibniz.adjunction M) X E
      ((toHomotopyCategory _).map ((EnrichedFunctorCat.tensorLeft M).map f) ≫ eY.symm a) = _
    rw [QuillenOrdinaryHoHom.homEquiv_naturality_left]
    change (toHomotopyCategory _).map f ≫ eY (eY.symm a) = _
    rw [Equiv.apply_symm_apply]
    exact ha

/-- Apply the original Q functor to the entire caller arrow before scalar suspension. -/
theorem tensorQMap_omegaTests (M : PointedCGWH.{u, v}) [IsCofibrant M]
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hf : omegaTests s f) :
    omegaTests s ((EnrichedFunctorCat.tensorLeft M).map
      ((Replacement.cofibrantReplacement (B := B)).map f)) := by
  let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) X
  let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) Y
  exact tensorMap_omegaTests_of_cofibrant (B := B) s M
    ((Replacement.cofibrantReplacement (B := B)).map f)
    ((cofibrantReplacement_map_localTest_iff (B := B) s f).mpr hf)

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
