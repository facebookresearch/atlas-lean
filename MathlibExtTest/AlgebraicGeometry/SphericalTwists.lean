/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.SphericalTwists

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.SphericalTwists

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open FourierMukai

attribute [local instance] HasDerivedCategory.standard

universe u

-- The kernel is the cone, in degree zero, of the canonical map `𝒪_{X×X} → Δ_* 𝒪_X`.
example (k : Type u) [Field k] (X : Over (Spec (.of k))) :
    kernel X = DerivedCategory.Q.obj (CochainComplex.mappingCone
      ((CochainComplex.singleFunctor (pullback X.hom X.hom).Modules 0).map
        (SheafOfModules.unitToPushforwardObjUnit (pullback.diagonal X.hom).toRingCatSheafHom))) :=
  rfl

-- Sphericality is only defined in positive degree.
example (k : Type u) [Field k] (X : Over (Spec (.of k))) [IsNoetherian X.left] :
    IsEmpty (SphericalStructure k X 0) :=
  ⟨fun S ↦ (lt_irrefl _ S.positive).elim⟩

end MathlibExt.AlgebraicGeometry.SphericalTwists
