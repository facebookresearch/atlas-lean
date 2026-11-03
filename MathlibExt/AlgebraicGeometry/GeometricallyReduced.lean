/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_GeometricallyReduced_of_isReduced_of_perfectField.lean` and
`P2M/Sol/S_AlgebraicGeometry_GeometricallyReduced_of_isReduced_of_perfectField.lean`
(fermats-last-theorem):
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.
-/

module

public import MathlibExt.Algebra.Algebra.TensorProductReduced
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Geometrically reduced schemes over perfect fields

A reduced scheme over a perfect field is
geometrically reduced: the statement is closed under isomorphism, so it
reduces to affine schemes, where it is reducedness of tensor products over
perfect fields.
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace GeometricallyReducedAux

private scoped instance isReduced_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (IsReduced : ObjectProperty Scheme.{u}) where
  of_iso e _ := isReduced_of_isOpenImmersion e.inv

private lemma isReduced_pullback_Spec {k : Type u} [Field k] [PerfectField k]
    {R : CommRingCat.{u}} (g : Spec R ⟶ Spec (CommRingCat.of k)) (hred : IsReduced (Spec R))
    (K : Type u) [Field K] [Algebra k K] :
    IsReduced (pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  algebraize [φ.hom]
  have hred' : _root_.IsReduced R := (affine_isReduced_iff R).mp hred
  have hKR : _root_.IsReduced (K ⊗[k] R) :=
    Algebra.isReduced_tensorProduct_of_perfectField k R K
  have hRK : _root_.IsReduced (R ⊗[k] K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm k R K).toRingHom
      (Algebra.TensorProduct.comm k R K).injective
  have hspec : IsReduced (Spec (CommRingCat.of (R ⊗[k] K))) :=
    (affine_isReduced_iff _).mpr hRK
  let e : pullback (Spec.map φ) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≅
      Spec (CommRingCat.of (R ⊗[k] K)) :=
    pullbackSpecIso k R K
  exact isReduced_of_isOpenImmersion e.hom

end GeometricallyReducedAux

/-- A reduced scheme over a perfect field is
geometrically reduced. -/
theorem AlgebraicGeometry.GeometricallyReduced.of_isReduced_of_perfectField
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsReduced X] :
    AlgebraicGeometry.GeometricallyReduced f := by
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms (P := IsReduced)).mpr ?_⟩
  intro K _ _
  apply +allowSynthFailures @IsReduced.of_openCover
    (𝒰 := Scheme.Pullback.openCoverOfLeft X.affineCover f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  intro i
  change IsReduced (pullback (X.affineCover.f i ≫ f)
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  have : IsOpenImmersion (X.affineCover.f i) := X.affineCover.map_prop i
  have hred : IsReduced (X.affineCover.X i) := isReduced_of_isOpenImmersion (X.affineCover.f i)
  exact GeometricallyReducedAux.isReduced_pullback_Spec (X.affineCover.f i ≫ f) hred K
