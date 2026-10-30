/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_isReduced_of_smooth_over_field.lean` and
`P2M/Sol/S_AlgebraicGeometry_isReduced_of_smooth_over_field.lean`
(fermats-last-theorem):
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Flat

/-!
# Smooth schemes over a field are reduced

Étale algebras over a field are reduced (formal unramifiedness), hence so
are standard smooth algebras over a domain (étale over a polynomial ring,
then base-change to the fraction field), hence so are smooth algebras over
a domain (locally standard smooth), hence so are schemes smooth over a
field (check on an affine cover).
-/

@[expose] public section

open TensorProduct

universe u

namespace IsReducedOfSmoothFieldAux

private theorem etale_isReduced (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [Algebra.Etale K A] : IsReduced A := by
  have : Algebra.FormallyUnramified K A := inferInstance
  have : Algebra.EssFiniteType K A := inferInstance
  exact Algebra.FormallyUnramified.isReduced_of_field K A

private theorem isStandardSmooth_isReduced_of_isDomain
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R] {φ : R →+* A}
    (hφ : φ.IsStandardSmooth) : IsReduced A := by
  obtain ⟨n, g, -, hg⟩ := hφ.exists_etale_mvPolynomial
  let _ : Algebra (MvPolynomial (Fin n) R) A := g.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin n) R) A := hg.toAlgebra
  have : IsReduced
      (FractionRing (MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] A) :=
    IsReducedOfSmoothFieldAux.etale_isReduced (FractionRing (MvPolynomial (Fin n) R)) _
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight :
      A →ₐ[MvPolynomial (Fin n) R]
        FractionRing (MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] A)
    (Algebra.TensorProduct.includeRight_injective
      (IsFractionRing.injective (MvPolynomial (Fin n) R)
        (FractionRing (MvPolynomial (Fin n) R))))

private theorem smooth_isReduced_of_isDomain
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R] {φ : R →+* A}
    (hφ : φ.Smooth) : IsReduced A := by
  rw [RingHom.smooth_iff_locally_isStandardSmooth] at hφ
  obtain ⟨s, hs, H⟩ := hφ
  constructor
  intro x hx
  apply Localization.algebraMap_injective_of_span_eq_top s hs
  rw [map_zero]
  funext a
  have : IsReduced (Localization.Away a.1) :=
    IsReducedOfSmoothFieldAux.isStandardSmooth_isReduced_of_isDomain (H a.1 a.2)
  simpa using IsReduced.eq_zero _ (hx.map (algebraMap A (Localization.Away a.1)))

end IsReducedOfSmoothFieldAux

open AlgebraicGeometry CategoryTheory

/-- A scheme smooth over a field is reduced. -/
theorem AlgebraicGeometry.isReduced_of_smooth_over_field {k : Type u} [Field k]
    {Z : Scheme.{u}} {g : Z ⟶ Spec (.of k)} (hg : Smooth g) : IsReduced Z := by
  have := hg
  have : ∀ i, IsReduced (Z.affineCover.X i) := by
    intro i
    have : IsDomain Γ(Spec (CommRingCat.of k), ⊤) :=
      Function.Injective.isDomain _
        (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.injective
    have : _root_.IsReduced ↑Γ(Z.affineCover.X i, ⊤) :=
      IsReducedOfSmoothFieldAux.smooth_isReduced_of_isDomain
        ((HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp
          (inferInstance : Smooth (Z.affineCover.f i ≫ g)))
    exact isReduced_of_isAffine_isReduced _
  exact IsReduced.of_openCover _ Z.affineCover
