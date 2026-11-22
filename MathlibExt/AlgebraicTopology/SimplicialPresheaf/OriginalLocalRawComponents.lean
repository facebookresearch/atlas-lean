/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalSmithModel
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InjectiveMappingComponents
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InjectiveDerivedMappingComparison
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
import Mathlib.AlgebraicTopology.ModelCategory.Homotopy

/-!
# Components of raw local mapping spaces

For a working-small localizing family on a working-small, locally small site, the components
of the raw mapping space from an arbitrary simplicial presheaf to a local fibrant target
identify with morphisms in the localized homotopy category. The equivalence sends each map to
its localization and respects source composition and maps between local fibrant targets.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w i
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open CategoryTheory.MorphismProperty
open SimplicialPresheaf SimplicialPresheaf.InjectiveKan
namespace SimplicialPresheaf.OriginalLocalRawComponents
variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i} [Small.{u} I]

private def baseClasses (A Z : (SimplicialPresheaf.{u} D)) : Type _ :=
  letI : ModelCategory (SimplicialPresheaf.{u} D) := (data D).model
  LeftHomotopyClass A Z
private def localClasses (S : I → Arrow (SimplicialPresheaf.{u} D))
    (A Z : (SimplicialPresheaf.{u} D)) : Type _ :=
  letI : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
  LeftHomotopyClass A Z
private def baseRelation {A Z : (SimplicialPresheaf.{u} D)} (f g : A ⟶ Z) : Prop :=
  letI : ModelCategory (SimplicialPresheaf.{u} D) := (data D).model
  LeftHomotopyRel f g
private def localRelation (S : I → Arrow (SimplicialPresheaf.{u} D))
    {A Z : (SimplicialPresheaf.{u} D)} (f g : A ⟶ Z) : Prop :=
  letI : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
  LeftHomotopyRel f g

private def commonBaseCylinder (A : (SimplicialPresheaf.{u} D)) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := (data D).model
    Cylinder A := by
  let : ModelCategory (SimplicialPresheaf.{u} D) := (data D).model
  exact Cylinder.ofFactorizationData
    ((originalCofibrationFactorization D).factorizationData (codiag A))

private theorem commonBaseCylinder_good (A : (SimplicialPresheaf.{u} D)) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := (data D).model
    (commonBaseCylinder A).IsGood := by
  let : ModelCategory (SimplicialPresheaf.{u} D) := (data D).model
  change (Cylinder.ofFactorizationData
    ((originalCofibrationFactorization D).factorizationData (codiag A))).IsGood
  infer_instance

private def commonLocalCylinder (S : I → Arrow (SimplicialPresheaf.{u} D))
    (A : (SimplicialPresheaf.{u} D)) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
    Cylinder A := by
  let P : Precylinder A := by
    let : ModelCategory (SimplicialPresheaf.{u} D) := (data D).model
    exact (commonBaseCylinder A).toPrecylinder
  let q := originalLocalSmithData S
  letI : ModelCategory (SimplicialPresheaf.{u} D) := q.model
  refine { toPrecylinder := P
           weakEquivalence_π := ?_ }
  apply (weakEquivalence_iff _).mpr
  change q.model.categoryWithWeakEquivalences.weakEquivalences P.π
  rw [q.weakEquivalences_eq]
  apply weakEquivalences_le_originalLocalEquivalences S
  let : ModelCategory (SimplicialPresheaf.{u} D) := (data D).model
  exact (weakEquivalence_iff _).mp (commonBaseCylinder A).weakEquivalence_π

private theorem commonLocalCylinder_good (S : I → Arrow (SimplicialPresheaf.{u} D))
    (A : (SimplicialPresheaf.{u} D)) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
    (commonLocalCylinder S A).IsGood := by
  let P : Precylinder A := by
    let : ModelCategory (SimplicialPresheaf.{u} D) := (data D).model
    exact (commonBaseCylinder A).toPrecylinder
  have h : monomorphisms (SimplicialPresheaf.{u} D) P.i := by
    let : ModelCategory (SimplicialPresheaf.{u} D) := (data D).model
    let : (commonBaseCylinder A).IsGood := commonBaseCylinder_good A
    have hb := (cofibration_iff _).mp (inferInstance : Cofibration (commonBaseCylinder A).i)
    change (data D).model.categoryWithCofibrations.cofibrations P.i at hb
    rwa [(data D).cofibrations_eq] at hb
  let q := originalLocalSmithData S
  let : ModelCategory (SimplicialPresheaf.{u} D) := q.model
  refine { cofibration_i := (cofibration_iff _).mpr ?_ }
  change q.model.categoryWithCofibrations.cofibrations P.i
  rw [q.cofibrations_eq]
  exact h

private theorem sameOriginalRelation (S : I →
    Arrow (SimplicialPresheaf.{u} D)) {A Z : (SimplicialPresheaf.{u} D)}
    (hZ : isOriginalLocalFibrant S Z) (f g : A ⟶ Z) :
    baseRelation f g ↔ localRelation S f g := by
  let q := originalLocalSmithData S
  constructor
  · intro h
    let : ModelCategory (SimplicialPresheaf.{u} D) := (data D).model
    let : IsCofibrant A := (data D).all_cofibrant A
    let : IsFibrant Z := hZ.1
    let : (commonBaseCylinder A).IsGood := commonBaseCylinder_good A
    have hb := (show LeftHomotopyRel f g from h).leftHomotopy (commonBaseCylinder A)
    let : ModelCategory (SimplicialPresheaf.{u} D) := q.model
    exact ⟨commonLocalCylinder S A, ⟨{ h := hb.h, h₀ := hb.h₀, h₁ := hb.h₁ }⟩⟩
  · intro h
    let : ModelCategory (SimplicialPresheaf.{u} D) := q.model
    let : IsCofibrant A := q.all_cofibrant A
    let : IsFibrant Z := (q.isFibrant_iff Z).mpr hZ
    let : (commonLocalCylinder S A).IsGood := commonLocalCylinder_good S A
    have hl := (show LeftHomotopyRel f g from h).leftHomotopy (commonLocalCylinder S A)
    let : ModelCategory (SimplicialPresheaf.{u} D) := (data D).model
    exact ⟨commonBaseCylinder A, ⟨{ h := hl.h, h₀ := hl.h₀, h₁ := hl.h₁ }⟩⟩

private def sameOriginalClassEquiv (S : I → Arrow (SimplicialPresheaf.{u} D))
    (A Z : (SimplicialPresheaf.{u} D))
    (hZ : isOriginalLocalFibrant S Z) : baseClasses A Z ≃ localClasses S A Z where
  toFun := Quot.map (fun f => f)
    (fun f g h => (sameOriginalRelation S hZ f g).mp h)
  invFun := Quot.map (fun f => f)
    (fun f g h => (sameOriginalRelation S hZ f g).mpr h)
  left_inv c := by
    let : ModelCategory (SimplicialPresheaf.{u} D) := (data D).model
    obtain ⟨f,rfl⟩ := LeftHomotopyClass.mk_surjective c
    rfl
  right_inv c := by
    let : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
    obtain ⟨f,rfl⟩ := LeftHomotopyClass.mk_surjective c
    rfl

/-- Actual raw components have the SAME internally selected original localized Ho interpretation. -/
def originalLocalRawMappingHoEquiv (S : I → Arrow (SimplicialPresheaf.{u} D))
    (A Z : (SimplicialPresheaf.{u} D)) (hZ : isOriginalLocalFibrant S Z) :
    let q := originalLocalSmithData S
    letI : ModelCategory (SimplicialPresheaf.{u} D) := q.model
    SSet.π₀ (innerHom A Z) ≃
      ((toHomotopyCategory (SimplicialPresheaf.{u} D)).obj A ⟶
          (toHomotopyCategory (SimplicialPresheaf.{u} D)).obj Z) := by
  let q := originalLocalSmithData S
  have e : SSet.π₀ (innerHom A Z) ≃ localClasses S A Z := by
    let : ModelCategory (SimplicialPresheaf.{u} D) := (data D).model
    exact (rawMappingComponentEquiv A Z hZ.1).trans (sameOriginalClassEquiv S A Z hZ)
  letI : ModelCategory (SimplicialPresheaf.{u} D) := q.model
  letI : IsCofibrant A := q.all_cofibrant A
  letI : IsFibrant Z := (q.isFibrant_iff Z).mpr hZ
  exact e.trans (leftHomotopyClassEquivOfIsLocalization
      (toHomotopyCategory (SimplicialPresheaf.{u} D)))

/-- Each actual original map point retains its actual localized Ho image. -/
theorem originalLocalRawMappingHoEquiv_mk
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (A Z : (SimplicialPresheaf.{u} D))
        (hZ : isOriginalLocalFibrant S Z) (f : A ⟶ Z) :
    let q := originalLocalSmithData S
    letI : ModelCategory (SimplicialPresheaf.{u} D) := q.model
    originalLocalRawMappingHoEquiv S A Z hZ (SSet.π₀.mk (innerHomHomEquiv A Z f)) =
      (toHomotopyCategory (SimplicialPresheaf.{u} D)).map f := by
  let q := originalLocalSmithData S
  have hc : (sameOriginalClassEquiv S A Z hZ)
      (rawMappingComponentEquiv A Z hZ.1 (SSet.π₀.mk (innerHomHomEquiv A Z f))) =
        (show localClasses S A Z from (by
          letI : ModelCategory (SimplicialPresheaf.{u} D) := q.model
          exact LeftHomotopyClass.mk f)) := by
    rw [rawMappingComponentEquiv_mk]
    rfl
  let : ModelCategory (SimplicialPresheaf.{u} D) := q.model
  let : IsCofibrant A := q.all_cofibrant A
  let : IsFibrant Z := (q.isFibrant_iff Z).mpr hZ
  change leftHomotopyClassEquivOfIsLocalization (toHomotopyCategory (SimplicialPresheaf.{u} D))
    ((sameOriginalClassEquiv S A Z hZ)
      (rawMappingComponentEquiv A Z hZ.1 (SSet.π₀.mk (innerHomHomEquiv A Z f)))) = _
  rw [hc, leftHomotopyClassEquivOfIsLocalization_mk]

/-- Every original source arrow has the actual localized Ho precomposition action. -/
theorem originalLocalRawMappingHoEquiv_source
    (S : I → Arrow (SimplicialPresheaf.{u} D)) {A B Z : (SimplicialPresheaf.{u} D)} (f : A ⟶ B)
    (hZ : isOriginalLocalFibrant S Z) (x : SSet.π₀ (innerHom B Z)) :
    let q := originalLocalSmithData S
    letI : ModelCategory (SimplicialPresheaf.{u} D) := q.model
    originalLocalRawMappingHoEquiv S A Z hZ (SSet.mapπ₀ (innerHomPre f Z) x) =
      (toHomotopyCategory (SimplicialPresheaf.{u} D)).map f ≫
          originalLocalRawMappingHoEquiv S B Z hZ x := by
  obtain ⟨x,rfl⟩ := x.mk_surjective
  obtain ⟨g,rfl⟩ := (innerHomHomEquiv B Z).surjective x
  rw [SSet.mapπ₀_mk, innerHomHomEquiv_precomp,
    originalLocalRawMappingHoEquiv_mk, originalLocalRawMappingHoEquiv_mk, Functor.map_comp]

/-- Every original local-fibrant target arrow retains the actual localized Ho action. -/
theorem originalLocalRawMappingHoEquiv_target
    (S : I → Arrow (SimplicialPresheaf.{u} D))
        (A : (SimplicialPresheaf.{u} D)) {Z Z' : (SimplicialPresheaf.{u} D)} (z : Z ⟶ Z')
    (hZ : isOriginalLocalFibrant S Z) (hZ' : isOriginalLocalFibrant S Z')
    (x : SSet.π₀ (innerHom A Z)) :
    let q := originalLocalSmithData S
    letI : ModelCategory (SimplicialPresheaf.{u} D) := q.model
    originalLocalRawMappingHoEquiv S A Z' hZ' (SSet.mapπ₀ (innerHomPost A z) x) =
      originalLocalRawMappingHoEquiv S A Z hZ x ≫
          (toHomotopyCategory (SimplicialPresheaf.{u} D)).map z := by
  obtain ⟨x,rfl⟩ := x.mk_surjective
  obtain ⟨f,rfl⟩ := (innerHomHomEquiv A Z).surjective x
  rw [SSet.mapπ₀_mk, innerHomHomEquiv_postcomp,
    originalLocalRawMappingHoEquiv_mk, originalLocalRawMappingHoEquiv_mk, Functor.map_comp]

end SimplicialPresheaf.OriginalLocalRawComponents
