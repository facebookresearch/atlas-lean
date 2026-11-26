/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleCoefficientSections
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# Geometric points in a common coefficient universe

Let `X : Scheme.{u}` and let `Spec Ω → X` be a geometric point with `Ω : Type u` separably
closed. Lift its étale fiber sets to universe `λ = max u w`. The categories of elements before
and after lifting are equivalent, and the neighborhood category is initially small in `λ`,
giving a point of the small étale topology in that universe.

At each scheme point, the separable closure of its residue field gives a canonical geometric
morphism. These geometric points, both before and after lifting, form conservative families
and detect covering sieves. The common universe also supports sheafification of type-valued
presheaves.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- Lifting geometric fibers preserves their category of elements.

The elements category of a geometric-point fiber is equivalent to that of the fiber followed
by the universe lift from `u` to `max u w`. -/
def smallEtaleGeometricElementsLiftEquivalence {X : Scheme.{u}}
    (x : Spec (.of Ω) ⟶ X) :
    (Scheme.pointSmallEtale x).fiber.Elements ≌
      ((Scheme.pointSmallEtale x).fiber ⋙ uliftFunctor.{w, u}).Elements :=
  (Functor.Elements.structuredArrowEquivalence (Scheme.pointSmallEtale x).fiber).trans
    (((StructuredArrow.post PUnit.{u + 1} (Scheme.pointSmallEtale x).fiber
      uliftFunctor.{w, u}).asEquivalence).trans
      ((StructuredArrow.mapIso
        ((Equiv.ofUnique (ULift.{w} PUnit.{u + 1}) PUnit.{(max u w) + 1}).toIso)).trans
        (Functor.Elements.structuredArrowEquivalence
          ((Scheme.pointSmallEtale x).fiber ⋙ uliftFunctor.{w, u})).symm))

/-- Geometric neighborhoods are initially small in the common universe.

For a geometric point over a separably closed field in universe `u`, its étale fiber-elements
category is initially small in universe `max u w`. -/
theorem smallEtaleGeometricNeighborhoodsInitiallySmallCommon {X : Scheme.{u}}
    (x : Spec (.of Ω) ⟶ X) :
    InitiallySmall.{max u w} (Scheme.pointSmallEtale x).fiber.Elements := by
  let C := (Scheme.pointSmallEtale x).fiber.Elements
  let e : InitialModel.{u} C ≌ AsSmall.{w} (InitialModel.{u} C) := AsSmall.equiv
  let F := e.inverse ⋙ fromInitialModel.{u} C
  let : F.Initial := Functor.initial_comp _ _
  exact InitiallySmall.mk' F

/-- Geometric point with lifted fiber values.

Lift the fiber sets of the small étale geometric point to universe `max u w`; their cofiltered
and initially small elements category defines the common-universe point. -/
def smallEtaleGeometricPointCommon {X : Scheme.{u}} (x : Spec (.of Ω) ⟶ X) :
    X.smallEtaleTopology.Point.{max u w} where
  fiber := (Scheme.pointSmallEtale x).fiber ⋙ uliftFunctor.{w, u}
  isCofiltered := IsCofiltered.of_equivalence (smallEtaleGeometricElementsLiftEquivalence.{u, w} x)
  initiallySmall := by
    let : InitiallySmall.{max u w} (Scheme.pointSmallEtale x).fiber.Elements :=
      smallEtaleGeometricNeighborhoodsInitiallySmallCommon.{u, w} x
    exact initiallySmall_of_initial_of_initiallySmall
      (smallEtaleGeometricElementsLiftEquivalence.{u, w} x).functor
  jointly_surjective {U} R hR z := by
    obtain ⟨V, g, hg, y, hy⟩ := (Scheme.pointSmallEtale x).jointly_surjective R hR z.down
    refine ⟨V, g, hg, ULift.up y, ?_⟩
    exact congrArg ULift.up hy

/-- Common universe type valued presheaves admit sheafification.

The small étale topology of `X` has sheafification for presheaves valued in `Type (max u w)`. -/
instance smallEtaleHasSheafifyTypesCommon (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology (Type (max u w)) := by
  let : EssentiallySmall.{max u w} X.AffineEtale := by
    let e := equivSmallModel.{u} X.AffineEtale
    exact EssentiallySmall.mk'
      (e.trans
        (AsSmall.equiv : SmallModel.{u} X.AffineEtale ≌
          AsSmall.{w} (SmallModel.{u} X.AffineEtale)))
  let : HasSheafify (Scheme.AffineEtale.topology X) (Type (max u w)) :=
    hasSheafifyEssentiallySmallSite.{u, max u w, u + 1, (max u w) + 1, max u w} _ _
  let : ((Scheme.AffineEtale.Spec X).sheafPushforwardContinuous (Type (max u w))
      (Scheme.AffineEtale.topology X) X.smallEtaleTopology).IsEquivalence :=
    Functor.isEquivalence_of_isOneHypercoverDense.{u}
      (Scheme.AffineEtale.Spec X) (Scheme.AffineEtale.topology X)
      X.smallEtaleTopology (Type (max u w))
  exact Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (Scheme.AffineEtale.topology X) X.smallEtaleTopology (Scheme.AffineEtale.Spec X)

/-- Geometric morphism from the separable closure of a residue field.

For a scheme point `x`, use the residue-field inclusion into its separable closure to define
`Spec (SeparableClosure (κ(x))) → X`. -/
abbrev smallEtaleCanonicalGeometricMorphism (X : Scheme.{u}) (x : X) :
    Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
  (SpecToEquivOfField (SeparableClosure (X.residueField x)) X).symm
    ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩

/-- Family of residue field geometric points.

Take the small étale points associated to the canonical separable-closure morphism at each
point of `X`. -/
abbrev smallEtaleCanonicalGeometricPoints (X : Scheme.{u}) :
    ObjectProperty X.smallEtaleTopology.Point.{u} :=
  ObjectProperty.ofObj
    (fun x : X => Scheme.pointSmallEtale (smallEtaleCanonicalGeometricMorphism X x))

/-- Lifted family of residue field geometric points.

Take the common-universe lifts of the canonical residue-field geometric points, indexed by the
points of `X`. -/
abbrev smallEtaleCanonicalGeometricPointsCommon (X : Scheme.{u}) :
    ObjectProperty X.smallEtaleTopology.Point.{max u w} :=
  ObjectProperty.ofObj
    (fun x : X => smallEtaleGeometricPointCommon.{u, w} (smallEtaleCanonicalGeometricMorphism X x))

/-- Residue field geometric points form a conservative family.

The canonical geometric points obtained from separable closures of residue fields form a
conservative family of small étale points. -/
theorem smallEtaleCanonicalGeometricPoints_conservative (X : Scheme.{u}) :
    (smallEtaleCanonicalGeometricPoints X).IsConservativeFamilyOfPoints := by
  exact Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X

/-- Lifted residue field geometric points remain conservative.

The common-universe family of canonical geometric points is conservative. -/
theorem smallEtaleCanonicalGeometricPointsCommon_conservative (X : Scheme.{u}) :
    (smallEtaleCanonicalGeometricPointsCommon.{u, w} X).IsConservativeFamilyOfPoints := by
  apply ObjectProperty.IsConservativeFamilyOfPoints.mk'
  intro U R hR
  obtain ⟨ι, V, g, rfl⟩ := R.exists_eq_ofArrows
  apply (ObjectProperty.IsConservativeFamilyOfPoints.jointly_reflect_ofArrows_mem_of_small
    (smallEtaleCanonicalGeometricPoints_conservative X) g).mpr
  rintro ⟨Φ, hΦ⟩ z
  obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ Φ).mp hΦ
  subst Φ
  obtain ⟨T, q, hq, y, hy⟩ := hR
    ⟨smallEtaleGeometricPointCommon.{u, w} (smallEtaleCanonicalGeometricMorphism X x),
      ObjectProperty.ofObj.mk x⟩
    (ULift.up z)
  have hy' :
      (Scheme.pointSmallEtale (smallEtaleCanonicalGeometricMorphism X x)).fiber.map q y.down = z :=
    congrArg ULift.down hy
  obtain ⟨_, p, _, ⟨i⟩, rfl⟩ := hq
  refine ⟨i, (Scheme.pointSmallEtale (smallEtaleCanonicalGeometricMorphism X x)).fiber.map p y.down,
    ?_⟩
  simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using hy'

/-- Canonical geometric fibers detect covering sieves.

If every fiber element at every canonical common-universe point lifts through an arrow of a
sieve on an étale object, that sieve is covering in the small étale topology. -/
theorem smallEtaleCanonicalGeometricPointsCommon_cover {X : Scheme.{u}} {U : X.Etale}
    (R : Sieve U)
    (hR : ∀ (Φ : (smallEtaleCanonicalGeometricPointsCommon.{u, w} X).FullSubcategory)
      (z : Φ.obj.fiber.obj U),
      ∃ (V : X.Etale) (g : V ⟶ U) (_ : R g) (y : Φ.obj.fiber.obj V),
        Φ.obj.fiber.map g y = z) : R ∈ X.smallEtaleTopology U := by
  obtain ⟨ι, V, g, rfl⟩ := R.exists_eq_ofArrows
  apply (ObjectProperty.IsConservativeFamilyOfPoints.jointly_reflect_ofArrows_mem_of_small
    (smallEtaleCanonicalGeometricPoints_conservative X) g).mpr
  rintro ⟨Φ, hΦ⟩ z
  obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ Φ).mp hΦ
  subst Φ
  obtain ⟨T, q, hq, y, hy⟩ := hR
    ⟨smallEtaleGeometricPointCommon.{u, w} (smallEtaleCanonicalGeometricMorphism X x),
      ObjectProperty.ofObj.mk x⟩ (ULift.up z)
  have hy' :
      (Scheme.pointSmallEtale (smallEtaleCanonicalGeometricMorphism X x)).fiber.map q y.down = z :=
    congrArg ULift.down hy
  obtain ⟨_, p, _, ⟨i⟩, rfl⟩ := hq
  refine ⟨i, (Scheme.pointSmallEtale (smallEtaleCanonicalGeometricMorphism X x)).fiber.map p y.down,
    ?_⟩
  simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using hy'

end AlgebraicGeometry.Scheme.DerivedSections
