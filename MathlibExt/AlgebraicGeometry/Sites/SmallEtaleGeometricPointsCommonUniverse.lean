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

/-! # Original geometric points and covers in the common universe

The original common-point declarations and their cover-detection proof are
extracted unchanged from the inverse-image scouts. The affine common-universe size construction
is derived inline from the stock small model and universe enlargement. This provider needs
only coefficients and stock site/point APIs; it has no inverse-image,
inverse-exactness, or presheaf Kan-extension dependency.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The same geometric neighborhoods after lifting their fiber elements.
This uses stock equivalences of structured arrows and fully faithful postcomposition. -/
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

/-- The original geometric-neighborhood initial model enlarges to the common universe. -/
theorem smallEtaleGeometricNeighborhoodsInitiallySmallCommon {X : Scheme.{u}}
    (x : Spec (.of Ω) ⟶ X) :
    InitiallySmall.{max u w} (Scheme.pointSmallEtale x).fiber.Elements := by
  let C := (Scheme.pointSmallEtale x).fiber.Elements
  let e : InitialModel.{u} C ≌ AsSmall.{w} (InitialModel.{u} C) := AsSmall.equiv
  let F := e.inverse ⋙ fromInitialModel.{u} C
  let : F.Initial := Functor.initial_comp _ _
  exact InitiallySmall.mk' F

/-- The prescribed original geometric point, with its fiber elements lifted
to the common universe and all point conditions derived internally. -/
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

/-- Actual common-universe sheafification for type-valued sheaves, using the
same original affine basis and its genuine sheaf restriction equivalence. -/
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

/-- The actual canonical residue-field geometric morphism at each original point. -/
abbrev smallEtaleCanonicalGeometricMorphism (X : Scheme.{u}) (x : X) :
    Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
  (SpecToEquivOfField (SeparableClosure (X.residueField x)) X).symm
    ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩

/-- The original small-universe canonical geometric point family. -/
abbrev smallEtaleCanonicalGeometricPoints (X : Scheme.{u}) :
    ObjectProperty X.smallEtaleTopology.Point.{u} :=
  ObjectProperty.ofObj
    (fun x : X => Scheme.pointSmallEtale (smallEtaleCanonicalGeometricMorphism X x))

/-- The same actual geometric morphisms define the common-universe point family. -/
abbrev smallEtaleCanonicalGeometricPointsCommon (X : Scheme.{u}) :
    ObjectProperty X.smallEtaleTopology.Point.{max u w} :=
  ObjectProperty.ofObj
    (fun x : X => smallEtaleGeometricPointCommon.{u, w} (smallEtaleCanonicalGeometricMorphism X x))

/-- Stock conservativity of the original actual small-site geometric points. -/
theorem smallEtaleCanonicalGeometricPoints_conservative (X : Scheme.{u}) :
    (smallEtaleCanonicalGeometricPoints X).IsConservativeFamilyOfPoints := by
  exact Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X

/-- The same original geometric family is conservative after its fiber elements
are lifted to the common universe; cover detection is inherited from the
original family rather than supplied as a certificate. -/
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

/-- An actual sieve is covering if its arrows lift every element of each
original common-universe geometric fiber. This is the cover criterion used
to construct the preceding conservative family, with no common-universe
local-bijectivity certificate. -/
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
