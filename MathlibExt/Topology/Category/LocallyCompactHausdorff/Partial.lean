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

public import MathlibExt.Topology.Category.PointedTopCat
public import MathlibExt.Topology.Compactification.OnePoint.PartialProperMap
public import Mathlib.CategoryTheory.Category.Basic

/-!
# Locally compact Hausdorff spaces with their original partial morphisms

Objects retain their original locally compact Hausdorff carrier and topology.
Morphisms are precisely continuous maps of the original one-point
compactifications preserving infinity. The category laws are the original
continuous extension laws. Each morphism has its actual open proper
restriction, with the same finite values and infinity outside that domain.
No arbitrary domain, inverse or map model is stored as an input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open CategoryTheory Topology
open scoped OnePoint

universe u

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications.

locally compact Hausdorff objects for the pointed-compactification morphism convention. -/
structure LocallyCompactHausPartialCat : Type (u + 1) where
  /-- The original space carrier. -/
  carrier : Type u
  /-- Its original topology. -/
  [topologicalSpace : TopologicalSpace carrier]
  /-- Its original Hausdorff property. -/
  [t2Space : T2Space carrier]
  /-- Its original local compactness. -/
  [locallyCompactSpace : LocallyCompactSpace carrier]

attribute [instance] LocallyCompactHausPartialCat.topologicalSpace
  LocallyCompactHausPartialCat.t2Space LocallyCompactHausPartialCat.locallyCompactSpace

namespace LocallyCompactHausPartialCat

instance instCoeSort : CoeSort LocallyCompactHausPartialCat.{u} (Type u) := ⟨carrier⟩

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications.

Bundle the existing topology and locally compact Hausdorff properties. -/
abbrev of (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] :
    LocallyCompactHausPartialCat.{u} := ⟨X⟩

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications.

The locally compact object pointed at its one-point infinity, using the canonical owner. -/
def toPointedTopCat (X : LocallyCompactHausPartialCat.{u}) : PointedTopCat.{u} :=
  PointedTopCat.onePointPointed X

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications.

Hom, identity, composition and laws are inherited from the canonical pointed category. -/
instance category : Category.{u} LocallyCompactHausPartialCat.{u} :=
  let canonical : Category.{u} PointedTopCat.{u} := inferInstance
  { Hom := fun X Y => canonical.Hom (toPointedTopCat X) (toPointedTopCat Y)
    id := fun X => canonical.id (toPointedTopCat X)
    comp := fun f g => canonical.comp f g
    id_comp := by intro X Y f; exact canonical.id_comp f
    comp_id := by intro X Y f; exact canonical.comp_id f
    assoc := by intro X Y Z W f g h; exact canonical.assoc f g h }

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications.

Forget only the locally compact object fields into canonical pointed topological spaces. -/
def pointedFunctor : LocallyCompactHausPartialCat.{u} ⥤ PointedTopCat.{u} where
  obj := toPointedTopCat
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications.

The canonical pointed-morphism Hom has exactly the continuous extension and infinity law. -/
def toPointedMap {X Y : LocallyCompactHausPartialCat.{u}} (f : X ⟶ Y) : PointedOnePointMap X Y where
  extension := f.right.hom
  map_infty := by
    exact PointedTopCat.map_basepoint f

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications.

The pointed extension is used as the canonical category morphism, with no model choice. -/
def ofPointedMap {X Y : LocallyCompactHausPartialCat.{u}} (f : PointedOnePointMap X Y) : X ⟶ Y :=
  Under.homMk (TopCat.ofHom f.extension) (by
    apply ConcreteCategory.hom_ext
    intro p
    cases p
    exact f.map_infty)

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications.

Roundtrip to the independent-universe pointed-map carrier preserves every extension field. -/
theorem toPointedMap_ofPointedMap {X Y : LocallyCompactHausPartialCat.{u}} (f : PointedOnePointMap X Y) :
    toPointedMap (ofPointedMap f) = f := by
  apply PointedOnePointMap.ext
  rfl

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications.

Roundtrip to canonical pointed morphisms preserves the full Hom value. -/
theorem ofPointedMap_toPointedMap {X Y : LocallyCompactHausPartialCat.{u}} (f : X ⟶ Y) :
    ofPointedMap (toPointedMap f) = f := by
  apply Under.UnderMorphism.ext
  rfl

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications. The subset `U ⊆ X` is open and `g
: U → Y` is a proper continuous map.

Construct the category morphism from a proper map on an open subset. -/
def ofOpenProperMap {X Y : LocallyCompactHausPartialCat.{u}}
    (U : Set X) (hU : IsOpen U) (g : C(U, Y)) (hg : IsProperMap g) : X ⟶ Y :=
  ofPointedMap (PointedOnePointMap.ofOpenProperMap U hU g hg)

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications. The subset `U ⊆ X` is open and `g
: U → Y` is a proper continuous map.

The pointed adapter retains the open-domain extension. -/
theorem toPointedMap_ofOpenProperMap {X Y : LocallyCompactHausPartialCat.{u}}
    (U : Set X) (hU : IsOpen U) (g : C(U, Y)) (hg : IsProperMap g) :
    toPointedMap (ofOpenProperMap U hU g hg) =
      PointedOnePointMap.ofOpenProperMap U hU g hg :=
  toPointedMap_ofPointedMap _

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications. The subset `U ⊆ X` is open and `g
: U → Y` is a proper continuous map.

Proper open-domain maps have unique category morphisms with the same finite values. -/
theorem existsUnique_ofOpenProperMap {X Y : LocallyCompactHausPartialCat.{u}}
    (U : Set X) (hU : IsOpen U) (g : C(U, Y)) (hg : IsProperMap g) :
    ∃! f : X ⟶ Y, (toPointedMap f).domain = U ∧
      ∀ x : U, (g x : OnePoint Y) = (toPointedMap f).extension (x : X) := by
  refine ⟨ofOpenProperMap U hU g hg, ?_, ?_⟩
  · dsimp only
    rw [toPointedMap_ofOpenProperMap]
    refine ⟨PointedOnePointMap.domain_ofOpenProperMap U hU g hg, ?_⟩
    intro x
    exact (PointedOnePointMap.ofOpenProperMap_extension_coe U hU g hg x).symm
  · intro f hf
    have h := PointedOnePointMap.ofOpenProperMap_unique U hU g hg (toPointedMap f) hf.1 hf.2
    have h' := congrArg ofPointedMap h
    simpa only [ofPointedMap_toPointedMap, ofOpenProperMap] using h'

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications.

The canonical identity morphism is the pointed identity extension. -/
theorem toPointedMap_id (X : LocallyCompactHausPartialCat.{u}) :
    toPointedMap (𝟙 X) = PointedOnePointMap.id X := by
  apply PointedOnePointMap.ext
  rfl

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications.

Canonical pointed composition is the exact continuous pointed-map composition. -/
theorem toPointedMap_comp {X Y Z : LocallyCompactHausPartialCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    toPointedMap (f ≫ g) = (toPointedMap g).comp (toPointedMap f) := by
  apply PointedOnePointMap.ext
  rfl

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications.

The pointed adapter preserves the exact finite-value domain. -/
theorem toPointedMap_domain {X Y : LocallyCompactHausPartialCat.{u}} (f : X ⟶ Y) :
    (toPointedMap f).domain = ((↑) : X → OnePoint X) ⁻¹'
      (f.right.hom ⁻¹' ({∞} : Set (OnePoint Y))ᶜ) := rfl

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications.

The exact continuous extension of a canonical category morphism. -/
abbrev extension {X Y : LocallyCompactHausPartialCat.{u}} (f : X ⟶ Y) :
    C(OnePoint X, OnePoint Y) := (toPointedMap f).extension

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications.

Every category morphism preserves the same canonical infinity. -/
theorem extension_infty {X Y : LocallyCompactHausPartialCat.{u}} (f : X ⟶ Y) :
    extension (X := X) (Y := Y) f ∞ = ∞ := (toPointedMap f).map_infty

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications.

The finite-value domain of the canonical category morphism. -/
abbrev finiteDomain {X Y : LocallyCompactHausPartialCat.{u}} (f : X ⟶ Y) : Set X :=
  (toPointedMap f).domain

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications.

The same finite-value domain, exposed for source compatibility. -/
abbrev domain {X Y : LocallyCompactHausPartialCat.{u}} (f : X ⟶ Y) : Set X :=
  finiteDomain (X := X) (Y := Y) f

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications.

This same finite-value domain is open. -/
theorem finiteDomain_isOpen {X Y : LocallyCompactHausPartialCat.{u}} (f : X ⟶ Y) :
    IsOpen (domain (X := X) (Y := Y) f) := (toPointedMap f).domain_isOpen

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications.

The proper finite restriction, through the unchanged independent pointed-map factory. -/
abbrev finiteRestriction {X Y : LocallyCompactHausPartialCat.{u}} (f : X ⟶ Y) :
    C(domain (X := X) (Y := Y) f, Y) := (toPointedMap f).partialMap

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications.

The finite restriction, exposed for existing source value contracts. -/
abbrev partialMap {X Y : LocallyCompactHausPartialCat.{u}} (f : X ⟶ Y) :
    C(domain (X := X) (Y := Y) f, Y) :=
  finiteRestriction (X := X) (Y := Y) f

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications.

The finite restriction is proper on its open domain. -/
theorem finiteRestriction_isProperMap {X Y : LocallyCompactHausPartialCat.{u}} (f : X ⟶ Y) :
    IsProperMap (partialMap (X := X) (Y := Y) f) := (toPointedMap f).partialMap_isProperMap

/-- The objects are locally compact Hausdorff spaces, and morphisms are continuous
infinity-preserving maps of their one-point compactifications.

The adapter retains every finite value of the canonical pointed extension. -/
theorem finiteRestriction_coe {X Y : LocallyCompactHausPartialCat.{u}} (f : X ⟶ Y)
    (x : domain (X := X) (Y := Y) f) :
    (finiteRestriction (X := X) (Y := Y) f x : OnePoint Y) =
      extension (X := X) (Y := Y) f (x : X) := (toPointedMap f).partialMap_coe x

end LocallyCompactHausPartialCat

end
