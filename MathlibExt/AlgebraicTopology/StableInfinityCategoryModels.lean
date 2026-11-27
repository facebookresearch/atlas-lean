/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.StableInfinityFiniteDiagrams
public import MathlibExt.AlgebraicTopology.FullEnhancedSubcategory
public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Algebra.Group.WithOne.Defs

/-!
# Small stable infinity categories and their exact functors

A stable category is an actual quasicategory with a zero object,
all native finite pullback/pushout cones, and the bicartesian-square
condition. These conditions use the actual functor and mapping objects.
The domain is all small stable infinity categories, with no field,
DG-linearity or scheme restriction.

Coherent idempotents are diagrams on the two-element idempotent monoid.
Splitting extends that diagram to its actual Karoubi envelope, the
walking retract. Exact functors preserve zero objects and the specified
native pushout squares. Their full functor infinity category retains
all natural transformations before any maximal core is taken.

References: Lurie, Higher Algebra, Section 1.1;
Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Sections 2.2 and 7.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.StableInfinityCategoryModels

open _root_.CategoryTheory _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open StableInfinityMappingSpaces StableInfinityFiniteDiagrams
open QuasicategoricalModels
open scoped Simplicial

universe u

/-- The entire small stable infinity category, with actual finite universal diagrams. -/
structure StableInfinityCategory where
  toSSet : SSet.{u}
  quasicategory : SSet.Quasicategory toSSet
  zero : toSSet _⦋0⦌
  zero_universal : IsZeroObject toSSet zero
  pullbacks : ∀ d : indexNerve CospanCorner ⟶ toSSet,
    ∃ c : (leftCones toSSet d) _⦋0⦌, IsTerminalObject (leftCones toSSet d) c
  pushouts : ∀ d : indexNerve SpanCorner ⟶ toSSet,
    ∃ c : (rightCones toSSet d) _⦋0⦌, IsInitialObject (rightCones toSSet d) c
  bicartesian : ∀ d : indexNerve SquareCorner ⟶ toSSet,
    IsPullbackSquare d ↔ IsPushoutSquare d

attribute [instance] StableInfinityCategory.quasicategory

/-- The actual walking coherent idempotent: the nonunit element of WithOne(PUnit). -/
abbrev IdempotentIndex := SingleObj (WithOne PUnit.{1})

/-- The actual walking retract is the native idempotent completion of that index. -/
abbrev RetractIndex := Idempotents.Karoubi IdempotentIndex

/-- Idempotents split when each entire coherent diagram extends to its walking retract. -/
def IsIdempotentComplete (C : StableInfinityCategory) : Prop :=
  ∀ d : indexNerve IdempotentIndex ⟶ C.toSSet,
    ∃ r : indexNerve RetractIndex ⟶ C.toSSet,
      indexMap (Idempotents.toKaroubi IdempotentIndex) ≫ r = d

/-- The source BGT domain consists of these actual idempotent-complete stable categories. -/
structure PerfectInfinityCategory extends StableInfinityCategory where
  idempotentComplete : IsIdempotentComplete toStableInfinityCategory

/-- Exactness is preservation of actual zero objects and actual finite cocartesian squares. -/
def IsExact (C D : StableInfinityCategory) (f : C.toSSet ⟶ D.toSSet) : Prop :=
  (∀ x : C.toSSet _⦋0⦌, IsZeroObject C.toSSet x →
    IsZeroObject D.toSSet (f.app (op ⦋0⦌) x)) ∧
  ∀ d : indexNerve SquareCorner ⟶ C.toSSet, IsPushoutSquare d → IsPushoutSquare (d ≫ f)

/-- The exact functor is the original simplicial map with its finite-colimit preservation proof. -/
structure ExactFunctor (C D : StableInfinityCategory) where
  map : C.toSSet ⟶ D.toSSet
  exact : IsExact C D map

/-- The literal identity map is exact. -/
theorem identity_isExact (C : StableInfinityCategory) : IsExact C C (𝟙 C.toSSet) := by
  constructor
  · intro x hx
    exact hx
  · intro d hd
    simpa only [Category.comp_id] using hd

/-- Actual simplicial composition preserves the source's finite-colimit tests. -/
theorem composition_isExact {C D E : StableInfinityCategory}
    {f : C.toSSet ⟶ D.toSSet} {g : D.toSSet ⟶ E.toSSet}
    (hf : IsExact C D f) (hg : IsExact D E g) : IsExact C E (f ≫ g) := by
  constructor
  · intro x hx
    exact hg.1 _ (hf.1 x hx)
  · intro d hd
    simpa only [Category.assoc] using hg.2 (d ≫ f) (hf.2 d hd)

/-- The exact identity functor uses that same actual map. -/
def ExactFunctor.id (C : StableInfinityCategory) : ExactFunctor C C :=
  ⟨𝟙 C.toSSet, identity_isExact C⟩

/-- Exact functors compose by the actual native simplicial composition. -/
def ExactFunctor.comp {C D E : StableInfinityCategory}
    (f : ExactFunctor C D) (g : ExactFunctor D E) : ExactFunctor C E :=
  ⟨f.map ≫ g.map, composition_isExact f.exact g.exact⟩

/-- The vertex predicate is evaluated on the actual native simplicial Hom comparison. -/
def IsExactVertex (C D : StableInfinityCategory)
    (a : (mapping C.toSSet D.toSSet) _⦋0⦌) : Prop :=
  IsExact C D ((mappingZero C.toSSet D.toSSet).symm a)

/-- The full exact functor infinity category, with all natural transformations. -/
def exactFunctorCategory (C D : StableInfinityCategory) : SSet.{u} :=
  ((mapping C.toSSet D.toSSet).fullEnhancedSubcategory (IsExactVertex C D)).toSSet

/-- The maximal core is taken only after the full exact functor category has been formed. -/
def exactFunctorSpace (C D : StableInfinityCategory) : SSet.{u} :=
  core (exactFunctorCategory C D)

end MathlibExt.AlgebraicTopology.StableInfinityCategoryModels
