/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CategoricalEquivalences

/-!
# Categorical equivalences: formal calculus tests

These tests exercise the public API of `SSet.categoricalEquivalences`: the
defining membership criterion, the closure instances (identities,
isomorphisms, composition, two-out-of-three, retracts, and stability under
composition with isomorphisms), and universe polymorphism. They only use
formal consequences of the definition; no inner-anodyne or model-structure
input is involved.
-/

@[expose] public section

open CategoryTheory MonoidalClosed
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
namespace CategoricalEquivalencesTest

section Instances

example : SSet.categoricalEquivalences.{u}.ContainsIdentities := inferInstance
example : SSet.categoricalEquivalences.{u}.IsStableUnderComposition := inferInstance
example : SSet.categoricalEquivalences.{u}.IsMultiplicative := inferInstance
example : SSet.categoricalEquivalences.{u}.HasTwoOutOfThreeProperty := inferInstance
example : SSet.categoricalEquivalences.{u}.RespectsIso := inferInstance
example : SSet.categoricalEquivalences.{u}.IsStableUnderRetracts := inferInstance
example : SSet.categoricalEquivalences.{u}.HasOfPostcompProperty
    SSet.categoricalEquivalences.{u} := inferInstance
example : SSet.categoricalEquivalences.{u}.HasOfPrecompProperty
    SSet.categoricalEquivalences.{u} := inferInstance

-- The instances also exist at universe `0`.
example : SSet.categoricalEquivalences.{0}.HasTwoOutOfThreeProperty := inferInstance
example : SSet.categoricalEquivalences.{0}.IsStableUnderRetracts := inferInstance

end Instances

section MembershipCriterion

variable {X Y : SSet.{u}} (f : X ⟶ Y)

example : SSet.categoricalEquivalences f ↔
    ∀ (C : SSet.{u}), SSet.Quasicategory C →
      (SSet.hoFunctor.map ((pre f).app C)).toFunctor.IsEquivalence :=
  SSet.categoricalEquivalences.mem_iff f

end MembershipCriterion

section IdentitiesAndIsomorphisms

variable (X Y : SSet.{u})

example : SSet.categoricalEquivalences (𝟙 X) :=
  MorphismProperty.id_mem _ X

example : SSet.categoricalEquivalences (𝟙 (Δ[0] : SSet.{u})) :=
  MorphismProperty.id_mem _ _

example : SSet.categoricalEquivalences (𝟙 (Δ[1] : SSet.{u})) :=
  MorphismProperty.id_mem _ _

example (e : X ≅ Y) : SSet.categoricalEquivalences e.hom :=
  SSet.categoricalEquivalences.of_isIso e.hom

example (e : X ≅ Y) : SSet.categoricalEquivalences e.hom :=
  MorphismProperty.of_isIso _ e.hom

example : SSet.categoricalEquivalences (Iso.refl (Δ[1] : SSet.{u})).hom :=
  SSet.categoricalEquivalences.of_isIso _

example (f : X ⟶ Y) [IsIso f] : SSet.categoricalEquivalences f :=
  SSet.categoricalEquivalences.of_isIso f

end IdentitiesAndIsomorphisms

section CompositionAndTwoOutOfThree

variable {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}

example (hf : SSet.categoricalEquivalences f) (hg : SSet.categoricalEquivalences g) :
    SSet.categoricalEquivalences (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg

example (hg : SSet.categoricalEquivalences g)
    (hfg : SSet.categoricalEquivalences (f ≫ g)) : SSet.categoricalEquivalences f :=
  MorphismProperty.of_postcomp _ f g hg hfg

example (hf : SSet.categoricalEquivalences f)
    (hfg : SSet.categoricalEquivalences (f ≫ g)) : SSet.categoricalEquivalences g :=
  MorphismProperty.of_precomp _ f g hf hfg

-- Concrete composition of identities.
example : SSet.categoricalEquivalences
    ((𝟙 (Δ[1] : SSet.{u})) ≫ (𝟙 (Δ[1] : SSet.{u}))) :=
  MorphismProperty.comp_mem _ _ _
    (MorphismProperty.id_mem _ _) (MorphismProperty.id_mem _ _)

end CompositionAndTwoOutOfThree

section IsomorphismStability

variable {X Y Z : SSet.{u}}

example (e : X ⟶ Y) [IsIso e] (f : Y ⟶ Z) (hf : SSet.categoricalEquivalences f) :
    SSet.categoricalEquivalences (e ≫ f) :=
  MorphismProperty.RespectsIso.precomp _ e f hf

example (f : X ⟶ Y) (hf : SSet.categoricalEquivalences f) (e : Y ⟶ Z) [IsIso e] :
    SSet.categoricalEquivalences (f ≫ e) :=
  MorphismProperty.RespectsIso.postcomp _ e f hf

end IsomorphismStability

section Retracts

variable {X Y A B : SSet.{u}} {f : X ⟶ Y} {g : A ⟶ B}

example (h : RetractArrow f g) (hg : SSet.categoricalEquivalences g) :
    SSet.categoricalEquivalences f :=
  SSet.categoricalEquivalences.of_retract h hg

example (h : RetractArrow f g) (hg : SSet.categoricalEquivalences g) :
    SSet.categoricalEquivalences f :=
  MorphismProperty.of_retract h hg

example : SSet.categoricalEquivalences (𝟙 (Δ[0] : SSet.{u})) :=
  SSet.categoricalEquivalences.of_retract (Retract.refl _)
    (MorphismProperty.id_mem _ _)

end Retracts

section PrecompositionFunctoriality

variable {X Y Z C : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

example :
    (SSet.hoFunctor.map ((pre (𝟙 X)).app C)).toFunctor =
      𝟭 (SSet.hoFunctor.obj ((ihom X).obj C)) :=
  SSet.hoFunctor_pre_id C

example :
    (SSet.hoFunctor.map ((pre (f ≫ g)).app C)).toFunctor =
      (SSet.hoFunctor.map ((pre g).app C)).toFunctor ⋙
        (SSet.hoFunctor.map ((pre f).app C)).toFunctor :=
  SSet.hoFunctor_pre_comp C f g

example :
    (SSet.hoFunctor.map
      ((pre ((𝟙 (Δ[1] : SSet.{u})) ≫ (𝟙 (Δ[1] : SSet.{u})))).app C)).toFunctor =
      𝟭 (SSet.hoFunctor.obj ((ihom (Δ[1] : SSet.{u})).obj C)) := by
  rw [SSet.hoFunctor_pre_comp, SSet.hoFunctor_pre_id,
    Functor.comp_id]

end PrecompositionFunctoriality

end CategoricalEquivalencesTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
