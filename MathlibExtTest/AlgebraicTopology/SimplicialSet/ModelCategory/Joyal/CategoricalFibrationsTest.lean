/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CategoricalFibrations

/-!
# Genuine categorical fibrations: lifting and closure tests

The self-lifting test checks the consequence that a monic categorical
equivalence which is also a categorical fibration is an isomorphism.
The other examples exercise public lifting, retract, composition, and
arbitrary-base pullback use without a quasicategory hypothesis.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
namespace CategoricalFibrationsTest

example : SSet.categoricalFibrations.{u}.IsMultiplicative := inferInstance
example : SSet.categoricalFibrations.{u}.RespectsIso := inferInstance
example : SSet.categoricalFibrations.{u}.IsStableUnderRetracts := inferInstance
example : SSet.categoricalFibrations.{u}.IsStableUnderBaseChange := inferInstance
example : SSet.categoricalFibrations.{0}.IsStableUnderBaseChange := inferInstance

variable {A B X Y Z : SSet.{u}}

example (p : X ⟶ Y) (hp : SSet.categoricalFibrations p)
    (i : A ⟶ B) [Mono i] (hi : SSet.categoricalEquivalences i) :
    HasLiftingProperty i p :=
  (SSet.categoricalFibrations.mem_iff p).1 hp i inferInstance hi

example (p : X ⟶ Y)
    (h : ∀ {A B : SSet.{u}} (i : A ⟶ B),
      Mono i → SSet.categoricalEquivalences i → HasLiftingProperty i p) :
    SSet.categoricalFibrations p :=
  (SSet.categoricalFibrations.mem_iff p).2 h

example (e : X ≅ Y) : SSet.categoricalFibrations e.hom :=
  MorphismProperty.of_isIso _ e.hom

example (p : X ⟶ Y) (q : Y ⟶ Z)
    (hp : SSet.categoricalFibrations p) (hq : SSet.categoricalFibrations q) :
    SSet.categoricalFibrations (p ≫ q) :=
  MorphismProperty.comp_mem _ p q hp hq

example {p : X ⟶ Y} {q : A ⟶ B} (h : RetractArrow p q)
    (hq : SSet.categoricalFibrations q) : SSet.categoricalFibrations p :=
  MorphismProperty.of_retract h hq

example (p : X ⟶ Z) (f : Y ⟶ Z) (hp : SSet.categoricalFibrations p) :
    SSet.categoricalFibrations (pullback.snd p f) :=
  MorphismProperty.pullback_snd p f hp

example (f : X ⟶ Y) [Mono f] (hw : SSet.categoricalEquivalences f)
    (hf : SSet.categoricalFibrations f) : IsIso f := by
  let : HasLiftingProperty f f :=
    (SSet.categoricalFibrations.mem_iff f).1 hf f inferInstance hw
  let sq : CommSq (𝟙 X) f f (𝟙 Y) := ⟨by simp⟩
  let e : X ≅ Y :=
    { hom := f
      inv := sq.lift
      hom_inv_id := sq.fac_left
      inv_hom_id := sq.fac_right }
  exact e.isIso_hom

end CategoricalFibrationsTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
