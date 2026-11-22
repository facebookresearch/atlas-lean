/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.HoFunctorCategorical

/-!
# Testing categorical equivalences against nerves: tests

These tests exercise the Joyal-specific public API of
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.HoFunctorCategorical`:
testing a categorical equivalence against nerves and the strict nerve
gate for isomorphisms in `Cat`. The generic nerve-descent and
vertex-evaluation API imported by that module is tested separately in
`MathlibExtTest.AlgebraicTopology.SimplicialSet.NerveDescentTest`.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
namespace HoFunctorCategoricalTest

section NerveTestAndStrictGate

variable {X Y : SSet.{u}} {f : X ⟶ Y} {C D : Type u}
variable [Category.{u} C] [Category.{u} D]

example (hf : SSet.categoricalEquivalences f) :
    (SSet.hoFunctor.map ((MonoidalClosed.pre f).app
      (CategoryTheory.nerve D))).toFunctor.IsEquivalence :=
  SSet.categoricalEquivalences.hoPre_nerve_isEquivalence hf D

example (hf : SSet.categoricalEquivalences f) :
    (SSet.hoFunctor.map ((MonoidalClosed.pre f).app
      (CategoryTheory.nerve (ULift.{u} (Fin 2))))).toFunctor.IsEquivalence :=
  SSet.categoricalEquivalences.hoPre_nerve_isEquivalence hf _

example (F : C ⥤ D) [IsIso F.toCatHom] :
    SSet.categoricalEquivalences (CategoryTheory.nerveMap F) :=
  SSet.categoricalEquivalences.nerveMap_of_isIso_toCatHom F

example (e : Cat.of C ≅ Cat.of D) :
    SSet.categoricalEquivalences
      (CategoryTheory.nerveMap e.hom.toFunctor) :=
  SSet.categoricalEquivalences.nerveMap_catIso_hom e

example : SSet.categoricalEquivalences
    (CategoryTheory.nerveMap (Iso.refl (Cat.of C)).hom.toFunctor) :=
  SSet.categoricalEquivalences.nerveMap_catIso_hom (Iso.refl _)

-- Mixed-universe strict-gate clients: `Type 0` (object universe `1`,
-- morphism universe `0`) and `ULiftHom.{1} (Fin 2)` (object universe
-- `0`, morphism universe `1`).
example : SSet.categoricalEquivalences
    (CategoryTheory.nerveMap (Iso.refl (Cat.of (Type 0))).hom.toFunctor) :=
  SSet.categoricalEquivalences.nerveMap_catIso_hom (Iso.refl _)

example : SSet.categoricalEquivalences
    (CategoryTheory.nerveMap
      (Iso.refl (Cat.of (ULiftHom.{1} (Fin 2)))).hom.toFunctor) :=
  SSet.categoricalEquivalences.nerveMap_catIso_hom (Iso.refl _)

end NerveTestAndStrictGate

end HoFunctorCategoricalTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal

end
