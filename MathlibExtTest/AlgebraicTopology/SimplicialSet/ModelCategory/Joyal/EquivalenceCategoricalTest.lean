/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.EquivalenceCategorical

/-!
# Homotopy equivalences and the comparison functor: tests

These tests exercise the public API of
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.EquivalenceCategorical`:
external products of edges, internal composition of homotopy categories
of functor objects and its slices, the main theorem that a map with a
homotopy inverse up to isomorphism in `h Fun` (in isomorphism,
equivalence-edge, and inverse-data forms) is a categorical equivalence,
the identification of the `nerveAdjunction` counit with
`SSet.descNerve`, and the comparison functor
`SSet.hoFunNerveComparison` with its object formula, at an arbitrary
universe and at universe `0`.

The backward nerve gate for arbitrary equivalences of categories, the
morphism formula and naturality of the comparison functor, and the
assembly of the additional comparison obligation are the additional comparison obligation,
the additional comparison obligation, and the additional comparison obligation in
the main file header and are deliberately not tested here.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
namespace EquivalenceCategoricalTest

section MainTheorem

variable {X Y C : SSet.{u}} {f : X ⟶ Y}

example (g : Y ⟶ X)
    (α : (SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv X X (f ≫ g)) :
        SSet.hoFunctor.obj ((ihom X).obj X)) ≅
      SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv X X (𝟙 X)))
    (β : (SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv Y Y (g ≫ f)) :
        SSet.hoFunctor.obj ((ihom Y).obj Y)) ≅
      SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv Y Y (𝟙 Y))) :
    SSet.categoricalEquivalences f :=
  SSet.categoricalEquivalences.of_hoCompIso g α β

example (g : Y ⟶ X)
    {eX : SSet.Edge (SSet.ihomVertexEquiv X X (f ≫ g))
      (SSet.ihomVertexEquiv X X (𝟙 X))} (heX : eX.IsEquivalence)
    {eY : SSet.Edge (SSet.ihomVertexEquiv Y Y (g ≫ f))
      (SSet.ihomVertexEquiv Y Y (𝟙 Y))} (heY : eY.IsEquivalence) :
    SSet.categoricalEquivalences f :=
  SSet.categoricalEquivalences.of_isEquivalence_edges g heX heY

example (g : Y ⟶ X)
    {eX : SSet.Edge (SSet.ihomVertexEquiv X X (f ≫ g))
      (SSet.ihomVertexEquiv X X (𝟙 X))} (hX : eX.InvStruct)
    {eY : SSet.Edge (SSet.ihomVertexEquiv Y Y (g ≫ f))
      (SSet.ihomVertexEquiv Y Y (𝟙 Y))} (hY : eY.InvStruct) :
    SSet.categoricalEquivalences f :=
  SSet.categoricalEquivalences.of_invStruct_edges g hX hY

example : SSet.categoricalEquivalences (𝟙 X) :=
  SSet.categoricalEquivalences.of_hoCompIso (𝟙 X)
    (by simpa using Iso.refl _) (by simpa using Iso.refl _)

end MainTheorem

section DescentAndComparison

variable {Z : SSet.{u}} {D : Type u} [Category.{u} D]

example : ((ihom Z).obj (CategoryTheory.nerve D)).HomotopyCategory ⥤
    (Z.HomotopyCategory ⥤ D) :=
  SSet.hoFunNerveComparison Z D

example (m : Z ⟶ CategoryTheory.nerve D) :
    (SSet.hoFunNerveComparison Z D).obj
        (SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv Z _ m)) =
      SSet.descNerve m :=
  SSet.hoFunNerveComparison_obj_mk_ihomVertexEquiv m

example :
    (SSet.hoFunNerveComparison Z Z.HomotopyCategory).obj
        (SSet.HomotopyCategory.mk
          (SSet.ihomVertexEquiv Z _
            (CategoryTheory.nerveAdjunction.unit.app Z :
              Z ⟶ CategoryTheory.nerve Z.HomotopyCategory))) =
      𝟭 Z.HomotopyCategory :=
  (SSet.hoFunNerveComparison_obj_mk_ihomVertexEquiv _).trans
    (SSet.descNerve_nerveAdjunction_unit_app Z)

example (K : Z.HomotopyCategory ⥤ D) :
    (SSet.hoFunNerveComparison Z D).obj
        (SSet.HomotopyCategory.mk
          (SSet.ihomVertexEquiv Z _
            ((CategoryTheory.nerveAdjunction.unit.app Z :
                Z ⟶ CategoryTheory.nerve Z.HomotopyCategory) ≫
              CategoryTheory.nerveMap K))) =
      K :=
  (SSet.hoFunNerveComparison_obj_mk_ihomVertexEquiv _).trans
    ((SSet.descNerve_postcomp_nerveMap _ K).trans
      ((congrArg (· ⋙ K)
        (SSet.descNerve_nerveAdjunction_unit_app Z)).trans
          (Functor.id_comp K)))

example (m : Z ⟶ CategoryTheory.nerve (ULift.{u} (Fin 2))) :
    (SSet.hoFunNerveComparison Z (ULift.{u} (Fin 2))).obj
        (SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv Z _ m)) =
      SSet.descNerve m :=
  SSet.hoFunNerveComparison_obj_mk_ihomVertexEquiv m

end DescentAndComparison

section UniverseZero

variable {X Y : SSet.{0}} {f : X ⟶ Y}

example (g : Y ⟶ X)
    (α : (SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv X X (f ≫ g)) :
        SSet.hoFunctor.obj ((ihom X).obj X)) ≅
      SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv X X (𝟙 X)))
    (β : (SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv Y Y (g ≫ f)) :
        SSet.hoFunctor.obj ((ihom Y).obj Y)) ≅
      SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv Y Y (𝟙 Y))) :
    SSet.categoricalEquivalences.{0} f :=
  SSet.categoricalEquivalences.of_hoCompIso g α β

example (m : (Δ[0] : SSet.{0}) ⟶ CategoryTheory.nerve (Fin 2)) :
    (SSet.hoFunNerveComparison (Δ[0] : SSet.{0}) (Fin 2)).obj
        (SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv _ _ m)) =
      SSet.descNerve m :=
  SSet.hoFunNerveComparison_obj_mk_ihomVertexEquiv m

end UniverseZero

end EquivalenceCategoricalTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal

end
