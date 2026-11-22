/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveDescent
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CategoricalEquivalences

/-!
# Categorical equivalences, homotopy categories, and nerves

The generic nerve-descent and vertex-evaluation infrastructure used
by the Joyal characterizations is not proved in this file. It lives
in the neutral module
`MathlibExt.AlgebraicTopology.SimplicialSet.NerveDescent`, which
provides descent of maps into nerves (`SSet.descNerve` and its
formulas), detection on `2`-truncations (`SSet.nerveTruncEquiv`),
the nerve-adjunction transpose and canonical-unit formulas, and
evaluation of functor-object edges at vertices
(`SSet.edgeAtVertex`). The underlying internal-hom vertex dictionary
is in `MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices`.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Limits Opposite

open scoped Simplicial

universe v u

namespace SSet

variable {X Y : SSet.{u}}

/-! ## Testing categorical equivalences against nerves; strict nerve gate -/

/-- A categorical equivalence tested against a nerve: precomposition
with a categorical equivalence induces an equivalence of homotopy
categories of functor objects into every nerve, since nerves are
quasicategories. This is the input to the proof of
the additional comparison obligation recorded in the module header. The
`Category.{u}` restriction on `D` is forced here: testing
`categoricalEquivalences.{u} f` against `nerve D` requires
`nerve D : SSet.{u}`. -/
theorem categoricalEquivalences.hoPre_nerve_isEquivalence {f : X ⟶ Y}
    (hf : categoricalEquivalences f) (D : Type u) [Category.{u} D] :
    (hoFunctor.map ((MonoidalClosed.pre f).app
      (CategoryTheory.nerve D))).toFunctor.IsEquivalence :=
  hf (CategoryTheory.nerve D) inferInstance

/-- Strict nerve gate: if `F.toCatHom` is an isomorphism in `Cat`, i.e.
`F` is a strict isomorphism of categories, then
`CategoryTheory.nerveMap F` is an isomorphism of simplicial sets and
hence a categorical equivalence. The full backward nerve gate for
arbitrary equivalences of categories is the additional comparison obligation in the
module header. -/
theorem categoricalEquivalences.nerveMap_of_isIso_toCatHom
    {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D)
    [IsIso F.toCatHom] :
    categoricalEquivalences (CategoryTheory.nerveMap F) := by
  have hI : IsIso (CategoryTheory.nerveMap F) := by
    have h : CategoryTheory.nerveMap F =
        CategoryTheory.nerveFunctor.map F.toCatHom := rfl
    rw [h]
    exact Functor.map_isIso _ _
  exact categoricalEquivalences.of_isIso _

/-- The nerve of the forward functor of an isomorphism in `Cat` is a
categorical equivalence. -/
theorem categoricalEquivalences.nerveMap_catIso_hom
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (e : Cat.of C ≅ Cat.of D) :
    categoricalEquivalences (CategoryTheory.nerveMap e.hom.toFunctor) := by
  have hI : IsIso (e.hom.toFunctor).toCatHom :=
    inferInstanceAs (IsIso e.hom)
  exact categoricalEquivalences.nerveMap_of_isIso_toCatHom _

end SSet

end
