/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveDescent
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CategoricalEquivalences

/-! # Categorical equivalences, homotopy categories, and nerves

First characterizations of Joyal categorical equivalences
(`SSet.categoricalEquivalences`, the `hFun` class of HTT §2.2.5) through
ordinary homotopy categories and nerves (packet T20 of the Joyal model
structure programme).

## Imported infrastructure

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

## Main results (proved in this file)

This file proves the first nerve tests for Joyal categorical
equivalences, plus the strict nerve gate. The headline
characterization itself (target (1) of packet T20: a categorical
equivalence induces an equivalence of ordinary homotopy categories)
is not proved in this file. Its proof is separate follow-up work
in the programme, using the comparison functor
`SSet.hoFunNerveComparison` constructed in
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.EquivalenceCategorical`.
No statement in this file alone should be read as claiming
target (1).

* `SSet.categoricalEquivalences.hoPre_nerve_isEquivalence`: a
  categorical equivalence induces an equivalence on homotopy
  categories of functor objects into every nerve.
* Strict nerve gate:
  `SSet.categoricalEquivalences.nerveMap_of_isIso_toCatHom` and
  `SSet.categoricalEquivalences.nerveMap_catIso_hom`: nerves of strict
  isomorphisms of categories are categorical equivalences.

## What is not proved in this file

* Target (1) of packet T20 — if `f : X ⟶ Y` is a categorical
  equivalence then `(SSet.hoFunctor.map f).toFunctor` is an
  equivalence of ordinary categories — is not proved in this file.
  That proof is separate follow-up work in the programme; it uses
  the comparison functor `SSet.hoFunNerveComparison` from
  `MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.EquivalenceCategorical`,
  where it is built by a route that does not pass through the
  square lemma formerly recorded here as
  TODO(T20-hoFunctor)(a).
* The nerve gate in both directions is not proved in this file
  (only the strict case `IsIso F.toCatHom` is proved here); the
  general characterization of categorical equivalences between
  nerves is separate follow-up work in the programme
  (TODO(T20-nerve-backward) for the backward direction).
* Evaluation at `Δ[0]` is the canonical isomorphism
  `SSet.evalDeltaZeroIso` in
  `MathlibExt.AlgebraicTopology.SimplicialSet.Slice` (built from
  `SSet.Δ0IsoUnit` and upstream `MonoidalClosed.unitIsoSelf`),
  and evaluation at the unit is `(MonoidalClosed.unitIsoSelf C).hom`
  itself; this file defines no separate evaluation maps. The vertex
  formulas for these canonical maps in `MonoidalClosed.curry'`
  calculus are in
  `MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices`, and the
  nerve-specific vertex/edge evaluation formulas are in
  `MathlibExt.AlgebraicTopology.SimplicialSet.NerveDescent`.
* TODO(T20-products): stability of `SSet.categoricalEquivalences`
  under binary products and coproducts in `SSet` is not proved here.
  For products the expected proof curries through
  `Fun(X ⊗ Y, C) ≅ Fun(X, Fun(Y, C))` and uses that an internal hom
  into a quasicategory is a quasicategory; for coproducts it uses
  `Fun(X ⊔ Y, C) ≅ Fun(X, C) × Fun(Y, C)` and that `SSet.hoFunctor`
  preserves binary products. Neither identification of precomposition
  with the product of precompositions is carried out here.

## References

* J. Lurie, *Higher Topos Theory*, §2.2.5 (weak categorical equivalences)
  and §2.3 (the homotopy category detection of categorical equivalences
  against nerves).
* D. Stevenson, *Notes on the Joyal model structure*, arXiv:1810.05233.
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
TODO(T20-hoFunctor) recorded in the module header. The
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
arbitrary equivalences of categories is TODO(T20-nerve-backward) in the
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
