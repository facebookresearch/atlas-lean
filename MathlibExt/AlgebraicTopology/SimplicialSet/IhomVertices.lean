/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import MathlibExt.AlgebraicTopology.SimplicialSet.Slice

/-! # Vertices of internal homs of simplicial sets

Low-level vertex and evaluation dictionary for the internal hom
`(ihom X).obj C` of simplicial sets (the simplicial functor object
`Fun(X, C)`), shared by the Joyal model structure packets:

* the vertex dictionary `SSet.ihomVertexEquiv`: vertices of
  `(ihom X).obj C` are exactly the maps `X ⟶ C`, precomposition and
  postcomposition on vertices are precomposition and postcomposition
  of the classifying maps (`SSet.curry'_comp_pre_app`,
  `SSet.ihomVertexEquiv_pre_app`, `SSet.ihomVertexEquiv_ihom_map`),
  and the Yoneda name of a vertex is its curried name transported
  along `SSet.Δ0IsoUnit` (`SSet.yonedaEquiv_symm_ihomVertexEquiv`);
* evaluation at the monoidal unit and at `Δ[0]` in the
  `MonoidalClosed.curry'` calculus: the canonical evaluations are the
  upstream `(MonoidalClosed.unitIsoSelf C).hom` and
  `(SSet.evalDeltaZeroIso C).hom` (the latter from
  `MathlibExt.AlgebraicTopology.SimplicialSet.Slice`, built from
  `SSet.Δ0IsoUnit`), and they send the curried name of a point
  back to the point (`SSet.curry'_unitIsoSelf_hom`,
  `SSet.curry'_evalDeltaZeroIso_hom`,
  `SSet.evalDeltaZeroIso_hom_app_ihomVertexEquiv`);
* the Yoneda/unit dictionary `SSet.yonedaEquiv_eq_unitHomEquiv`.

This module is deliberately placed below the Joyal theory: it imports
only the (upstream and `Slice`) simplicial-set API, and in particular
nothing about `SSet.categoricalEquivalences` or `SSet.coherentIso`.
Its consumers include
`MathlibExt.AlgebraicTopology.SimplicialSet.NerveDescent` and
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.NotCategorical`
(endpoint evaluations into nerves); later Joyal packets reuse these
single canonical copies of this API rather than private duplicates.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

/-- The vertex dictionary for an internal hom of simplicial sets: vertices
of `(ihom X).obj C` are exactly the maps `X ⟶ C`. This is the composite of
`MonoidalClosed.curryHomEquiv'` (maps out of the tensor unit into an
internal hom) with `SSet.unitHomEquiv` (maps out of the tensor unit are
vertices). -/
noncomputable def ihomVertexEquiv (X C : SSet.{u}) :
    (X ⟶ C) ≃ ((ihom X).obj C) _⦋0⦌ :=
  MonoidalClosed.curryHomEquiv'.trans (unitHomEquiv _)

/-- Currying a map and then precomposing the internal hom corresponds to
precomposing the map itself: `curry' g ≫ (pre f).app C = curry' (f ≫ g)`.
The proof uncurries both sides and uses
`MonoidalClosed.uncurry_pre_app` together with naturality of the right
unitor. -/
lemma curry'_comp_pre_app {A B C : SSet.{u}} (f : B ⟶ A) (g : A ⟶ C) :
    MonoidalClosed.curry' g ≫ (pre f).app C =
      MonoidalClosed.curry' (f ≫ g) := by
  apply MonoidalClosed.uncurry'_injective (X := B) (Y := C)
  simp [MonoidalClosed.uncurry', MonoidalClosed.uncurry_pre_app,
    MonoidalClosed.curry']

/-- Precomposition on internal-hom vertices is precomposition of the
classifying maps: the image of the vertex classified by `g : A ⟶ C` under
`(MonoidalClosed.pre f).app C` is the vertex classified by `f ≫ g`. -/
lemma ihomVertexEquiv_pre_app {A B C : SSet.{u}} (f : B ⟶ A) (g : A ⟶ C) :
    ((pre f).app C).app (op ⦋0⦌) (ihomVertexEquiv A C g) =
      ihomVertexEquiv B C (f ≫ g) :=
  congrArg (fun φ : 𝟙_ SSet.{u} ⟶ (ihom B).obj C => φ.app _ PUnit.unit)
    (curry'_comp_pre_app f g)

/-- The vertex dictionary `SSet.ihomVertexEquiv` is currying followed by
reading the resulting map out of the unit as a vertex. -/
theorem ihomVertexEquiv_eq (X C : SSet.{u}) (g : X ⟶ C) :
    ihomVertexEquiv X C g = unitHomEquiv _ (MonoidalClosed.curry' g) :=
  rfl

/-- The forward map of upstream `MonoidalClosed.unitIsoSelf` unfolds
definitionally to the left unitor followed by the internal-hom counit.
This is the single bridge to the `MonoidalClosed.curry'` calculus for
the canonical evaluation at the unit; there is no separate evaluation
map to maintain. -/
private lemma unitIsoSelf_hom_eq (C : SSet.{u}) :
    (MonoidalClosed.unitIsoSelf C).hom =
      (λ_ ((ihom (𝟙_ SSet.{u})).obj C)).inv ≫ (ihom.ev (𝟙_ SSet.{u})).app C :=
  rfl

/-- Evaluation at the monoidal unit (the forward map of upstream
`MonoidalClosed.unitIsoSelf`) sends the curried name of `h` back to
`h`. -/
lemma curry'_unitIsoSelf_hom {C : SSet.{u}} (h : 𝟙_ SSet.{u} ⟶ C) :
    MonoidalClosed.curry' h ≫ (MonoidalClosed.unitIsoSelf C).hom = h := by
  rw [unitIsoSelf_hom_eq, ← Category.assoc,
    MonoidalCategory.leftUnitor_inv_naturality, Category.assoc,
    MonoidalClosed.whiskerLeft_curry'_ihom_ev_app,
    ← MonoidalCategory.unitors_equal, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-- Evaluation at `Δ[0]` (the forward map of `SSet.evalDeltaZeroIso`
from `MathlibExt.AlgebraicTopology.SimplicialSet.Slice`) sends the
curried name of a point of `C` to the corresponding map from the
monoidal unit. -/
lemma curry'_evalDeltaZeroIso_hom {C : SSet.{u}}
    (q : (Δ[0] : SSet.{u}) ⟶ C) :
    MonoidalClosed.curry' q ≫ (evalDeltaZeroIso C).hom =
      Δ0IsoUnit.inv ≫ q := by
  rw [evalDeltaZeroIso_hom, ← Category.assoc, curry'_comp_pre_app,
    curry'_unitIsoSelf_hom]

/-- The vertex of `C` classified by a point `q : Δ[0] ⟶ C` can equally be
read through `SSet.unitHomEquiv` after precomposing with any map
`𝟙_ SSet ⟶ Δ[0]`, because `Δ[0]` has a single vertex. -/
theorem yonedaEquiv_eq_unitHomEquiv {C : SSet.{u}}
    (s : 𝟙_ SSet.{u} ⟶ (Δ[0] : SSet.{u})) (q : (Δ[0] : SSet.{u}) ⟶ C) :
    yonedaEquiv q = unitHomEquiv C (s ≫ q) := by
  have h : (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌) : (Δ[0] : SSet.{u}) _⦋0⦌) =
      s.app _ PUnit.unit := by
    apply stdSimplex.obj₀Equiv.injective
    apply Fin.ext
    have hx := (stdSimplex.obj₀Equiv
      (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))).isLt
    have hy := (stdSimplex.obj₀Equiv (s.app _ PUnit.unit)).isLt
    omega
  have e1 : yonedaEquiv q = q.app _ (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)) := rfl
  have e2 : unitHomEquiv C (s ≫ q) = q.app _ (s.app _ PUnit.unit) := rfl
  rw [e1, e2, h]

/-- Evaluation at `Δ[0]` sends the vertex classified by a point `q` of
`C` to the vertex of `C` classified by `q` itself. -/
theorem evalDeltaZeroIso_hom_app_ihomVertexEquiv {C : SSet.{u}}
    (q : (Δ[0] : SSet.{u}) ⟶ C) :
    ((evalDeltaZeroIso C).hom).app (op ⦋0⦌) (ihomVertexEquiv (Δ[0]) C q) =
      yonedaEquiv q := by
  have h : ((evalDeltaZeroIso C).hom).app (op ⦋0⦌)
        (ihomVertexEquiv (Δ[0]) C q) =
      unitHomEquiv C (MonoidalClosed.curry' q ≫ (evalDeltaZeroIso C).hom) :=
    rfl
  rw [h, curry'_evalDeltaZeroIso_hom, ← yonedaEquiv_eq_unitHomEquiv]

/-- Postcomposition on internal-hom vertices is postcomposition of the
classifying maps. -/
theorem ihomVertexEquiv_ihom_map {A B C : SSet.{u}} (m : A ⟶ B) (q : B ⟶ C) :
    ((ihom A).map q).app (op ⦋0⦌) (ihomVertexEquiv A B m) =
      ihomVertexEquiv A C (m ≫ q) := by
  have h : MonoidalClosed.curry' m ≫ (ihom A).map q =
      MonoidalClosed.curry' (m ≫ q) := by
    simp only [MonoidalClosed.curry', ← MonoidalClosed.curry_natural_right,
      Category.assoc]
  exact congrArg (fun φ : 𝟙_ SSet.{u} ⟶ (ihom A).obj C =>
    φ.app _ PUnit.unit) h

/-- The Yoneda name of a vertex, read as a map out of the unit, is the
transport of its curried name along `SSet.Δ0IsoUnit`. -/
theorem yonedaEquiv_symm_ihomVertexEquiv (X C : SSet.{u}) (m : X ⟶ C) :
    yonedaEquiv.symm (ihomVertexEquiv X C m) =
      Δ0IsoUnit.hom ≫ MonoidalClosed.curry' m := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, ihomVertexEquiv_eq,
    yonedaEquiv_eq_unitHomEquiv Δ0IsoUnit.inv
      (Δ0IsoUnit.hom ≫ MonoidalClosed.curry' m)]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Evaluation of the vertex classified by `m` at a vertex `z` is
`m.app _ z`: the vertex form of
`MonoidalClosed.whiskerLeft_curry'_ihom_ev_app`. -/
theorem ihom_ev_app_zero_ihomVertexEquiv {X C : SSet.{u}} (m : X ⟶ C) (z : X _⦋0⦌) :
    ((ihom.ev X).app C).app (op ⦋0⦌) (z, ihomVertexEquiv X C m) =
      m.app (op ⦋0⦌) z := by
  have h := MonoidalClosed.whiskerLeft_curry'_ihom_ev_app m
  have h2 := congrArg (fun φ : X ⊗ 𝟙_ SSet.{u} ⟶ C =>
    φ.app (op ⦋0⦌) (z, PUnit.unit)) h
  exact h2

/-- Evaluation on a `1`-simplex that is an edge in the first factor and an
identity edge at the vertex classified by `m` in the second is `m` applied
to that edge. -/
theorem ihom_ev_app_one_ihomVertexEquiv {X C : SSet.{u}} (m : X ⟶ C) {z₀ z₁ : X _⦋0⦌}
    (ε : Edge z₀ z₁) :
    ((ihom.ev X).app C).app (op ⦋1⦌)
        (ε.edge, (Edge.id (ihomVertexEquiv X C m)).edge) =
      m.app (op ⦋1⦌) ε.edge := by
  have h := MonoidalClosed.whiskerLeft_curry'_ihom_ev_app m
  have h2 := congrArg (fun φ : X ⊗ 𝟙_ SSet.{u} ⟶ C =>
    φ.app (op ⦋1⦌) (ε.edge, PUnit.unit)) h
  exact h2

end SSet
