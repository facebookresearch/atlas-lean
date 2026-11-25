/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.GeneralJoinSlice
public import MathlibExt.AlgebraicTopology.SimplicialSet.Slice
public import MathlibExt.AlgebraicTopology.SimplicialSet.FullSubcomplex

/-!
# Slice simplicial sets and mapping spaces (join model)

For a simplicial set `X` and a vertex `x : Δ[0] ⟶ X`, this file provides
the *genuine join slices* of Lurie (HTT §1.2.9) and Kerodon (§4.3.5;
joins in §4.3.3):

* `sliceOver X x` (written `X_{/x}` in the literature), whose
  `n`-simplices are the maps `f : Δ[n] ⋆ Δ[0] ⟶ X` whose restriction
  along the right endpoint inclusion `SSet.joinInr Δ[n] Δ[0]` is `x`;
* `sliceUnder X x` (written `X_{x/}`), dually, with `n`-simplices the
  maps `f : Δ[0] ⋆ Δ[n] ⟶ X` whose restriction along the left endpoint
  inclusion `SSet.joinInl Δ[0] Δ[n]` is `x`;
* the right mapping space `mappingSpaceRight X x y`
  (Lurie's `Hom^R_X(x, y)`), the fiber of the forgetful map
  `sliceOver.proj X y : sliceOver X y ⟶ X` at `x`: its `n`-simplices
  are the maps `f : Δ[n] ⋆ Δ[0] ⟶ X` with both endpoint restrictions
  fixed (left restriction constantly `x`, right restriction `y`);
* the left mapping space `mappingSpaceLeft X x y`
  (Lurie's `Hom^L_X(x, y)`), dually the fiber of
  `sliceUnder.proj X x` at `y`.

Each object is defined *directly* as a presheaf by the displayed
subtype formula, with functoriality given by precomposition with joins
of simplicial operators — not via an abstract pullback. This makes the
simplex-level characterizations definitional (`simplexEquiv` below is
`Equiv.refl`).

## Names (read before using)

The general slice objects, projections, restriction maps and
postcomposition maps come from
[GeneralJoinSlice.lean](GeneralJoinSlice.lean). This file specializes that
API to vertices and builds mapping spaces and their applications.

The declarations here carry the standard names `SSet.sliceOver`,
`SSet.sliceUnder`, `SSet.mappingSpaceRight` and
`SSet.mappingSpaceLeft`. The exponential/path model in
[Slice.lean](Slice.lean) uses the `path`-prefixed names
(`SSet.pathSliceOver` and companions), so the unprefixed names denote
the genuine join slices and mapping spaces defined here.

## What is proved

* the definitions, with definitional simplex characterizations
  (`sliceOver.simplexEquiv` and companions) and the restriction
  (face/degeneracy) action described by precomposition
  (`sliceOver.map_val` and companions);
* the forgetful maps `sliceOver.proj X x : sliceOver X x ⟶ X` and
  `sliceUnder.proj X x : sliceUnder X x ⟶ X`, given at each level by
  restriction along the free endpoint inclusion
  (`sliceOver.proj_apply` and companion);
* functoriality in `X`: `sliceOver.map`, `sliceUnder.map`,
  `mappingSpaceRight.map`, `mappingSpaceLeft.map` by postcomposition,
  compatible with the forgetful maps and satisfying the identity and
  composition laws;
* the canonical maps `mappingSpaceRight.toSliceOver` and
  `mappingSpaceLeft.toSliceUnder`, with the fiber condition
  `mappingSpaceRight.proj_toSliceOver_apply` (the free endpoint of a
  mapping-space simplex is constantly the source vertex), which is the
  element-level statement that the mapping space is the fiber of the
  slice projection;
* transport along `SSet.joinStdSimplexIso`: `n`-simplices of
  `sliceOver X x` are identified with `(n+1)`-simplices of `X`
  (`sliceOver.simplexEquivSucc`), and in particular `0`-simplices of
  `sliceOver X x` are edges of `X` into `x`
  (`sliceOver.zeroSimplexEquiv`); dually for `sliceUnder`, and
  similarly for both mapping spaces;
* the induced maps on left and right mapping spaces of a
  full-subcomplex inclusion are injective on simplices in every
  degree (`mappingSpaceLeft_map_full_ι_app_injective` and
  `mappingSpaceRight_map_full_ι_app_injective`).

## Transported endpoint identifications

In `sliceOver.simplexEquivSucc`, the condition on an
`(n+1)`-simplex `σ : Δ[n + 1] ⟶ X` is stated using the *transported*
vertex map `rightVertex n := SSet.joinInr Δ[n] Δ[0] ≫
(SSet.joinStdSimplexIso n 0).hom : Δ[0] ⟶ Δ[n + 1]`, i.e. the condition
is `rightVertex n ≫ σ = x`; dually the front condition in
`mappingSpaceRight.simplexEquivSucc` uses the transported front face
`frontInclusion n`. These transports are identified with the standard
inclusions as follows. The front face is the last face map,
`SSet.frontInclusion_eq` below, via the left endpoint identification
on representables `SSet.joinInl_comp_joinStdSimplexIso_hom` in
[JoinProperties.lean](JoinProperties.lean). For the right vertex,
this file proves the face relation
`SSet.rightVertex_comp_δ_castSucc` and the full identification
`rightVertex n = SSet.stdSimplex.map
(AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌)` (`SSet.rightVertex_eq`
below), deduced from that face relation by vertex pinning. The general right-inclusion
identification `SSet.joinInr Δ[m] Δ[n] ≫ (SSet.joinStdSimplexIso m n).hom =
SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋m⦌ ⦋n⦌)` and
the dual identifications for `leftVertex`/`backInclusion` remain
open; see the TODO in [JoinProperties.lean](JoinProperties.lean).
Consequently `zeroSimplexEquiv` below still states its endpoint
condition as `rightVertex 0 ≫ e = x`, with the standard-vertex
reading available via `SSet.rightVertex_zero` below.

## References

- J. Lurie, *Higher Topos Theory*, §1.2.8 (joins), §1.2.9 (slices) and
  §1.2.2 (mapping spaces `Hom^L`, `Hom^R`).
- *Kerodon*, §4.3.3 (joins), §4.3.5 (slice categories) and §4.6
  (mapping spaces).
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet

/-- The right endpoint inclusion `Δ[n] ⋆ Δ[0]` transported along
`SSet.joinStdSimplexIso n 0 : Δ[n] ⋆ Δ[0] ≅ Δ[n + 1]`: the vertex of
`Δ[n + 1]` corresponding to the right factor. See the file header and
`SSet.rightVertex_comp_δ_castSucc` below for the identification of
this map with the standard last-vertex inclusion. -/
def rightVertex (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ Δ[n + 1] :=
  SSet.joinInr Δ[n] Δ[0] ≫ (SSet.joinStdSimplexIso n 0).hom

/-- The left endpoint inclusion `Δ[n] ⋆ Δ[0]` transported along
`SSet.joinStdSimplexIso n 0`: the front face of `Δ[n + 1]` spanned by
the left factor. -/
def frontInclusion (n : ℕ) : (Δ[n] : SSet.{u}) ⟶ Δ[n + 1] :=
  SSet.joinInl Δ[n] Δ[0] ≫ (SSet.joinStdSimplexIso n 0).hom

/-- The left endpoint inclusion `Δ[0] ⋆ Δ[n]` transported along
`SSet.joinStdSimplexIso 0 n : Δ[0] ⋆ Δ[n] ≅ Δ[0 + n + 1]`: the vertex
of `Δ[0 + n + 1]` corresponding to the left factor. Note
`0 + n + 1 = n + 1` as natural numbers; the unreduced form is kept
because it is the form produced by `SSet.joinStdSimplexIso`. -/
def leftVertex (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ Δ[0 + n + 1] :=
  SSet.joinInl Δ[0] Δ[n] ≫ (SSet.joinStdSimplexIso 0 n).hom

/-- The right endpoint inclusion `Δ[0] ⋆ Δ[n]` transported along
`SSet.joinStdSimplexIso 0 n`: the back face of `Δ[0 + n + 1]` spanned
by the right factor. -/
def backInclusion (n : ℕ) : (Δ[n] : SSet.{u}) ⟶ Δ[0 + n + 1] :=
  SSet.joinInr Δ[0] Δ[n] ≫ (SSet.joinStdSimplexIso 0 n).hom

namespace sliceOver

variable (X : SSet.{u}) (x : (Δ[0] : SSet.{u}) ⟶ X)

/-- Transporting along `SSet.joinStdSimplexIso n 0 : Δ[n] ⋆ Δ[0] ≅
Δ[n + 1]`, the `n`-simplices of `sliceOver X x` are the
`(n + 1)`-simplices of `X` whose restriction along the transported
vertex `rightVertex n` is `x`. See the file header for the
identification of `rightVertex n` with the standard last-vertex
inclusion. -/
def simplexEquivSucc (n : ℕ) :
    (sliceOver X x).obj (op ⦋n⦌) ≃
      { σ : (Δ[n + 1] : SSet.{u}) ⟶ X // rightVertex n ≫ σ = x } where
  toFun f := ⟨(SSet.joinStdSimplexIso n 0).inv ≫ f.1, by
    rw [rightVertex, Category.assoc,
      ← Category.assoc (SSet.joinStdSimplexIso n 0).hom
        (SSet.joinStdSimplexIso n 0).inv f.1,
      Iso.hom_inv_id, Category.id_comp]
    exact f.2⟩
  invFun σ := ⟨(SSet.joinStdSimplexIso n 0).hom ≫ σ.1, by
    rw [← Category.assoc]
    exact σ.2⟩
  left_inv f := by
    apply Subtype.ext
    change (SSet.joinStdSimplexIso n 0).hom ≫
        ((SSet.joinStdSimplexIso n 0).inv ≫ f.1) = f.1
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  right_inv σ := by
    apply Subtype.ext
    change (SSet.joinStdSimplexIso n 0).inv ≫
        ((SSet.joinStdSimplexIso n 0).hom ≫ σ.1) = σ.1
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The forward direction of `simplexEquivSucc` is precomposition
with the inverse of `SSet.joinStdSimplexIso n 0`. -/
@[simp]
lemma simplexEquivSucc_apply_val (n : ℕ)
    (f : (sliceOver X x).obj (op ⦋n⦌)) :
    ((simplexEquivSucc X x n) f).1 =
      (SSet.joinStdSimplexIso n 0).inv ≫ f.1 :=
  rfl

/-- The inverse direction of `simplexEquivSucc` is precomposition
with `SSet.joinStdSimplexIso n 0`. -/
@[simp]
lemma simplexEquivSucc_symm_apply_val (n : ℕ)
    (σ : { σ : (Δ[n + 1] : SSet.{u}) ⟶ X // rightVertex n ≫ σ = x }) :
    ((simplexEquivSucc X x n).symm σ).1 =
      (SSet.joinStdSimplexIso n 0).hom ≫ σ.1 :=
  rfl

/-- The `0`-simplices of `sliceOver X x` are the edges of `X` into
`x`: maps `e : Δ[1] ⟶ X` with `rightVertex 0 ≫ e = x`. The other
endpoint of the edge is the image under `proj X x`, by
`proj_apply`. See the file header for the identification of
`rightVertex 0` with a standard `stdSimplex` vertex map. -/
def zeroSimplexEquiv :
    (sliceOver X x).obj (op ⦋0⦌) ≃
      { e : (Δ[1] : SSet.{u}) ⟶ X // rightVertex 0 ≫ e = x } :=
  simplexEquivSucc X x 0

end sliceOver

namespace sliceUnder

variable (X : SSet.{u}) (x : (Δ[0] : SSet.{u}) ⟶ X)

/-- Transporting along `SSet.joinStdSimplexIso 0 n : Δ[0] ⋆ Δ[n] ≅
Δ[0 + n + 1]`, the `n`-simplices of `sliceUnder X x` are the
`(n + 1)`-simplices of `X` whose restriction along the transported
vertex `leftVertex n` is `x`. -/
def simplexEquivSucc (n : ℕ) :
    (sliceUnder X x).obj (op ⦋n⦌) ≃
      { σ : (Δ[0 + n + 1] : SSet.{u}) ⟶ X // leftVertex n ≫ σ = x } where
  toFun f := ⟨(SSet.joinStdSimplexIso 0 n).inv ≫ f.1, by
    rw [leftVertex, Category.assoc,
      ← Category.assoc (SSet.joinStdSimplexIso 0 n).hom
        (SSet.joinStdSimplexIso 0 n).inv f.1,
      Iso.hom_inv_id, Category.id_comp]
    exact f.2⟩
  invFun σ := ⟨(SSet.joinStdSimplexIso 0 n).hom ≫ σ.1, by
    rw [← Category.assoc]
    exact σ.2⟩
  left_inv f := by
    apply Subtype.ext
    change (SSet.joinStdSimplexIso 0 n).hom ≫
        ((SSet.joinStdSimplexIso 0 n).inv ≫ f.1) = f.1
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  right_inv σ := by
    apply Subtype.ext
    change (SSet.joinStdSimplexIso 0 n).inv ≫
        ((SSet.joinStdSimplexIso 0 n).hom ≫ σ.1) = σ.1
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The forward direction of `simplexEquivSucc` is precomposition
with the inverse of `SSet.joinStdSimplexIso 0 n`. -/
@[simp]
lemma simplexEquivSucc_apply_val (n : ℕ)
    (f : (sliceUnder X x).obj (op ⦋n⦌)) :
    ((simplexEquivSucc X x n) f).1 =
      (SSet.joinStdSimplexIso 0 n).inv ≫ f.1 :=
  rfl

/-- The inverse direction of `simplexEquivSucc` is precomposition
with `SSet.joinStdSimplexIso 0 n`. -/
@[simp]
lemma simplexEquivSucc_symm_apply_val (n : ℕ)
    (σ : { σ : (Δ[0 + n + 1] : SSet.{u}) ⟶ X // leftVertex n ≫ σ = x }) :
    ((simplexEquivSucc X x n).symm σ).1 =
      (SSet.joinStdSimplexIso 0 n).hom ≫ σ.1 :=
  rfl

/-- The `0`-simplices of `sliceUnder X x` are the edges of `X` out of
`x`: maps `e : Δ[1] ⟶ X` with `leftVertex 0 ≫ e = x`. The other
endpoint of the edge is the image under `proj X x`, by
`proj_apply`. -/
def zeroSimplexEquiv :
    (sliceUnder X x).obj (op ⦋0⦌) ≃
      { e : (Δ[1] : SSet.{u}) ⟶ X // leftVertex 0 ≫ e = x } :=
  simplexEquivSucc X x 0

end sliceUnder

/-- The right mapping space `Hom^R_X(x, y)` between two vertices of
`X`: the fiber of `sliceOver.proj X y : sliceOver X y ⟶ X` at `x`,
defined directly by its simplices. An `n`-simplex is a map
`f : Δ[n] ⋆ Δ[0] ⟶ X` with both endpoint restrictions fixed: the
left restriction is the constant simplex at `x` and the right
restriction is `y`. -/
def mappingSpaceRight (X : SSet.{u}) (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    SSet.{u} where
  obj n :=
    { f : SSet.stdSimplex.obj n.unop ⋆ (Δ[0] : SSet.{u}) ⟶ X //
      SSet.joinInl (SSet.stdSimplex.obj n.unop) Δ[0] ≫ f =
          toDeltaZero (SSet.stdSimplex.obj n.unop) ≫ x ∧
        SSet.joinInr (SSet.stdSimplex.obj n.unop) Δ[0] ≫ f = y }
  map α := ↾fun f =>
    ⟨(SSet.join.map (SSet.stdSimplex.map α.unop)).app Δ[0] ≫ f.1, by
      constructor
      · have hterm : SSet.stdSimplex.map α.unop ≫ toDeltaZero _ =
            toDeltaZero _ :=
          toDeltaZero_eq _
        rw [← Category.assoc, ← SSet.map_comp_joinInl, Category.assoc,
          f.2.1, ← Category.assoc, hterm]
      · rw [← Category.assoc, SSet.joinInr_comp_map]
        exact f.2.2⟩
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    simp
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    simp [Category.assoc]

namespace mappingSpaceRight

variable (X : SSet.{u}) (x y : (Δ[0] : SSet.{u}) ⟶ X)

/-- The `n`-simplices of `mappingSpaceRight X x y` are definitionally
the maps `Δ[n] ⋆ Δ[0] ⟶ X` with both endpoint restrictions fixed. -/
def simplexEquiv (n : ℕ) :
    (mappingSpaceRight X x y).obj (op ⦋n⦌) ≃
      { f : (Δ[n] : SSet.{u}) ⋆ Δ[0] ⟶ X //
        SSet.joinInl Δ[n] Δ[0] ≫ f = toDeltaZero Δ[n] ≫ x ∧
          SSet.joinInr Δ[n] Δ[0] ≫ f = y } :=
  Equiv.refl _

/-- The left endpoint condition on a simplex of the right mapping
space: its left restriction is constantly `x`. -/
@[simp]
lemma condition_left {n : SimplexCategoryᵒᵖ}
    (f : (mappingSpaceRight X x y).obj n) :
    SSet.joinInl (SSet.stdSimplex.obj n.unop) Δ[0] ≫ f.1 =
      toDeltaZero (SSet.stdSimplex.obj n.unop) ≫ x :=
  f.2.1

/-- The right endpoint condition on a simplex of the right mapping
space: its right restriction is `y`. -/
@[simp]
lemma condition_right {n : SimplexCategoryᵒᵖ}
    (f : (mappingSpaceRight X x y).obj n) :
    SSet.joinInr (SSet.stdSimplex.obj n.unop) Δ[0] ≫ f.1 = y :=
  f.2.2

/-- The simplicial operators on `mappingSpaceRight X x y` act by
precomposition with joins of simplicial operators. -/
@[simp]
lemma map_val {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (f : (mappingSpaceRight X x y).obj n) :
    ((mappingSpaceRight X x y).map α f).1 =
      (SSet.join.map (SSet.stdSimplex.map α.unop)).app Δ[0] ≫ f.1 :=
  rfl

/-- The canonical map from the right mapping space to the over-slice
at `y`, forgetting the fixed source. -/
def toSliceOver : mappingSpaceRight X x y ⟶ sliceOver X y where
  app n := ↾fun f => ⟨f.1, f.2.2⟩
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    change (SSet.join.map (SSet.stdSimplex.map α.unop)).app Δ[0] ≫ f.1 =
      (SSet.join.map (SSet.stdSimplex.map α.unop)).app Δ[0] ≫ f.1
    rfl

/-- `toSliceOver` does not change the underlying join map. -/
@[simp]
lemma toSliceOver_app_val {n : SimplexCategoryᵒᵖ}
    (f : (mappingSpaceRight X x y).obj n) :
    ((toSliceOver X x y).app n f).1 = f.1 :=
  rfl

/-- The fiber condition: the free (source) endpoint of a simplex of
the right mapping space, read through the over-slice projection, is
the constant simplex at `x`. This is the element-level statement
that `mappingSpaceRight X x y` is the fiber of
`sliceOver.proj X y` at `x`. -/
lemma proj_toSliceOver_apply {n : SimplexCategoryᵒᵖ}
    (f : (mappingSpaceRight X x y).obj n) :
    (sliceOver.proj X y).app n ((toSliceOver X x y).app n f) =
      SSet.yonedaEquiv (toDeltaZero (SSet.stdSimplex.obj n.unop) ≫ x) := by
  rw [sliceOver.proj_apply, toSliceOver_app_val, f.2.1]

/-- Functoriality of the right mapping space in `X`:
postcomposition with `F : X ⟶ Y` sends mapping-space simplices from
`x` to `y` to simplices from `x ≫ F` to `y ≫ F`. -/
def map {Y : SSet.{u}} (F : X ⟶ Y) :
    mappingSpaceRight X x y ⟶ mappingSpaceRight Y (x ≫ F) (y ≫ F) where
  app n := ↾fun f => ⟨f.1 ≫ F, by
    constructor
    · rw [← Category.assoc, f.2.1, Category.assoc]
    · rw [← Category.assoc, f.2.2]⟩
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    change ((SSet.join.map (SSet.stdSimplex.map α.unop)).app Δ[0] ≫ f.1) ≫ F =
      (SSet.join.map (SSet.stdSimplex.map α.unop)).app Δ[0] ≫ (f.1 ≫ F)
    rw [Category.assoc]

/-- Simplices of the right mapping space map by
postcomposition. -/
@[simp]
lemma map_app_val {Y : SSet.{u}} (F : X ⟶ Y) {n : SimplexCategoryᵒᵖ}
    (f : (mappingSpaceRight X x y).obj n) :
    ((map X x y F).app n f).1 = f.1 ≫ F :=
  rfl

/-- Functoriality in `X` is compatible with the maps to the
over-slices. -/
@[reassoc (attr := simp)]
lemma map_toSliceOver {Y : SSet.{u}} (F : X ⟶ Y) :
    map X x y F ≫ toSliceOver Y (x ≫ F) (y ≫ F) =
      toSliceOver X x y ≫ sliceOver.map X y F := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro f
  apply Subtype.ext
  simp only [NatTrans.comp_app, types_comp_apply, toSliceOver_app_val,
    map_app_val, sliceOver.map_app_val]

/-- Functoriality in `X` preserves identities. -/
@[simp]
lemma map_id : map X x y (𝟙 X) = 𝟙 (mappingSpaceRight X x y) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro f
  apply Subtype.ext
  simp only [map_app_val, NatTrans.id_app, types_id_apply, Category.comp_id]

/-- Functoriality in `X` preserves composition. -/
@[simp]
lemma map_comp {Y Z : SSet.{u}} (F : X ⟶ Y) (G : Y ⟶ Z) :
    map X x y (F ≫ G) = map X x y F ≫ map Y (x ≫ F) (y ≫ F) G := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro f
  apply Subtype.ext
  simp only [NatTrans.comp_app, types_comp_apply, map_app_val, Category.assoc]

/-- Transporting along `SSet.joinStdSimplexIso n 0`, the
`n`-simplices of `mappingSpaceRight X x y` are the `(n + 1)`-simplices
of `X` whose restriction along the front face `frontInclusion n` is
constantly `x` and whose restriction along `rightVertex n` is
`y`. -/
def simplexEquivSucc (n : ℕ) :
    (mappingSpaceRight X x y).obj (op ⦋n⦌) ≃
      { σ : (Δ[n + 1] : SSet.{u}) ⟶ X //
        frontInclusion n ≫ σ = toDeltaZero Δ[n] ≫ x ∧
          rightVertex n ≫ σ = y } where
  toFun f := ⟨(SSet.joinStdSimplexIso n 0).inv ≫ f.1, by
    constructor
    · rw [frontInclusion, Category.assoc,
        ← Category.assoc (SSet.joinStdSimplexIso n 0).hom
          (SSet.joinStdSimplexIso n 0).inv f.1,
        Iso.hom_inv_id, Category.id_comp]
      exact f.2.1
    · rw [rightVertex, Category.assoc,
        ← Category.assoc (SSet.joinStdSimplexIso n 0).hom
          (SSet.joinStdSimplexIso n 0).inv f.1,
        Iso.hom_inv_id, Category.id_comp]
      exact f.2.2⟩
  invFun σ := ⟨(SSet.joinStdSimplexIso n 0).hom ≫ σ.1, by
    constructor
    · rw [← Category.assoc]
      exact σ.2.1
    · rw [← Category.assoc]
      exact σ.2.2⟩
  left_inv f := by
    apply Subtype.ext
    change (SSet.joinStdSimplexIso n 0).hom ≫
        ((SSet.joinStdSimplexIso n 0).inv ≫ f.1) = f.1
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  right_inv σ := by
    apply Subtype.ext
    change (SSet.joinStdSimplexIso n 0).inv ≫
        ((SSet.joinStdSimplexIso n 0).hom ≫ σ.1) = σ.1
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end mappingSpaceRight

/-- The left mapping space `Hom^L_X(x, y)` between two vertices of
`X`: the fiber of `sliceUnder.proj X x : sliceUnder X x ⟶ X` at `y`,
defined directly by its simplices. An `n`-simplex is a map
`f : Δ[0] ⋆ Δ[n] ⟶ X` with both endpoint restrictions fixed: the
left restriction is `x` and the right restriction is the constant
simplex at `y`. -/
def mappingSpaceLeft (X : SSet.{u}) (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    SSet.{u} where
  obj n :=
    { f : (Δ[0] : SSet.{u}) ⋆ SSet.stdSimplex.obj n.unop ⟶ X //
      SSet.joinInl Δ[0] (SSet.stdSimplex.obj n.unop) ≫ f = x ∧
        SSet.joinInr Δ[0] (SSet.stdSimplex.obj n.unop) ≫ f =
          toDeltaZero (SSet.stdSimplex.obj n.unop) ≫ y }
  map α := ↾fun f =>
    ⟨(SSet.join.obj Δ[0]).map (SSet.stdSimplex.map α.unop) ≫ f.1, by
      constructor
      · rw [← Category.assoc, SSet.joinInl_comp_map]
        exact f.2.1
      · have hterm : SSet.stdSimplex.map α.unop ≫ toDeltaZero _ =
            toDeltaZero _ :=
          toDeltaZero_eq _
        rw [← Category.assoc, ← SSet.map_comp_joinInr, Category.assoc,
          f.2.2, ← Category.assoc, hterm]⟩
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    simp
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    simp [Category.assoc]

namespace mappingSpaceLeft

variable (X : SSet.{u}) (x y : (Δ[0] : SSet.{u}) ⟶ X)

/-- The `n`-simplices of `mappingSpaceLeft X x y` are definitionally
the maps `Δ[0] ⋆ Δ[n] ⟶ X` with both endpoint restrictions fixed. -/
def simplexEquiv (n : ℕ) :
    (mappingSpaceLeft X x y).obj (op ⦋n⦌) ≃
      { f : (Δ[0] : SSet.{u}) ⋆ Δ[n] ⟶ X //
        SSet.joinInl Δ[0] Δ[n] ≫ f = x ∧
          SSet.joinInr Δ[0] Δ[n] ≫ f = toDeltaZero Δ[n] ≫ y } :=
  Equiv.refl _

/-- The left endpoint condition on a simplex of the left mapping
space: its left restriction is `x`. -/
@[simp]
lemma condition_left {n : SimplexCategoryᵒᵖ}
    (f : (mappingSpaceLeft X x y).obj n) :
    SSet.joinInl Δ[0] (SSet.stdSimplex.obj n.unop) ≫ f.1 = x :=
  f.2.1

/-- The right endpoint condition on a simplex of the left mapping
space: its right restriction is constantly `y`. -/
@[simp]
lemma condition_right {n : SimplexCategoryᵒᵖ}
    (f : (mappingSpaceLeft X x y).obj n) :
    SSet.joinInr Δ[0] (SSet.stdSimplex.obj n.unop) ≫ f.1 =
      toDeltaZero (SSet.stdSimplex.obj n.unop) ≫ y :=
  f.2.2

/-- The simplicial operators on `mappingSpaceLeft X x y` act by
precomposition with joins of simplicial operators. -/
@[simp]
lemma map_val {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (f : (mappingSpaceLeft X x y).obj n) :
    ((mappingSpaceLeft X x y).map α f).1 =
      (SSet.join.obj Δ[0]).map (SSet.stdSimplex.map α.unop) ≫ f.1 :=
  rfl

/-- The canonical map from the left mapping space to the under-slice
at `x`, forgetting the fixed target. -/
def toSliceUnder : mappingSpaceLeft X x y ⟶ sliceUnder X x where
  app n := ↾fun f => ⟨f.1, f.2.1⟩
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    change (SSet.join.obj Δ[0]).map (SSet.stdSimplex.map α.unop) ≫ f.1 =
      (SSet.join.obj Δ[0]).map (SSet.stdSimplex.map α.unop) ≫ f.1
    rfl

/-- `toSliceUnder` does not change the underlying join map. -/
@[simp]
lemma toSliceUnder_app_val {n : SimplexCategoryᵒᵖ}
    (f : (mappingSpaceLeft X x y).obj n) :
    ((toSliceUnder X x y).app n f).1 = f.1 :=
  rfl

/-- The fiber condition: the free (target) endpoint of a simplex of
the left mapping space, read through the under-slice projection, is
the constant simplex at `y`. This is the element-level statement
that `mappingSpaceLeft X x y` is the fiber of
`sliceUnder.proj X x` at `y`. -/
lemma proj_toSliceUnder_apply {n : SimplexCategoryᵒᵖ}
    (f : (mappingSpaceLeft X x y).obj n) :
    (sliceUnder.proj X x).app n ((toSliceUnder X x y).app n f) =
      SSet.yonedaEquiv (toDeltaZero (SSet.stdSimplex.obj n.unop) ≫ y) := by
  rw [sliceUnder.proj_apply, toSliceUnder_app_val, f.2.2]

/-- Functoriality of the left mapping space in `X`:
postcomposition with `F : X ⟶ Y` sends mapping-space simplices from
`x` to `y` to simplices from `x ≫ F` to `y ≫ F`. -/
def map {Y : SSet.{u}} (F : X ⟶ Y) :
    mappingSpaceLeft X x y ⟶ mappingSpaceLeft Y (x ≫ F) (y ≫ F) where
  app n := ↾fun f => ⟨f.1 ≫ F, by
    constructor
    · rw [← Category.assoc, f.2.1]
    · rw [← Category.assoc, f.2.2, Category.assoc]⟩
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    change ((SSet.join.obj Δ[0]).map (SSet.stdSimplex.map α.unop) ≫ f.1) ≫ F =
      (SSet.join.obj Δ[0]).map (SSet.stdSimplex.map α.unop) ≫ (f.1 ≫ F)
    rw [Category.assoc]

/-- Simplices of the left mapping space map by
postcomposition. -/
@[simp]
lemma map_app_val {Y : SSet.{u}} (F : X ⟶ Y) {n : SimplexCategoryᵒᵖ}
    (f : (mappingSpaceLeft X x y).obj n) :
    ((map X x y F).app n f).1 = f.1 ≫ F :=
  rfl

/-- Functoriality in `X` is compatible with the maps to the
under-slices. -/
@[reassoc (attr := simp)]
lemma map_toSliceUnder {Y : SSet.{u}} (F : X ⟶ Y) :
    map X x y F ≫ toSliceUnder Y (x ≫ F) (y ≫ F) =
      toSliceUnder X x y ≫ sliceUnder.map X x F := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro f
  apply Subtype.ext
  simp only [NatTrans.comp_app, types_comp_apply, toSliceUnder_app_val,
    map_app_val, sliceUnder.map_app_val]

/-- Functoriality in `X` preserves identities. -/
@[simp]
lemma map_id : map X x y (𝟙 X) = 𝟙 (mappingSpaceLeft X x y) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro f
  apply Subtype.ext
  simp only [map_app_val, NatTrans.id_app, types_id_apply, Category.comp_id]

/-- Functoriality in `X` preserves composition. -/
@[simp]
lemma map_comp {Y Z : SSet.{u}} (F : X ⟶ Y) (G : Y ⟶ Z) :
    map X x y (F ≫ G) = map X x y F ≫ map Y (x ≫ F) (y ≫ F) G := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro f
  apply Subtype.ext
  simp only [NatTrans.comp_app, types_comp_apply, map_app_val, Category.assoc]

/-- Transporting along `SSet.joinStdSimplexIso 0 n`, the
`n`-simplices of `mappingSpaceLeft X x y` are the `(n + 1)`-simplices
of `X` whose restriction along `leftVertex n` is `x` and whose
restriction along the back face `backInclusion n` is constantly
`y`. -/
def simplexEquivSucc (n : ℕ) :
    (mappingSpaceLeft X x y).obj (op ⦋n⦌) ≃
      { σ : (Δ[0 + n + 1] : SSet.{u}) ⟶ X //
        leftVertex n ≫ σ = x ∧
          backInclusion n ≫ σ = toDeltaZero Δ[n] ≫ y } where
  toFun f := ⟨(SSet.joinStdSimplexIso 0 n).inv ≫ f.1, by
    constructor
    · rw [leftVertex, Category.assoc,
        ← Category.assoc (SSet.joinStdSimplexIso 0 n).hom
          (SSet.joinStdSimplexIso 0 n).inv f.1,
        Iso.hom_inv_id, Category.id_comp]
      exact f.2.1
    · rw [backInclusion, Category.assoc,
        ← Category.assoc (SSet.joinStdSimplexIso 0 n).hom
          (SSet.joinStdSimplexIso 0 n).inv f.1,
        Iso.hom_inv_id, Category.id_comp]
      exact f.2.2⟩
  invFun σ := ⟨(SSet.joinStdSimplexIso 0 n).hom ≫ σ.1, by
    constructor
    · rw [← Category.assoc]
      exact σ.2.1
    · rw [← Category.assoc]
      exact σ.2.2⟩
  left_inv f := by
    apply Subtype.ext
    change (SSet.joinStdSimplexIso 0 n).hom ≫
        ((SSet.joinStdSimplexIso 0 n).inv ≫ f.1) = f.1
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  right_inv σ := by
    apply Subtype.ext
    change (SSet.joinStdSimplexIso 0 n).inv ≫
        ((SSet.joinStdSimplexIso 0 n).hom ≫ σ.1) = σ.1
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end mappingSpaceLeft

/-! ## Transported endpoint identifications

The front face is the last face map (`SSet.frontInclusion_eq`),
via `SSet.joinInl_comp_joinStdSimplexIso_hom` from
`JoinProperties.lean`; the right vertex satisfies the face
relation `SSet.rightVertex_comp_δ_castSucc`, from naturality of
`SSet.joinStdSimplexIso` in the left variable, and its
completion `SSet.rightVertex_eq` by vertex pinning. -/

/-- The transported right vertex composed with a face map that
does not omit the last vertex is the transported right vertex
one dimension up. From naturality of `joinStdSimplexIso` in the
left variable, `SSet.tensorHomOf_δ_id`, and naturality of
`joinInr` in the left variable; notably this does not need the
identification of `rightVertex` with a standard vertex map. -/
theorem rightVertex_comp_δ_castSucc {n : ℕ} (j : Fin (n + 2)) :
    rightVertex.{u} n ≫ stdSimplex.δ j.castSucc =
      rightVertex.{u} (n + 1) := by
  have step1 : rightVertex.{u} n ≫ stdSimplex.δ j.castSucc =
      joinInr (Δ[n] : SSet.{u}) Δ[0] ≫
        ((joinStdSimplexIso.{u} n 0).hom ≫
          stdSimplex.map (AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ j) (𝟙 ⦋0⦌))) := by
    rw [rightVertex, stdSimplex_δ_eq_map, ← tensorHomOf_δ_id]
    exact Category.assoc _ _ _
  have step2 : joinInr (Δ[n] : SSet.{u}) Δ[0] ≫
        ((joinStdSimplexIso.{u} n 0).hom ≫
          stdSimplex.map (AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ j) (𝟙 ⦋0⦌))) =
      joinInr (Δ[n + 1] : SSet.{u}) Δ[0] ≫
        (joinStdSimplexIso.{u} (n + 1) 0).hom := by
    rw [← joinStdSimplexIso_natural_left (SimplexCategory.δ j),
      (Category.assoc (joinInr (Δ[n] : SSet.{u}) (Δ[0] : SSet.{u}))
        ((join.{u}.map (stdSimplex.map (SimplexCategory.δ j))).app
          (Δ[0] : SSet.{u}))
        (joinStdSimplexIso.{u} (n + 1) 0).hom).symm, joinInr_comp_map]
  exact step1.trans step2

/-- **`frontInclusion` is the last face map**: the transported
left endpoint inclusion `SSet.frontInclusion n : Δ[n] ⟶ Δ[n + 1]`
is `stdSimplex.δ (Fin.last (n + 1))`. Via
`SSet.joinInl_comp_joinStdSimplexIso_hom` and `SSet.inl'_eq_δ_last`
(from `JoinProperties.lean`). -/
theorem frontInclusion_eq (n : ℕ) :
    frontInclusion.{u} n = stdSimplex.δ (Fin.last (n + 1)) := by
  rw [frontInclusion, joinInl_comp_joinStdSimplexIso_hom, inl'_eq_δ_last]
  exact (stdSimplex_δ_eq_map _).symm

/-! The transported right vertex is the last vertex, by the
pinning argument: `rightVertex n` is a vertex inclusion, and
the face relation `SSet.rightVertex_comp_δ_castSucc` above
forces the vertex to be the last one. -/

/-- Every vertex map into a standard simplex is
`stdSimplex.map` of a simplex-category hom (Yoneda). -/
private lemma exists_stdSimplex_map_eq_vertex (m : ℕ)
    (v : (Δ[0] : SSet.{u}) ⟶ Δ[m]) :
    ∃ φ : ⦋0⦌ ⟶ ⦋m⦌, v = stdSimplex.map φ := by
  refine ⟨stdSimplex.objEquiv (yonedaEquiv v), ?_⟩
  apply yonedaEquiv.injective
  rw [yonedaEquiv_map, Equiv.symm_apply_apply]

/-- `stdSimplex.map` is injective on homs out of `⦋0⦌`
(Yoneda). -/
private lemma stdSimplex_map_injective_vertex (m : ℕ) {φ ψ : ⦋0⦌ ⟶ ⦋m⦌}
    (h : (stdSimplex.map φ : (Δ[0] : SSet.{u}) ⟶ Δ[m]) = stdSimplex.map ψ) :
    φ = ψ := by
  have h2 := congrArg yonedaEquiv h
  rw [yonedaEquiv_map, yonedaEquiv_map] at h2
  exact stdSimplex.objEquiv.symm.injective h2

/-- If `Fin.succAbove j.castSucc k` is independent of `j`,
then `k` is the last vertex: the values at `j = 0` and at
`j.castSucc = k.succ` are `k.succ` and `k.castSucc`. -/
private lemma eq_last_of_succAbove_castSucc_eq {n : ℕ} (k : Fin (n + 2))
    (k' : Fin (n + 3))
    (h : ∀ j : Fin (n + 2), Fin.succAbove j.castSucc k = k') :
    k = Fin.last (n + 1) := by
  by_contra hk
  have hklt : k.val ≤ n := by
    have h1 : k.val < n + 2 := k.is_lt
    by_contra h2
    exact hk (Fin.ext (by simp [Fin.last]; omega))
  obtain ⟨j₂, hj₂⟩ : ∃ j : Fin (n + 2), j.castSucc = k.succ :=
    ⟨⟨k.val + 1, by omega⟩, Fin.ext (by simp [Fin.castSucc, Fin.succ])⟩
  have h0 := h 0
  rw [Fin.succAbove_castSucc_of_le _ _ (Fin.zero_le k)] at h0
  have h2 := h j₂
  rw [hj₂, Fin.succAbove_succ_self] at h2
  have heq : k.succ = k.castSucc := h0.trans h2.symm
  simp [Fin.ext_iff] at heq

/-- **The transported right vertex is `inr'`**: the right
endpoint inclusion of a join with `Δ[0]`, transported along
`SSet.joinStdSimplexIso n 0`, is the standard-simplex map of
`AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌`, i.e. the
last-vertex inclusion `Δ[0] ⟶ Δ[n + 1]`. This is step (1)
of TODO(T41-pi-identification) in
`ModelCategory/Joyal/MappingSpaceKanW.lean`, proved by
the vertex-pinning argument of the header rather than the
mirror Day-convolution chase. -/
theorem rightVertex_eq (n : ℕ) :
    rightVertex.{u} n =
      stdSimplex.map (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌) := by
  obtain ⟨φ, hφ⟩ := exists_stdSimplex_map_eq_vertex (n + 1) (rightVertex.{u} n)
  obtain ⟨φ', hφ'⟩ :=
    exists_stdSimplex_map_eq_vertex (n + 2) (rightVertex.{u} (n + 1))
  have hcomp : ∀ j : Fin (n + 2),
      φ ≫ SimplexCategory.δ j.castSucc = φ' := by
    intro j
    apply stdSimplex_map_injective_vertex (n + 2)
    have hmap : (stdSimplex.map (φ ≫ SimplexCategory.δ j.castSucc) :
        (Δ[0] : SSet.{u}) ⟶ Δ[n + 2]) =
        stdSimplex.map φ ≫ stdSimplex.map (SimplexCategory.δ j.castSucc) := by
      rw [Functor.map_comp]
    rw [hmap, ← hφ]
    have hδ : (stdSimplex.map (SimplexCategory.δ j.castSucc) :
        (Δ[n + 1] : SSet.{u}) ⟶ Δ[n + 2]) = stdSimplex.δ j.castSucc := rfl
    rw [hδ, rightVertex_comp_δ_castSucc, hφ']
  have hval : ∀ j : Fin (n + 2),
      Fin.succAbove j.castSucc (φ.toOrderHom 0) = φ'.toOrderHom 0 := by
    intro j
    have hj := congrArg (fun ψ : ⦋0⦌ ⟶ ⦋n + 2⦌ => ψ.toOrderHom 0) (hcomp j)
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
      Function.comp_apply] at hj
    have hδ : (SimplexCategory.δ j.castSucc).toOrderHom (φ.toOrderHom 0) =
        Fin.succAbove j.castSucc (φ.toOrderHom 0) := by
      simp [SimplexCategory.δ]
    rw [hδ] at hj
    exact hj
  have hlast : φ.toOrderHom 0 = Fin.last (n + 1) :=
    eq_last_of_succAbove_castSucc_eq _ _ hval
  have hφeq : φ = AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌ := by
    ext i : 3
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    rw [hlast, inr'_toOrderHom_zero]
  rw [hφ, hφeq]

/-- At level `0`, the transported right vertex is the face
map `stdSimplex.δ 0 : Δ[0] ⟶ Δ[1]` (the vertex `1`). -/
theorem rightVertex_zero : rightVertex.{u} 0 = stdSimplex.δ (0 : Fin 2) := by
  rw [rightVertex_eq]
  have h : AugmentedSimplexCategory.inr' ⦋0⦌ ⦋0⦌ =
      SimplexCategory.δ (0 : Fin 2) := by
    ext i : 3
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    rw [inr'_toOrderHom_zero]
    simp [SimplexCategory.δ]
  rw [h]
  rfl

/-! ### Full subcomplexes -/

/-- The induced map on naive (left) mapping spaces of a full
subcomplex inclusion is injective on simplices in every degree:
mapping-space simplices are join maps postcomposed with the
monomorphism `(Subcomplex.full V).ι`. Surjectivity onto the mapping
space of `X` between vertices of the full subcomplex — the
statement that the left mapping spaces of a full simplicial subset
agree with those of the ambient simplicial set — is blocked by the
vertex-identification issue recorded in the file header. -/
theorem mappingSpaceLeft_map_full_ι_app_injective {X : SSet.{u}}
    {V : Set (X _⦋0⦌)} (a b : (Δ[0] : SSet.{u}) ⟶ (Subcomplex.full V : SSet.{u}))
    (n : ℕ) :
    Function.Injective
      ((mappingSpaceLeft.map (Subcomplex.full V : SSet.{u}) a b
        (Subcomplex.full V).ι).app (op ⦋n⦌)) := by
  intro φ ψ h
  apply Subtype.ext
  have hval := congrArg Subtype.val h
  simp only [mappingSpaceLeft.map_app_val] at hval
  exact (cancel_mono (Subcomplex.full V).ι).mp hval

/-- The induced map on right mapping spaces of a full subcomplex
inclusion is injective on simplices in every degree; compare
`SSet.mappingSpaceLeft_map_full_ι_app_injective`. -/
theorem mappingSpaceRight_map_full_ι_app_injective {X : SSet.{u}}
    {V : Set (X _⦋0⦌)} (a b : (Δ[0] : SSet.{u}) ⟶ (Subcomplex.full V : SSet.{u}))
    (n : ℕ) :
    Function.Injective
      ((mappingSpaceRight.map (Subcomplex.full V : SSet.{u}) a b
        (Subcomplex.full V).ι).app (op ⦋n⦌)) := by
  intro φ ψ h
  apply Subtype.ext
  have hval := congrArg Subtype.val h
  simp only [mappingSpaceRight.map_app_val] at hval
  exact (cancel_mono (Subcomplex.full V).ι).mp hval

end SSet

end
