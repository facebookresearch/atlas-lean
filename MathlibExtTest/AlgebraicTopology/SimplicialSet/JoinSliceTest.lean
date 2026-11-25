/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSlice

/-!
# Tests for the join slices and mapping spaces

Consumer checks for `SSet.sliceOver`, `SSet.sliceUnder`,
`SSet.mappingSpaceRight` and `SSet.mappingSpaceLeft`:
the objects and their forgetful maps, the definitional simplex
characterizations, functoriality in `X`, the fiber conditions for the
mapping spaces, the `(n + 1)`-simplex descriptions obtained from
`SSet.joinStdSimplexIso` (including edges as `0`-simplices of the
slices), and injectivity of the induced mapping-space maps for
full-subcomplex inclusions.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.JoinSliceTest

variable (X Y : SSet.{u}) (x y : (Δ[0] : SSet.{u}) ⟶ X)

/-- The slices and mapping spaces as objects. -/
example : SSet.{u} := SSet.sliceOver X x

example : SSet.{u} := SSet.sliceUnder X x

example : SSet.{u} := SSet.mappingSpaceRight X x y

example : SSet.{u} := SSet.mappingSpaceLeft X x y

/-- The transported vertex and face maps. -/
example (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ Δ[n + 1] :=
  SSet.rightVertex.{u} n

example (n : ℕ) : (Δ[n] : SSet.{u}) ⟶ Δ[n + 1] :=
  SSet.frontInclusion.{u} n

example (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ Δ[0 + n + 1] :=
  SSet.leftVertex.{u} n

example (n : ℕ) : (Δ[n] : SSet.{u}) ⟶ Δ[0 + n + 1] :=
  SSet.backInclusion.{u} n

/-- Definitional simplex characterizations. -/
example (n : ℕ) :
    (SSet.sliceOver X x).obj (op ⦋n⦌) ≃
      { f : (Δ[n] : SSet.{u}) ⋆ Δ[0] ⟶ X //
        SSet.joinInr Δ[n] Δ[0] ≫ f = x } :=
  SSet.sliceOver.simplexEquiv X x n

example (n : ℕ) :
    (SSet.sliceUnder X x).obj (op ⦋n⦌) ≃
      { f : (Δ[0] : SSet.{u}) ⋆ Δ[n] ⟶ X //
        SSet.joinInl Δ[0] Δ[n] ≫ f = x } :=
  SSet.sliceUnder.simplexEquiv X x n

example (n : ℕ) :
    (SSet.mappingSpaceRight X x y).obj (op ⦋n⦌) ≃
      { f : (Δ[n] : SSet.{u}) ⋆ Δ[0] ⟶ X //
        SSet.joinInl Δ[n] Δ[0] ≫ f =
            SSet.toDeltaZero Δ[n] ≫ x ∧
          SSet.joinInr Δ[n] Δ[0] ≫ f = y } :=
  SSet.mappingSpaceRight.simplexEquiv X x y n

example (n : ℕ) :
    (SSet.mappingSpaceLeft X x y).obj (op ⦋n⦌) ≃
      { f : (Δ[0] : SSet.{u}) ⋆ Δ[n] ⟶ X //
        SSet.joinInl Δ[0] Δ[n] ≫ f = x ∧
          SSet.joinInr Δ[0] Δ[n] ≫ f =
            SSet.toDeltaZero Δ[n] ≫ y } :=
  SSet.mappingSpaceLeft.simplexEquiv X x y n

/-- Simplices of the slices satisfy their endpoint conditions, and
simplicial operators act by precomposition. -/
example {n : SimplexCategoryᵒᵖ} (f : (SSet.sliceOver X x).obj n) :
    SSet.joinInr (SSet.stdSimplex.obj n.unop) Δ[0] ≫ f.1 = x :=
  SSet.sliceOver.condition X x f

example {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (f : (SSet.sliceUnder X x).obj n) :
    ((SSet.sliceUnder X x).map α f).1 =
      (SSet.join.obj Δ[0]).map (SSet.stdSimplex.map α.unop) ≫ f.1 :=
  SSet.sliceUnder.map_val X x α f

/-- The forgetful maps and their element-level description. -/
example : SSet.sliceOver X x ⟶ X := SSet.sliceOver.proj X x

example : SSet.sliceUnder X x ⟶ X :=
  SSet.sliceUnder.proj X x

example {n : SimplexCategoryᵒᵖ} (f : (SSet.sliceOver X x).obj n) :
    (SSet.sliceOver.proj X x).app n f = SSet.yonedaEquiv
      (SSet.joinInl (SSet.stdSimplex.obj n.unop) Δ[0] ≫ f.1) :=
  SSet.sliceOver.proj_apply X x f

/-- Functoriality in `X`, compatible with the forgetful maps. -/
example (F : X ⟶ Y) :
    SSet.sliceOver X x ⟶ SSet.sliceOver Y (x ≫ F) :=
  SSet.sliceOver.map X x F

example (F : X ⟶ Y) :
    SSet.sliceUnder.map X x F ≫ SSet.sliceUnder.proj Y (x ≫ F) =
      SSet.sliceUnder.proj X x ≫ F :=
  SSet.sliceUnder.map_proj X x F

example : SSet.sliceOver.map X x (𝟙 X) =
    𝟙 (SSet.sliceOver X x) :=
  SSet.sliceOver.map_id X x

example {Z : SSet.{u}} (F : X ⟶ Y) (G : Y ⟶ Z) :
    SSet.mappingSpaceLeft.map X x y (F ≫ G) =
      SSet.mappingSpaceLeft.map X x y F ≫
        SSet.mappingSpaceLeft.map Y (x ≫ F) (y ≫ F) G :=
  SSet.mappingSpaceLeft.map_comp X x y F G

/-- The `(n + 1)`-simplex descriptions and edges as `0`-simplices. -/
example (n : ℕ) :
    (SSet.sliceOver X x).obj (op ⦋n⦌) ≃
      { σ : (Δ[n + 1] : SSet.{u}) ⟶ X //
        SSet.rightVertex.{u} n ≫ σ = x } :=
  SSet.sliceOver.simplexEquivSucc X x n

example (n : ℕ) :
    (SSet.sliceUnder X x).obj (op ⦋n⦌) ≃
      { σ : (Δ[0 + n + 1] : SSet.{u}) ⟶ X //
        SSet.leftVertex.{u} n ≫ σ = x } :=
  SSet.sliceUnder.simplexEquivSucc X x n

example :
    (SSet.sliceOver X x).obj (op ⦋0⦌) ≃
      { e : (Δ[1] : SSet.{u}) ⟶ X //
        SSet.rightVertex.{u} 0 ≫ e = x } :=
  SSet.sliceOver.zeroSimplexEquiv X x

example :
    (SSet.sliceUnder X x).obj (op ⦋0⦌) ≃
      { e : (Δ[1] : SSet.{u}) ⟶ X //
        SSet.leftVertex.{u} 0 ≫ e = x } :=
  SSet.sliceUnder.zeroSimplexEquiv X x

/-- The mapping spaces map to the slices and satisfy the fiber
conditions. -/
example : SSet.mappingSpaceRight X x y ⟶ SSet.sliceOver X y :=
  SSet.mappingSpaceRight.toSliceOver X x y

example : SSet.mappingSpaceLeft X x y ⟶
    SSet.sliceUnder X x :=
  SSet.mappingSpaceLeft.toSliceUnder X x y

example {n : SimplexCategoryᵒᵖ}
    (f : (SSet.mappingSpaceRight X x y).obj n) :
    (SSet.sliceOver.proj X y).app n
        ((SSet.mappingSpaceRight.toSliceOver X x y).app n f) =
      SSet.yonedaEquiv
        (SSet.toDeltaZero (SSet.stdSimplex.obj n.unop) ≫ x) :=
  SSet.mappingSpaceRight.proj_toSliceOver_apply X x y f

example {n : SimplexCategoryᵒᵖ}
    (f : (SSet.mappingSpaceLeft X x y).obj n) :
    (SSet.sliceUnder.proj X x).app n
        ((SSet.mappingSpaceLeft.toSliceUnder X x y).app n f) =
      SSet.yonedaEquiv
        (SSet.toDeltaZero (SSet.stdSimplex.obj n.unop) ≫ y) :=
  SSet.mappingSpaceLeft.proj_toSliceUnder_apply X x y f

/-- Simplices of the mapping spaces as `(n + 1)`-simplices. -/
example (n : ℕ) :
    (SSet.mappingSpaceRight X x y).obj (op ⦋n⦌) ≃
      { σ : (Δ[n + 1] : SSet.{u}) ⟶ X //
        SSet.frontInclusion.{u} n ≫ σ =
            SSet.toDeltaZero Δ[n] ≫ x ∧
          SSet.rightVertex.{u} n ≫ σ = y } :=
  SSet.mappingSpaceRight.simplexEquivSucc X x y n

example (n : ℕ) :
    (SSet.mappingSpaceLeft X x y).obj (op ⦋n⦌) ≃
      { σ : (Δ[0 + n + 1] : SSet.{u}) ⟶ X //
        SSet.leftVertex.{u} n ≫ σ = x ∧
          SSet.backInclusion.{u} n ≫ σ =
            SSet.toDeltaZero Δ[n] ≫ y } :=
  SSet.mappingSpaceLeft.simplexEquivSucc X x y n

/-- Functoriality of the mapping spaces is compatible with the maps
to the slices. -/
example (F : X ⟶ Y) :
    SSet.mappingSpaceRight.map X x y F ≫
        SSet.mappingSpaceRight.toSliceOver Y (x ≫ F) (y ≫ F) =
      SSet.mappingSpaceRight.toSliceOver X x y ≫
        SSet.sliceOver.map X y F :=
  SSet.mappingSpaceRight.map_toSliceOver X x y F

/-- At a standard simplex, the slices are inhabited by the
tautological simplices: the identity of `Δ[1]`, read through
`SSet.joinStdSimplexIso 0 0`, gives a `0`-simplex of the over-slice
of `Δ[1]` at its right vertex. -/
example :
    (SSet.sliceOver (Δ[1] : SSet.{u})
      (SSet.rightVertex.{u} 0)).obj (op ⦋0⦌) :=
  (SSet.sliceOver.simplexEquivSucc (Δ[1] : SSet.{u})
    (SSet.rightVertex.{u} 0) 0).symm ⟨𝟙 Δ[1], by simp⟩

/-- The induced map on left mapping spaces of a full subcomplex
inclusion is injective on `0`-simplices (edges). -/
example (V : Set (X _⦋0⦌))
    (a b : (Δ[0] : SSet.{u}) ⟶ (SSet.Subcomplex.full V : SSet.{u})) :
    Function.Injective
      ((SSet.mappingSpaceLeft.map (SSet.Subcomplex.full V : SSet.{u})
        a b (SSet.Subcomplex.full V).ι).app (op ⦋0⦌)) :=
  SSet.mappingSpaceLeft_map_full_ι_app_injective a b 0

/-- The induced map on right mapping spaces of a full subcomplex
inclusion is injective on simplices in every degree. -/
example (V : Set (X _⦋0⦌))
    (a b : (Δ[0] : SSet.{u}) ⟶ (SSet.Subcomplex.full V : SSet.{u}))
    (n : ℕ) :
    Function.Injective
      ((SSet.mappingSpaceRight.map (SSet.Subcomplex.full V : SSet.{u})
        a b (SSet.Subcomplex.full V).ι).app (op ⦋n⦌)) :=
  SSet.mappingSpaceRight_map_full_ι_app_injective a b n

end MathlibExtTest.AlgebraicTopology.SimplicialSet.JoinSliceTest

end
