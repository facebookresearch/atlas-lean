/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceCategory

/-!
# Every original native necklace-map vertex and simplex

The same actual native simplicial map determines its original ordinal
vertex images. Every full original simplex reads those same images at
every vertex; no categorical or weak-map outcome is assumed.
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

/-- The same original vertex of the native whole necklace. -/
def vertexSimplex (T : Data) (i : Fin (T.dimension + 1)) :
    T.object.{u} _⦋0⦌ :=
  ⟨stdSimplex.obj₀Equiv.symm i, vertex_mem T.joints i⟩

/-- The same original ordinal image of a vertex under the actual whole simplicial map. -/
def vertexImage {T U : Data} (f : T.object.{u} ⟶ U.object.{u})
    (i : Fin (T.dimension + 1)) : Fin (U.dimension + 1) :=
  stdSimplex.obj₀Equiv ((f.app (op ⦋0⦌) (vertexSimplex T i)).val)

/-- The actual whole vertex prism follows the same original simplicial map. -/
theorem vertexMap_map {T U : Data} (f : T.object.{u} ⟶ U.object.{u})
    (i : Fin (T.dimension + 1)) :
    vertexMap T.joints i ≫ f = vertexMap U.joints (vertexImage f i) := by
  apply SSet.yonedaEquiv.injective
  apply Subtype.ext
  apply stdSimplex.obj₀Equiv.injective
  rfl

/-- Every complete original simplex vertex reads the actual same original vertex map. -/
theorem simplex_vertex_image {T U : Data} (f : T.object.{u} ⟶ U.object.{u})
    {d : ℕ} (s : T.object _⦋d⦌) (i : Fin (d + 1)) :
    (f.app (op ⦋d⦌) s).val i = vertexImage f (s.val i) := by
  let θ : op ⦋d⦌ ⟶ op ⦋0⦌ := (SimplexCategory.const ⦋0⦌ ⦋d⦌ i).op
  have hs : T.object.map θ s = vertexSimplex T (s.val i) := by
    apply Subtype.ext
    apply stdSimplex.ext
    intro j
    rfl
  have h := ConcreteCategory.congr_hom (f.naturality θ) s
  have h' := congrArg (fun a : U.object _⦋0⦌ => stdSimplex.obj₀Equiv a.val) h
  exact h'.symm.trans
    (congrArg (fun a : T.object _⦋0⦌ => stdSimplex.obj₀Equiv (f.app (op ⦋0⦌) a).val) hs)

/-- Whole original native maps are determined by all their same original vertex images. -/
theorem map_ext_vertices {T U : Data} {f g : T.object.{u} ⟶ U.object.{u}}
    (h : ∀ i, vertexImage f i = vertexImage g i) : f = g := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  exact (simplex_vertex_image f s i).trans
    ((h (s.val i)).trans (simplex_vertex_image g s i).symm)

/-- The complete actual vertex prism determines its same original ordinal label. -/
theorem vertexMap_injective (T : Data) :
    Function.Injective (vertexMap.{u} T.joints) := by
  intro i j h
  have he := congrArg
    (fun a : (Δ[0] : SSet.{u}) ⟶ T.object =>
      stdSimplex.obj₀Equiv (SSet.yonedaEquiv a).val) h
  exact he

namespace Morphism

/-- An original native ordinal morphism reads back its same actual ordinal vertex operator. -/
theorem vertexImage_map {T U : Data} (f : Morphism T U) (i : Fin (T.dimension + 1)) :
    vertexImage f.map.{u} i = f.operator.toOrderHom i := rfl

/-- The same complete native simplicial map retains its entire original necklace morphism. -/
theorem map_injective {T U : Data} :
    Function.Injective (map.{u} : Morphism T U → (T.object ⟶ U.object)) := by
  intro f g h
  apply Morphism.ext
  ext i : 3
  exact congrArg (fun a => vertexImage a i) h

end Morphism

end SSet.OriginalNecklace
