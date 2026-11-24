/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceMapVertices
public import Mathlib.Order.Fin.Basic

/-!
# The original ordinal operator of every native necklace map

All consecutive original edges belong to the full native necklace.
Their actual images give the monotonicity of the entire original vertex
map. Every simplex then reads back the same original ordinal operator.
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

/-- The complete original consecutive edge at the supplied original index. -/
def adjacentEdge {n : ℕ} (i : Fin n) : (Δ[n] : SSet.{u}) _⦋1⦌ :=
  stdSimplex.objMk (n := ⦋n⦌) (m := op ⦋1⦌)
    (show Fin 2 →o Fin (n + 1) from
    ⟨fun j => ⟨i.val + j.val, by have hi := i.isLt; have hj := j.isLt; omega⟩,
      fun a b hab => by
        change i.val + a.val ≤ i.val + b.val
        exact Nat.add_le_add_left hab i.val⟩)

/-- The original first vertex of the consecutive edge. -/
theorem adjacentEdge_zero {n : ℕ} (i : Fin n) :
    adjacentEdge.{u} i 0 = i.castSucc := Fin.ext rfl

/-- The original last vertex of the consecutive edge. -/
theorem adjacentEdge_one {n : ℕ} (i : Fin n) :
    adjacentEdge.{u} i 1 = i.succ := Fin.ext rfl

/-- Every complete original consecutive edge crosses none of the supplied necklace joints. -/
theorem adjacentEdge_mem {n : ℕ} (J : Finset (Fin (n + 1))) (i : Fin n) :
    adjacentEdge.{u} i ∈ (complex J).obj (op ⦋1⦌) := by
  apply (mem_complex_iff _ _).mpr
  intro j _
  by_cases h : j ≤ i.castSucc
  · apply Or.inr
    intro a
    apply h.trans
    change i.val ≤ i.val + a.val
    omega
  · apply Or.inl
    intro a
    have hj : i.val < j.val := not_le.mp h
    have ha := a.isLt
    change i.val + a.val ≤ j.val
    omega

/-- The entire original vertex map of any actual native simplicial necklace map is monotone. -/
theorem vertexImage_monotone {T U : Data} (f : T.object.{u} ⟶ U.object.{u}) :
    Monotone (vertexImage f) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  let s : T.object _⦋1⦌ := ⟨adjacentEdge i, adjacentEdge_mem T.joints i⟩
  calc
    vertexImage f i.castSucc = (f.app (op ⦋1⦌) s).val 0 :=
      (simplex_vertex_image f s 0).symm
    _ ≤ (f.app (op ⦋1⦌) s).val 1 :=
      stdSimplex.monotone_apply (f.app (op ⦋1⦌) s).val (by decide : (0 : Fin 2) ≤ 1)
    _ = vertexImage f i.succ := simplex_vertex_image f s 1

/-- The actual original ordinal operator of the same full native simplicial map. -/
def mapOperator {T U : Data} (f : T.object.{u} ⟶ U.object.{u}) :
    ⦋T.dimension⦌ ⟶ ⦋U.dimension⦌ :=
  SimplexCategory.Hom.mk ⟨vertexImage f, vertexImage_monotone f⟩

/-- The complete original map reads back its literal whole standard-simplex operator. -/
theorem mapOperator_readback {T U : Data} (f : T.object.{u} ⟶ U.object.{u}) :
    f ≫ (complex U.joints).ι =
      (complex T.joints).ι ≫ SSet.stdSimplex.map (mapOperator f) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro i
  exact simplex_vertex_image f s i

end SSet.OriginalNecklace
