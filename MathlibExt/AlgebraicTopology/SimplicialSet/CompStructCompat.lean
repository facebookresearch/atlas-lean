/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
See NOTICE in the repository root for the original Mathlib attribution.
-/

module

-- BACKPORT: Opposite and truncation-conversion APIs from Mathlib PR #42435,
-- head `e09070f786c9fc0a688e6239d71230b618b045ff`,
-- `Mathlib/AlgebraicTopology/SimplicialSet/CompStruct.lean`,
-- blob `4d0cc316cfe55c9021a59dca3a16b6bbcf6838bd`.
-- Current-pin comparison and removal conditions: `BACKPORTS.md`.

public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.Op

/-!
# Opposite edges and composition triangles

Order reversal exchanges the endpoints of an edge and reverses the two composable sides of its
triangle. The conversions retain the original edge or simplex, commute with opposite and
unopposite, and preserve the two-truncation round trips for arbitrary simplicial sets. The base
edge and triangle types come from the pinned upstream module.

The compatibility scope against Mathlib 4.35.0 (`56a005855ea17e0b0958f73ec801ae140b0a1679`) and
its removal conditions are recorded in `BACKPORTS.md`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped Simplicial

namespace SSet

variable {X : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}

namespace Edge

@[simp]
lemma toTruncated_ofTruncated (e : ((truncation 2).obj X).Edge x₀ x₁) :
    (ofTruncated e).toTruncated = e := rfl

@[simp]
lemma ofTruncated_toTruncated (e : X.Edge x₀ x₁) :
    ofTruncated e.toTruncated = e := rfl

/-- The opposite of an edge. -/
def op (e : Edge x₀ x₁) :
    Edge (opObjEquiv.symm x₁) (opObjEquiv.symm x₀) :=
  Edge.mk (opObjEquiv.symm e.edge) (by simp) (by simp)

@[simp]
lemma op_edge (e : Edge x₀ x₁) :
    e.op.edge = opObjEquiv.symm e.edge := rfl

/-- The edge obtained from an edge in the opposite simplicial set. -/
def unop {x₀ x₁ : X.op _⦋0⦌} (e : Edge x₀ x₁) :
    Edge (opObjEquiv x₁) (opObjEquiv x₀) :=
  Edge.mk (opObjEquiv e.edge) (by simp [δ_opObjEquiv]) (by simp [δ_opObjEquiv])

@[simp]
lemma unop_edge {x₀ x₁ : X.op _⦋0⦌} (e : Edge x₀ x₁) :
    e.unop.edge = opObjEquiv e.edge := rfl

@[simp]
lemma unop_op (e : Edge x₀ x₁) :
    e.op.unop = e := rfl

@[simp]
lemma op_unop {x₀ x₁ : X.op _⦋0⦌} (e : Edge x₀ x₁) :
    e.unop.op = e := rfl

namespace CompStruct

/-- The `CompStruct` in `X.op` that is deduced from a `CompStruct` in `X`. -/
def op {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (h : CompStruct e₀₁ e₁₂ e₀₂) :
    CompStruct e₁₂.op e₀₁.op e₀₂.op :=
  CompStruct.mk (opObjEquiv.symm h.simplex) (by simp) (by simp) (by simp)

@[simp]
lemma op_simplex {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (h : CompStruct e₀₁ e₁₂ e₀₂) :
    h.op.simplex = opObjEquiv.symm h.simplex := rfl

/-- The `CompStruct` in `X` that is deduced from a `CompStruct` in `X.op`. -/
def unop {x₀ x₁ x₂ : X.op _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (h : CompStruct e₀₁ e₁₂ e₀₂) :
    CompStruct e₁₂.unop e₀₁.unop e₀₂.unop :=
  CompStruct.mk (opObjEquiv h.simplex) (by simp [δ_opObjEquiv])
    (by simp [δ_opObjEquiv]) (by simp [δ_opObjEquiv])

@[simp]
lemma unop_simplex {x₀ x₁ x₂ : X.op _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (h : CompStruct e₀₁ e₁₂ e₀₂) :
    h.unop.simplex = opObjEquiv h.simplex := rfl

end CompStruct

end Edge

end SSet
