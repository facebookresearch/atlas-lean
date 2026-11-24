/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Arnoud van der Leer
-/
module

-- BACKPORT: Extracted from PR `leanprover-community/mathlib4#42435` head
-- `e09070f786c9fc0a688e6239d71230b618b045ff`, file
-- `Mathlib/AlgebraicTopology/SimplicialSet/CompStruct.lean`, blob
-- `4d0cc316cfe55c9021a59dca3a16b6bbcf6838bd`.
-- See `BACKPORTS.md` for adaptations and upgrade-removal steps.

public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.Op

/-!
# Edge and comp-structure opposite compatibility for Lean 4.33

This file backports the opposite involution API for edges and composition
structures introduced in PR #42435 which is absent from the pinned Mathlib
`v4.33.0` (`db584cd`).

## Source

* PR: leanprover-community/mathlib4#42435
* PR head: `e09070f786c9fc0a688e6239d71230b618b045ff`
* File: `Mathlib/AlgebraicTopology/SimplicialSet/CompStruct.lean`
* Blob: `4d0cc316cfe55c9021a59dca3a16b6bbcf6838bd`
* Upstream authors: Joël Riou, Arnoud van der Leer (copyright header in upstream source)
* Base: canonical KQ2 `10d0a5123c58a6c79020ae9490f71d906b7cd3bf`

## Ported declarations

Exactly twelve declarations, preserving upstream statements, attributes,
namespaces, and proof bodies verbatim where they elaborate on the 4.33 pin:

* `SSet.Edge.toTruncated_ofTruncated` (`@[simp]`)
* `SSet.Edge.ofTruncated_toTruncated` (`@[simp]`)
* `SSet.Edge.op`
* `SSet.Edge.op_edge` (`@[simp]`)
* `SSet.Edge.unop`
* `SSet.Edge.unop_edge` (`@[simp]`)
* `SSet.Edge.unop_op` (`@[simp]`)
* `SSet.Edge.op_unop` (`@[simp]`)
* `SSet.Edge.CompStruct.op`
* `SSet.Edge.CompStruct.op_simplex` (`@[simp]`)
* `SSet.Edge.CompStruct.unop`
* `SSet.Edge.CompStruct.unop_simplex` (`@[simp]`)

All proofs use only `Edge.mk`, `opObjEquiv`, `opObjEquiv.symm`,
`δ_opObjEquiv`, `CompStruct.mk`, and `simp`/`rfl` already present on the pin.

## Adaptations for 4.33

* Imports pinned `Mathlib.AlgebraicTopology.SimplicialSet.CompStruct` for the base
  `Edge`, `CompStruct`, `id`, `mk`, etc., and pinned
  `Mathlib.AlgebraicTopology.SimplicialSet.Op` for `opObjEquiv`, `op_δ`,
  `δ_opObjEquiv`, etc.
* No signature or tactic changes; `δ_opObjEquiv` exists on the 4.33 pin, so
  `by simp [δ_opObjEquiv]` elaborates unchanged.
* Universe reduced to `u` only (upstream uses `v u`); declarations only need `u`.

## Removal rule

Delete this module `MathlibExt/AlgebraicTopology/SimplicialSet/CompStructCompat.lean`
and switch any imports of it to
`Mathlib.AlgebraicTopology.SimplicialSet.CompStruct`
once the pinned Mathlib provides all twelve declarations listed above.
Do not retain local copies that would collide with upstream.
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
