/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.WalkOverlap

@[expose] public section

open CerednikDrinfeld.Mumford

universe u

/-- Consumer with the original binders: the overlap is additive in the first walk. -/
private theorem exactSource {W : Type} [DecidableEq W] {𝒯 : SimpleGraph W} {u v w u' v' : W}
    (P₁ : 𝒯.Walk u v) (P₂ : 𝒯.Walk v w) (Q : 𝒯.Walk u' v') :
    walkOverlap (P₁.append P₂) Q = walkOverlap P₁ Q + walkOverlap P₂ Q :=
  walkOverlap_append_left P₁ P₂ Q

/-- Higher-universe consumer: reversing the second walk negates the overlap. -/
example {W : Type (u + 1)} [DecidableEq W] {𝒯 : SimpleGraph W} {u v u' v' : W}
    (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') : walkOverlap P Q.reverse = -walkOverlap P Q :=
  walkOverlap_reverse_right P Q

/-- The one-edge walk `false → true` in the complete graph on `Bool`. -/
private def edgeWalk : (⊤ : SimpleGraph Bool).Walk false true :=
  .cons (by simp) .nil

/-- A one-edge walk overlaps itself once and its reverse with sign `-1`; the sign records
orientation. -/
example : walkOverlap edgeWalk edgeWalk = 1 ∧ walkOverlap edgeWalk edgeWalk.reverse = -1 := by
  refine ⟨by decide, ?_⟩
  rw [walkOverlap_reverse_right]
  decide

/-- Boundary: the empty walk has overlap `0` with everything. -/
example : walkOverlap (SimpleGraph.Walk.nil : (⊤ : SimpleGraph Bool).Walk true true) edgeWalk = 0 :=
  walkOverlap_nil_left true edgeWalk
