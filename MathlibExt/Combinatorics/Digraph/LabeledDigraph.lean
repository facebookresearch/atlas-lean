/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic.Ext

/-!
# Labeled directed graphs

A generic labeled directed graph, represented by separate vertex, edge, and
label types together with source, target, and label maps, plus the generic
endpoint-restriction operation: restrict to a vertex predicate, keeping
exactly the edges whose source and target both satisfy it.

This is a concrete edge-type bundle rather than Mathlib's `Quiver`: clients
such as Young-graph pruning restrict the *edge type itself* to edges whose
two endpoints are retained, a total-space restriction, whereas
`Quiver.Subquiver` selects Hom-families over a fixed vertex type and
`Quiver.Total` has no first-class label map. Labels here are edge data, so
the bundle keeps `src`, `tgt`, and `label` as the primitive interface.
-/

namespace MetaMathlibExt

@[expose] public section

/-- A labeled directed graph, represented by its vertex and edge types together
with source, target, and label maps. -/
structure LabeledDigraph (V E L : Type _) where
  src : E → V
  tgt : E → V
  label : E → L

/-- Extensionality for labeled digraphs: two bundles with the same source,
target, and label maps are equal. -/
@[ext]
theorem LabeledDigraph.ext {V E L : Type _} {G H : LabeledDigraph V E L}
    (hsrc : G.src = H.src) (htgt : G.tgt = H.tgt) (hlabel : G.label = H.label) :
    G = H := by
  cases G
  cases H
  simp_all

/-- Restrict a labeled directed graph to the vertices satisfying `p`,
keeping exactly the edges whose source and target both satisfy `p`. -/
def LabeledDigraph.restrict {V E L : Type _} (G : LabeledDigraph V E L)
    (p : V → Prop) :
    LabeledDigraph { v : V // p v } { e : E // p (G.src e) ∧ p (G.tgt e) } L where
  src e := ⟨G.src e.val, e.property.1⟩
  tgt e := ⟨G.tgt e.val, e.property.2⟩
  label e := G.label e.val

/-- The source of a restricted edge: the ambient source, in the subtype. -/
@[simp]
theorem LabeledDigraph.restrict_src {V E L : Type _} (G : LabeledDigraph V E L)
    (p : V → Prop) (e : { e : E // p (G.src e) ∧ p (G.tgt e) }) :
    ((G.restrict p).src e).val = G.src e.val :=
  rfl

/-- The target of a restricted edge: the ambient target, in the subtype. -/
@[simp]
theorem LabeledDigraph.restrict_tgt {V E L : Type _} (G : LabeledDigraph V E L)
    (p : V → Prop) (e : { e : E // p (G.src e) ∧ p (G.tgt e) }) :
    ((G.restrict p).tgt e).val = G.tgt e.val :=
  rfl

/-- The label of a restricted edge is its ambient label. -/
@[simp]
theorem LabeledDigraph.restrict_label {V E L : Type _} (G : LabeledDigraph V E L)
    (p : V → Prop) (e : { e : E // p (G.src e) ∧ p (G.tgt e) }) :
    (G.restrict p).label e = G.label e.val :=
  rfl

end

end MetaMathlibExt
