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

/-- **Labeled directed graph.** A labeled directed graph with vertex set $V$, edge set $E$ and
label set $L$ consists of a source map $s : E \to V$, a target map $t : E \to V$ and a label
map $\ell : E \to L$; the edge $e$ goes from $s(e)$ to $t(e)$ and carries the label $\ell(e)$.
Loops and parallel edges are allowed. -/
structure LabeledDigraph (V E L : Type _) where
  src : E → V
  tgt : E → V
  label : E → L

/-- **Extensionality for labeled directed graphs.** Two labeled directed graphs $G$ and $H$
with the same vertex set, edge set and label set are equal if they have the same source map,
the same target map and the same label map. -/
@[ext]
theorem LabeledDigraph.ext {V E L : Type _} {G H : LabeledDigraph V E L}
    (hsrc : G.src = H.src) (htgt : G.tgt = H.tgt) (hlabel : G.label = H.label) :
    G = H := by
  cases G
  cases H
  simp_all

/-- **Restriction of a labeled directed graph.** Let $G$ be a labeled directed graph with
vertex set $V$ and label set $L$, and let $p$ be a predicate on $V$. The restriction of $G$ to
$p$ is the labeled directed graph with label set $L$ whose vertices are the vertices $v$ of $G$
with $p(v)$, whose edges are the edges of $G$ whose source and target both satisfy $p$, and in
which each edge has the same source, target and label as in $G$. -/
def LabeledDigraph.restrict {V E L : Type _} (G : LabeledDigraph V E L)
    (p : V → Prop) :
    LabeledDigraph { v : V // p v } { e : E // p (G.src e) ∧ p (G.tgt e) } L where
  src e := ⟨G.src e.val, e.property.1⟩
  tgt e := ⟨G.tgt e.val, e.property.2⟩
  label e := G.label e.val

/-- **Source of an edge in a restriction.** Let $G$ be a labeled directed graph, $p$ a predicate
on its vertices, and $e$ an edge of $G$ whose source and target satisfy $p$, viewed as an edge of
the restriction of $G$ to $p$. The source of $e$ in the restriction, viewed as a vertex of $G$,
is the source of $e$ in $G$. -/
@[simp]
theorem LabeledDigraph.restrict_src {V E L : Type _} (G : LabeledDigraph V E L)
    (p : V → Prop) (e : { e : E // p (G.src e) ∧ p (G.tgt e) }) :
    ((G.restrict p).src e).val = G.src e.val :=
  rfl

/-- **Target of an edge in a restriction.** Let $G$ be a labeled directed graph, $p$ a predicate
on its vertices, and $e$ an edge of $G$ whose source and target satisfy $p$, viewed as an edge of
the restriction of $G$ to $p$. The target of $e$ in the restriction, viewed as a vertex of $G$,
is the target of $e$ in $G$. -/
@[simp]
theorem LabeledDigraph.restrict_tgt {V E L : Type _} (G : LabeledDigraph V E L)
    (p : V → Prop) (e : { e : E // p (G.src e) ∧ p (G.tgt e) }) :
    ((G.restrict p).tgt e).val = G.tgt e.val :=
  rfl

/-- **Label of an edge in a restriction.** Let $G$ be a labeled directed graph, $p$ a predicate
on its vertices, and $e$ an edge of $G$ whose source and target satisfy $p$, viewed as an edge of
the restriction of $G$ to $p$. The label of $e$ in the restriction is its label in $G$. -/
@[simp]
theorem LabeledDigraph.restrict_label {V E L : Type _} (G : LabeledDigraph V E L)
    (p : V → Prop) (e : { e : E // p (G.src e) ∧ p (G.tgt e) }) :
    (G.restrict p).label e = G.label e.val :=
  rfl

end

end MetaMathlibExt
