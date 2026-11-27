/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Digraph.LabeledDigraph

/-!
# Young graph pruning

Young-specific retention/pruning for labeled digraphs: a node is retained
when it is a pivot node or precedes some pivot node, and the pruned graph is
the generic endpoint restriction (`LabeledDigraph.restrict`) to the retained
nodes. The generic graph bundle lives in
`MathlibExt/Combinatorics/Digraph/LabeledDigraph.lean`.

This module does not construct Kendrick's parameter-specific graph `Y(g, k)`;
clients supply the ambient labeled graph, pivot predicate, and precedence relation.

Source: L. H. Kendrick, *Young Graphs: 1089 et al.*, Journal of Integer
Sequences 18 (2015), Article 15.9.7, pruning operation in `def:ygraph`
(lines 200–202),
<https://cs.uwaterloo.ca/journals/JIS/VOL18/Kendrick/ken1.tex>.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Retained node.** Let $V$ be a set, let $P$ be a predicate on $V$ (the pivot nodes) and let
$\prec$ be a binary relation on $V$. A node $v \in V$ is retained with respect to $P$ and $\prec$
if $P(v)$ holds or there is a node $w \in V$ with $P(w)$ and $v \prec w$. -/
def isYoungRetained {V : Type _} (pivot : V → Prop)
    (precedes : V → V → Prop) (v : V) : Prop :=
  pivot v ∨ ∃ w, pivot w ∧ precedes v w

/-- **Characterization of retained nodes.** Let $V$ be a set, let $P$ be a predicate on $V$ and
let $\prec$ be a binary relation on $V$. A node $v \in V$ is retained with respect to $P$ and
$\prec$ if and only if $P(v)$ holds or there is a node $w \in V$ with $P(w)$ and $v \prec w$. -/
@[simp]
theorem isYoungRetained_iff {V : Type _} (pivot : V → Prop)
    (precedes : V → V → Prop) (v : V) :
    isYoungRetained pivot precedes v ↔ pivot v ∨ ∃ w, pivot w ∧ precedes v w :=
  Iff.rfl

/-- **Young graph of a labeled directed graph.** Let $G$ be a labeled directed graph with vertex
set $V$, edge set $E$ and label set $L$, let $P$ be a predicate on $V$ and let $\prec$ be a binary
relation on $V$. The Young graph of $G$ with respect to $P$ and $\prec$ is the labeled directed
graph with label set $L$ whose vertices are the vertices of $G$ that are retained with respect to
$P$ and $\prec$, whose edges are the edges of $G$ whose source and target are both retained, and
in which each edge has the same source, target and label as in $G$. -/
def youngGraph {V E L : Type _} (G : LabeledDigraph V E L)
    (pivot : V → Prop) (precedes : V → V → Prop) :
    LabeledDigraph { v : V // isYoungRetained pivot precedes v }
      { e : E // isYoungRetained pivot precedes (G.src e) ∧
        isYoungRetained pivot precedes (G.tgt e) } L :=
  G.restrict (isYoungRetained pivot precedes)

/-- **Source of an edge in the Young graph.** Let $G$ be a labeled directed graph, let $P$ be a
predicate on its vertices, let $\prec$ be a binary relation on its vertices, and let $e$ be an
edge of $G$ whose source and target are both retained with respect to $P$ and $\prec$, viewed as
an edge of the Young graph of $G$ with respect to $P$ and $\prec$. The source of $e$ in the Young
graph, viewed as a vertex of $G$, is the source of $e$ in $G$. -/
@[simp]
theorem youngGraph_src {V E L : Type _} (G : LabeledDigraph V E L)
    (pivot : V → Prop) (precedes : V → V → Prop)
    (e : {e : E // isYoungRetained pivot precedes (G.src e) ∧
      isYoungRetained pivot precedes (G.tgt e)}) :
    ((youngGraph G pivot precedes).src e).val = G.src e.val :=
  rfl

/-- **Target of an edge in the Young graph.** Let $G$ be a labeled directed graph, let $P$ be a
predicate on its vertices, let $\prec$ be a binary relation on its vertices, and let $e$ be an
edge of $G$ whose source and target are both retained with respect to $P$ and $\prec$, viewed as
an edge of the Young graph of $G$ with respect to $P$ and $\prec$. The target of $e$ in the Young
graph, viewed as a vertex of $G$, is the target of $e$ in $G$. -/
@[simp]
theorem youngGraph_tgt {V E L : Type _} (G : LabeledDigraph V E L)
    (pivot : V → Prop) (precedes : V → V → Prop)
    (e : {e : E // isYoungRetained pivot precedes (G.src e) ∧
      isYoungRetained pivot precedes (G.tgt e)}) :
    ((youngGraph G pivot precedes).tgt e).val = G.tgt e.val :=
  rfl

/-- **Label of an edge in the Young graph.** Let $G$ be a labeled directed graph, let $P$ be a
predicate on its vertices, let $\prec$ be a binary relation on its vertices, and let $e$ be an
edge of $G$ whose source and target are both retained with respect to $P$ and $\prec$, viewed as
an edge of the Young graph of $G$ with respect to $P$ and $\prec$. The label of $e$ in the Young
graph is its label in $G$. -/
@[simp]
theorem youngGraph_label {V E L : Type _} (G : LabeledDigraph V E L)
    (pivot : V → Prop) (precedes : V → V → Prop)
    (e : {e : E // isYoungRetained pivot precedes (G.src e) ∧
      isYoungRetained pivot precedes (G.tgt e)}) :
    (youngGraph G pivot precedes).label e = G.label e.val :=
  rfl

end

end MetaMathlibExt
