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

/-- A node is retained when it is a pivot or precedes some pivot. -/
def isYoungRetained {V : Type _} (pivot : V → Prop)
    (precedes : V → V → Prop) (v : V) : Prop :=
  pivot v ∨ ∃ w, pivot w ∧ precedes v w

/-- Characteristic lemma for retention: a node is retained exactly when it is
a pivot or precedes some pivot. -/
@[simp]
theorem isYoungRetained_iff {V : Type _} (pivot : V → Prop)
    (precedes : V → V → Prop) (v : V) :
    isYoungRetained pivot precedes v ↔ pivot v ∨ ∃ w, pivot w ∧ precedes v w :=
  Iff.rfl

/-- The Young graph: restrict a labeled directed graph to retained nodes and
to edges whose source and target are both retained. -/
def youngGraph {V E L : Type _} (G : LabeledDigraph V E L)
    (pivot : V → Prop) (precedes : V → V → Prop) :
    LabeledDigraph { v : V // isYoungRetained pivot precedes v }
      { e : E // isYoungRetained pivot precedes (G.src e) ∧
        isYoungRetained pivot precedes (G.tgt e) } L :=
  G.restrict (isYoungRetained pivot precedes)

/-- The source of an edge in the Young graph: the ambient source, viewed in
the retained subtype. -/
@[simp]
theorem youngGraph_src {V E L : Type _} (G : LabeledDigraph V E L)
    (pivot : V → Prop) (precedes : V → V → Prop)
    (e : {e : E // isYoungRetained pivot precedes (G.src e) ∧
      isYoungRetained pivot precedes (G.tgt e)}) :
    ((youngGraph G pivot precedes).src e).val = G.src e.val :=
  rfl

/-- The target of an edge in the Young graph: the ambient target, viewed in
the retained subtype. -/
@[simp]
theorem youngGraph_tgt {V E L : Type _} (G : LabeledDigraph V E L)
    (pivot : V → Prop) (precedes : V → V → Prop)
    (e : {e : E // isYoungRetained pivot precedes (G.src e) ∧
      isYoungRetained pivot precedes (G.tgt e)}) :
    ((youngGraph G pivot precedes).tgt e).val = G.tgt e.val :=
  rfl

/-- The label of an edge in the Young graph is its ambient label. -/
@[simp]
theorem youngGraph_label {V E L : Type _} (G : LabeledDigraph V E L)
    (pivot : V → Prop) (precedes : V → V → Prop)
    (e : {e : E // isYoungRetained pivot precedes (G.src e) ∧
      isYoungRetained pivot precedes (G.tgt e)}) :
    (youngGraph G pivot precedes).label e = G.label e.val :=
  rfl

end

end MetaMathlibExt
