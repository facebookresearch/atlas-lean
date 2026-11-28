/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
public import MathlibExt.NumberTheory.Digits.YoungGraph

/-! # Complete Young graphs

Kendrick's carry graph has a separate starting vertex, represented by `none`,
and ordinary carry pairs, represented by `some`. Reachability from the start
selects the vertices of `H(g, k)`; pruning at the pivots gives `Y(g, k)`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Young carry edge.** For base $g$ and multiplier $k$, the two carries of
an ordinary node lie in $[0,k)$, and the two digits of an edge label lie in
$[0,g)$. An edge labeled $(a,b)$ from $[r,s]$ to $[t,u]$ satisfies
$kb+s=a+ug$ and $ka+t=b+rg$. The separate start $[[0,0]]$ uses $r=s=0$ and
requires $a$ and $b$ both nonzero. No edge has the start as target.

Source: L. H. Kendrick, *Young Graphs: 1089 et al.*, Journal of Integer
Sequences 18 (2015), Article 15.9.7, Section 2.2,
<https://cs.uwaterloo.ca/journals/JIS/VOL18/Kendrick/ken1.tex>. -/
def IsYoungCarryEdge {g k : ℕ} (source : Option (Fin k × Fin k))
    (target : Fin k × Fin k) (label : Fin g × Fin g) : Prop :=
  let r := (source.map fun c => c.1.val).getD 0
  let s := (source.map fun c => c.2.val).getD 0
  (source = none → label.1.val ≠ 0 ∧ label.2.val ≠ 0) ∧
    k * label.2.val + s = label.1.val + target.2.val * g ∧
    k * label.1.val + target.1.val = label.2.val + r * g

/-- **Complete Young graphs.** For $2 \le k < g$, form $H(g,k)$ from the
carry edges reachable from the separate start $[[0,0]]$. Keep the vertices
that are or can reach a pivot, and all edges between those vertices, to form
$Y(g,k)$. An ordinary carry pair is a pivot if its entries are equal or it
has an edge to its swapped pair. The start is not a pivot.

The graph $Y(g,k)$ is complete on $m$ nodes if it contains the start and
exactly $m$ ordinary nodes, including $[0,0]$. Every ordered pair of ordinary
nodes, including an equal pair, has exactly one edge. The start has an edge
to each ordinary node except $[0,0]$, and no edge ends at the start.

Source: L. H. Kendrick, *Young Graphs: 1089 et al.*, Journal of Integer
Sequences 18 (2015), Article 15.9.7, Definition 21 and Sections 2.2–2.3,
<https://cs.uwaterloo.ca/journals/JIS/VOL18/Kendrick/ken1.tex>. For the loop
convention, see also N. J. A. Sloane, *2178 and All That*, Section 3.3,
<https://arxiv.org/abs/1307.0453>. -/
def IsCompleteYoungGraph (g k m : ℕ) : Prop :=
  2 ≤ k ∧ k < g ∧
    let adj (u v : Option (Fin k × Fin k)) : Prop :=
      match v with
      | none => False
      | some c => ∃ d : Fin g × Fin g, IsYoungCarryEdge u c d
    let reaches := Relation.ReflTransGen adj
    let pivot (v : Option (Fin k × Fin k)) : Prop :=
      match v with
      | none => False
      | some (r, s) => r = s ∨ adj v (some (s, r))
    let retained v := reaches none v ∧ isYoungRetained pivot reaches v
    let ordinary : Set (Fin k × Fin k) := {v | retained (some v)}
    retained none ∧ ordinary.ncard = m ∧
      ∃ z ∈ ordinary, z.1.val = 0 ∧ z.2.val = 0 ∧
        (∀ u ∈ ordinary, ∀ v ∈ ordinary,
          ∃! d : Fin g × Fin g, IsYoungCarryEdge (some u) v d) ∧
        (∀ v ∈ ordinary,
          (∃ d : Fin g × Fin g, IsYoungCarryEdge none v d) ↔ v ≠ z)

end

end MetaMathlibExt
