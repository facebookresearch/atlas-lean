/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A universal locally finite highly arc transitive digraph (Open Problem Garden 677)

Open Problem Garden, Universal highly arc transitive digraphs (P. J. Cameron, C. E. Praeger and N.
C. Wormald): an alternating walk uses arcs alternately forwards and backwards, and a digraph is
universal if any two edges lie on a common alternating walk. Does there exist a locally finite
highly arc transitive digraph which is universal?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Combinatorics.Digraph.Basic

@[expose] public section

namespace MathlibExt.GraphTheory.UniversalHighlyArcTransitiveOpenGardenProblem677Wanted

/-!
Source: Open Problem Garden, Universal highly arc transitive digraphs (node 677; P. J. Cameron, C.
E. Praeger and N. C. Wormald),
http://www.openproblemgarden.org/op/universal_highly_arc_transitive_digraphs. UnsolvedMath record
UM-00003302 (`OPG-677`), dataset ulamai/UnsolvedMath v1.8.0.

Definitions follow the source page: digraphs are Mathlib `Digraph`s; an `s`-arc is a sequence `(x 0,
…, x s)` with each `x i → x (i + 1)` an arc and `x (i - 1) ≠ x (i + 1)` for `1 ≤ i ≤ s - 1`; highly
arc transitive means that for every `s ≥ 0` the automorphisms act transitively on `s`-arcs (for `s =
0`, on vertices). The digraphs have no loops and no 2-cycles (the arc relation is asymmetric): with
2-cycles allowed, the complete symmetric digraph on three vertices would be a finite, highly arc
transitive, universal witness, contradicting the page's remark that the only finite highly arc
transitive digraphs are directed cycles. Without 2-cycles the condition `x (i - 1) ≠ x (i + 1)`
holds for every directed walk, so the page's `s`-arcs are exactly those of DeVos-Mohar-Šámal
(Section 1: all directed walks), whose Theorem 2.1 answers the question; their digraph `G_{a,b}` has
no 2-cycles (an arc and its reverse would give a 4-cycle in the tree `T_{a,b}`). Universal means
that for any two arcs `e`, `f` some alternating walk has first arc `e` and last arc `f` (the
reachability relation has one class); this is equivalent to the page's "a common alternating walk",
as reachability is an equivalence relation. Locally finite: finitely many out- and in-neighbours at
every vertex. As in DeVos-Mohar-Šámal, the digraph has no isolated vertices; together with `Nonempty
V` this excludes the arcless digraphs, which would satisfy the other conditions vacuously.
-/

/-- `(x 0, …, x s)` is an `s`-arc of `D` (the source page's definition): `x i → x (i + 1)` is an
arc for each `i < s`, and `x (i - 1) ≠ x (i + 1)` for each `1 ≤ i ≤ s - 1`. -/
def IsSArc {V : Type} (D : Digraph V) (s : ℕ) (x : ℕ → V) : Prop :=
  (∀ i < s, D.Adj (x i) (x (i + 1))) ∧ ∀ i, i + 2 ≤ s → x i ≠ x (i + 2)

/-- `σ` is an automorphism of `D`. -/
def IsAutomorphism {V : Type} (D : Digraph V) (σ : V ≃ V) : Prop :=
  ∀ u v, D.Adj (σ u) (σ v) ↔ D.Adj u v

/-- `D` is highly arc transitive: for every `s ≥ 0` its automorphism group acts transitively on its
`s`-arcs (for `s = 0`: on its vertices). -/
def IsHighlyArcTransitive {V : Type} (D : Digraph V) : Prop :=
  ∀ (s : ℕ) (x y : ℕ → V), IsSArc D s x → IsSArc D s y →
    ∃ σ : V ≃ V, IsAutomorphism D σ ∧ ∀ i ≤ s, σ (x i) = y i

/-- The `j`-th arc used by the sequence `v` when arcs are traversed alternately forwards and
backwards, starting forwards when `b = true`: `v j → v (j + 1)` if `j` is even and `b = true`, or
`j` is odd and `b = false`; otherwise `v (j + 1) → v j`. -/
def alternatingArc {V : Type} (v : ℕ → V) (b : Bool) (j : ℕ) : V × V :=
  if decide (Even j) = b then (v j, v (j + 1)) else (v (j + 1), v j)

/-- `v 0, …, v s` (`s ≥ 1`) is an alternating walk of `D`: its arcs `alternatingArc v b j`
(`j < s`) are arcs of `D`, used alternately forwards and backwards. -/
def IsAlternatingWalk {V : Type} (D : Digraph V) (s : ℕ) (v : ℕ → V) (b : Bool) : Prop :=
  0 < s ∧ ∀ j < s, D.Adj (alternatingArc v b j).1 (alternatingArc v b j).2

/-- `D` is universal: for any two arcs `e` and `f` there is an alternating walk whose first arc is
`e` and whose last arc is `f` (the reachability relation has a single class). -/
def IsUniversal {V : Type} (D : Digraph V) : Prop :=
  ∀ e f : V × V, D.Adj e.1 e.2 → D.Adj f.1 f.2 →
    ∃ (s : ℕ) (v : ℕ → V) (b : Bool), IsAlternatingWalk D s v b ∧
      alternatingArc v b 0 = e ∧ alternatingArc v b (s - 1) = f

/-- The question of Cameron, Praeger and Wormald, answered affirmatively: there is a locally finite
highly arc transitive digraph (nonempty, without loops or 2-cycles, without isolated vertices) which
is universal. -/
def universalHighlyArcTransitiveExists : Prop :=
  ∃ (V : Type) (D : Digraph V), Nonempty V ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
    (∀ v, ∃ w, D.Adj v w ∨ D.Adj w v) ∧
    (∀ v, {w | D.Adj v w}.Finite ∧ {w | D.Adj w v}.Finite) ∧
    IsHighlyArcTransitive D ∧ IsUniversal D

/--
Resolved true: DeVos, Mohar and Šámal constructed a locally finite highly arc transitive digraph
whose reachability relation is universal (for every composite `d ≥ 4`, one with all in- and
out-degrees `d`); it has no loops or 2-cycles, so it is highly arc transitive in the source page's
sense. Source: Open Problem Garden, Universal highly arc transitive digraphs (node 677; P. J.
Cameron, C. E. Praeger and N. C. Wormald),
http://www.openproblemgarden.org/op/universal_highly_arc_transitive_digraphs; resolution: M. DeVos,
B. Mohar and R. Šámal, Highly arc-transitive digraphs - structure and counterexamples, Combinatorica
35 (2015), 553-571, doi:10.1007/s00493-014-3040-4; arXiv:1110.2945, Theorem 2.1: there is a locally
finite highly arc-transitive digraph for which the reachability relation is universal; for every
composite d ≥ 4 there is one with all in- and out-degrees d ('The following result answers Question
1.1 in the affirmative', Question 1.1 being the Cameron-Praeger-Wormald question),
https://doi.org/10.1007/s00493-014-3040-4.
-/
public theorem_wanted universalHighlyArcTransitiveExists_holds : universalHighlyArcTransitiveExists

end MathlibExt.GraphTheory.UniversalHighlyArcTransitiveOpenGardenProblem677Wanted
