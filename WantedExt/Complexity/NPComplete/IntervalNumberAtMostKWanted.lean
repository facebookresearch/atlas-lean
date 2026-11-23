/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERVAL NUMBER AT MOST K is NP-complete for every fixed K ≥ 2

Source:
D. B. West and D. B. Shmoys, "Recognizing graphs with fixed interval number is NP-complete",
Discrete Applied Mathematics 8 (1984), 295-305, doi:10.1016/0166-218X(84)90127-6;
W. T. Trotter and F. Harary, "On double and multiple interval graphs", Journal of Graph Theory 3
(1979), 205-211, doi:10.1002/jgt.3190030302 (definition of `t`-interval graphs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.SetNotation
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntervalNumberAtMostK

/-!
# INTERVAL NUMBER AT MOST K is NP-complete for every fixed K ≥ 2

Fix an integer `K ≥ 2`.
INSTANCE: a finite simple undirected graph `G = (V, E)`.
QUESTION: is the interval number of `G` at most `K`, that is, is `G` the intersection graph of
sets each of which is a union of at most `K` real intervals (`G` is a `K`-interval graph)?

The interval number `i(G)` is the least `t` such that each vertex `v` can be assigned a set
`S(v)` that is a union of at most `t` closed intervals of the real line, with two distinct
vertices adjacent exactly when their sets intersect (Trotter and Harary). For `t = 1` these are
the interval graphs. West and Shmoys prove that recognizing graphs with `i(G) ≤ t` is
NP-complete for every fixed `t ≥ 2`.

`IsMultipleIntervalGraph t H` assigns each vertex `v` exactly `t` closed intervals
`[l v j, r v j]` (`j : Fin t`, `l v j ≤ r v j`) and takes `S(v)` to be their union. Intervals
may repeat, so for `t ≥ 1` the sets `S(v)` are exactly the unions of between `1` and `t` closed
intervals; a vertex with no interval at all can always be given a far-away one instead, so
this is the same graph class. The graph is given by an edge list on `Fin n` as in the other
graph statements of this directory (`Cslib.Complexity.Karp.edgeGraph`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev IntervalNumberAtMostKInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : IntervalNumberAtMostKInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : IntervalNumberAtMostKInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `H` is a `t`-interval graph: each vertex `v` is assigned `t` closed real intervals
`[l v j, r v j]` (`j : Fin t`, possibly repeated), and two distinct vertices are adjacent in `H`
exactly when the unions of their intervals intersect. -/
def IsMultipleIntervalGraph (t : ℕ) {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  ∃ l r : Fin n → Fin t → ℝ, (∀ v j, l v j ≤ r v j) ∧
    ∀ u v, u ≠ v →
      (H.Adj u v ↔
        ((⋃ j, Set.Icc (l u j) (r u j)) ∩ (⋃ j, Set.Icc (l v j) (r v j))).Nonempty)

/-- The interval number of the graph is at most `t`: it is a `t`-interval graph. -/
def IntervalNumberAtMostKFeasible (t : ℕ) (i : IntervalNumberAtMostKInstance) : Prop :=
  IsMultipleIntervalGraph t (Graph i)

open Classical in
/-- INTERVAL NUMBER AT MOST K, for the fixed bound `t`, as a decision problem over bitstrings. -/
noncomputable def intervalNumberAtMostKDec (t : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntervalNumberAtMostKInstance) x with
  | some i => decide (WellFormed i ∧ IntervalNumberAtMostKFeasible t i)
  | none => false

/-- **INTERVAL NUMBER AT MOST K is NP-complete for every fixed `K ≥ 2`.** Source: West and
Shmoys (1984). -/
public theorem_wanted intervalNumberAtMostK_npComplete (t : ℕ) (ht : 2 ≤ t) :
    intervalNumberAtMostKDec t ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (intervalNumberAtMostKDec t)

end MetaMathlibExt.Complexity.NPComplete.IntervalNumberAtMostK
