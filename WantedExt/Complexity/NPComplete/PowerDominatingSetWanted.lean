/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POWER DOMINATING SET is NP-complete

Source:
T. W. Haynes, S. M. Hedetniemi, S. T. Hedetniemi, and M. A. Henning, "Domination in graphs
applied to electric power networks", SIAM Journal on Discrete Mathematics 15(4) (2002), 519-529,
doi:10.1137/S0895480100375831;
D. J. Brueni and L. S. Heath, "The PMU placement problem", SIAM Journal on Discrete Mathematics
19(3) (2005), 744-761, doi:10.1137/S0895480103432556 (vertex form of the observation rules).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PowerDominatingSet

/-!
# POWER DOMINATING SET is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected) and a positive integer `K`.
QUESTION: is there a set `S ⊆ V` with `|S| ≤ K` that observes all of `V` under the rules:
the closed neighborhood `N[S]` is observed; an observed vertex with exactly one unobserved
neighbor makes that neighbor observed?

The observed set is the least set of vertices closed under the two rules (`Observed`, an
inductive predicate): every vertex of `S` and every neighbor of a vertex of `S` is observed, and
if `v` is observed, `u` is a neighbor of `v` and every other neighbor of `v` is observed, then
`u` is observed. This is the result of applying the propagation rule until nothing changes; the
order of the applications does not matter, because a vertex that may propagate keeps that
ability until its last unobserved neighbor is observed. As in the source, `K` is positive.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev PowerDominatingSetInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PowerDominatingSetInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `0 < K`. -/
def WellFormed (i : PowerDominatingSetInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

/-- The vertices of `G` observed from `S`: the least set containing the closed neighborhood
`N[S]` and closed under propagation (an observed vertex whose neighbors other than `u` are all
observed makes its neighbor `u` observed). -/
inductive Observed {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Fin n → Prop
  /-- Every vertex of `S` is observed. -/
  | mem {v : Fin n} : v ∈ S → Observed G S v
  /-- Every neighbor of a vertex of `S` is observed. -/
  | adj {s v : Fin n} : s ∈ S → G.Adj s v → Observed G S v
  /-- An observed vertex `v` with no unobserved neighbor other than `u` makes `u` observed. -/
  | propagate {v u : Fin n} : Observed G S v → G.Adj v u →
      (∀ w, G.Adj v w → w ≠ u → Observed G S w) → Observed G S u

/-- Some set `S` of at most `K` vertices observes every vertex. -/
def PowerDominatingSetFeasible (i : PowerDominatingSetInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2 ∧ ∀ v, Observed (Graph i) S v

open Classical in
/-- POWER DOMINATING SET as a decision problem over bitstrings. -/
noncomputable def powerDominatingSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PowerDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ PowerDominatingSetFeasible i)
  | none => false

/-- **POWER DOMINATING SET is NP-complete.** Source: Haynes, Hedetniemi, Hedetniemi, and
Henning (2002). -/
public theorem_wanted powerDominatingSet_npComplete :
    powerDominatingSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L powerDominatingSetDec

end MetaMathlibExt.Complexity.NPComplete.PowerDominatingSet
