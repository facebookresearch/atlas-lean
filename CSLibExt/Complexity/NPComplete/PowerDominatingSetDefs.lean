/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POWER DOMINATING SET: definitions

Source:
T. W. Haynes, S. M. Hedetniemi, S. T. Hedetniemi, and M. A. Henning, "Domination in graphs
applied to electric power networks", SIAM Journal on Discrete Mathematics 15(4) (2002), 519-529,
doi:10.1137/S0895480100375831;
D. J. Brueni and L. S. Heath, "The PMU placement problem", SIAM Journal on Discrete Mathematics
19(3) (2005), 744-761, doi:10.1137/S0895480103432556 (vertex form of the observation rules).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PowerDominatingSet

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

end MetaMathlibExt.Complexity.NPComplete.PowerDominatingSet
