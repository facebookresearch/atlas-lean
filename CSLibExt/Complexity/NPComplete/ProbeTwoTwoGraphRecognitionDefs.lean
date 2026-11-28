/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PROBE (2,2)-GRAPH RECOGNITION: definitions

Source:
S. Dantas, L. Faria, C. M. H. de Figueiredo and R. B. Teixeira, "The (k, ℓ) unpartitioned probe
problem NP-complete versus polynomial dichotomy", Information Processing Letters 116 (2016),
294-298, doi:10.1016/j.ipl.2015.11.004;
S. Dantas, L. Faria, C. M. H. de Figueiredo and R. B. Teixeira, "The generalized split probe
problem", Electronic Notes in Discrete Mathematics 44 (2013), 39-45,
doi:10.1016/j.endm.2013.10.007;
ISGCI (https://www.graphclasses.org/classes/gc_1269.html), problem "Recognition" on probe
(2,2)-colorable graphs: NP-complete.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ProbeTwoTwoGraphRecognition

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev ProbeTwoTwoGraphRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : ProbeTwoTwoGraphRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : ProbeTwoTwoGraphRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `H` is a `(2,2)`-graph: its vertex set splits into at most two independent sets (labels `0`
and `1`) and at most two cliques (labels `2` and `3`). -/
def IsTwoTwoGraph {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  ∃ c : Fin n → Fin 4, H.IsIndepSet {v | c v = 0} ∧ H.IsIndepSet {v | c v = 1} ∧
    H.IsClique {v | c v = 2} ∧ H.IsClique {v | c v = 3}

/-- `G` is a probe `(2,2)`-graph: some independent set `N` of non-probes admits a supergraph
`H ≥ G`, adding only edges between non-probes, that is a `(2,2)`-graph. -/
def IsProbeTwoTwoGraph {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ N : Set (Fin n), G.IsIndepSet N ∧
    ∃ H : SimpleGraph (Fin n), G ≤ H ∧ (∀ u v, H.Adj u v → G.Adj u v ∨ (u ∈ N ∧ v ∈ N)) ∧
      IsTwoTwoGraph H

/-- The graph of the instance is a probe `(2,2)`-graph. -/
def ProbeTwoTwoGraphRecognitionFeasible (i : ProbeTwoTwoGraphRecognitionInstance) : Prop :=
  IsProbeTwoTwoGraph (Graph i)

open Classical in
/-- PROBE (2,2)-GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def probeTwoTwoGraphRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ProbeTwoTwoGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ ProbeTwoTwoGraphRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ProbeTwoTwoGraphRecognition
