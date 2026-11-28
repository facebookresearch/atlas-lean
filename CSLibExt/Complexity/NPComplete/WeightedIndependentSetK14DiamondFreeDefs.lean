/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED INDEPENDENT SET on (K_1,4, diamond)-free graphs: definitions

Source:
D. G. Corneil, "The complexity of generalized clique packing", Discrete Applied Mathematics 12
(1985), 233-239, doi:10.1016/0166-218X(85)90027-7;
A. Brandstädt, V. B. Le and S. Mahfud, "New applications of clique separator decomposition for
the Maximum Weight Stable Set problem", Theoretical Computer Science 370 (2007), 229-239,
doi:10.1016/j.tcs.2006.10.035 (records the attribution: the maximum weight stable set problem
"remains NP-complete even on very restricted instances such as ... (K1,4,diamond)-free graphs",
citing Corneil (1985)).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ColoringK4ClawDiamondFreeDefs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Copy

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedIndependentSetK14DiamondFree

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, vertex weights (the `v`-th
entry is the weight of vertex `v`), bound `k`. -/
abbrev WeightedIndependentSetInstance := ℕ × List (ℕ × ℕ) × List ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : WeightedIndependentSetInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The weight of vertex `v`: the `v`-th entry of the weight list. -/
def weight (i : WeightedIndependentSetInstance) (v : Fin i.1) : ℕ :=
  i.2.2.1.getD v 0

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), there is one weight
per vertex, and the graph has neither `K_1,4` nor the diamond as an induced subgraph. -/
def WellFormed (i : WeightedIndependentSetInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.1.length = i.1 ∧
    ¬ (completeBipartiteGraph (Fin 1) (Fin 4)).IsIndContained (Graph i) ∧
    ¬ ColoringK4ClawDiamondFree.diamond.IsIndContained (Graph i)

/-- Some set of pairwise non-adjacent vertices has total weight at least `k`. -/
def WeightedIndependentSetFeasible (i : WeightedIndependentSetInstance) : Prop :=
  ∃ s : Finset (Fin i.1), (Graph i).IsIndepSet (s : Set (Fin i.1)) ∧
    i.2.2.2 ≤ ∑ v ∈ s, weight i v

open Classical in
/-- WEIGHTED INDEPENDENT SET on `(K_1,4, diamond)`-free graphs as a decision problem over
bitstrings. -/
noncomputable def weightedIndependentSetK14DiamondFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeightedIndependentSetInstance) x with
  | some i => decide (WellFormed i ∧ WeightedIndependentSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.WeightedIndependentSetK14DiamondFree
