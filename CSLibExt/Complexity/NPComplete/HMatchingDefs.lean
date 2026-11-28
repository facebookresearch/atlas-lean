/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# H-MATCHING: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MAXIMUM H-MATCHING (the decision version of the optimization problem stated here);
D. G. Kirkpatrick and P. Hell, "On the completeness of a generalized matching
problem", Proceedings of the 10th Annual ACM Symposium on Theory of Computing
(1978), 240-245, doi:10.1145/800133.804353;
D. G. Kirkpatrick and P. Hell, "On the complexity of general graph factor
problems", SIAM Journal on Computing 12(3) (1983), 601-609, doi:10.1137/0212040;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), comment to problem [GT12]
PARTITION INTO ISOMORPHIC SUBGRAPHS.
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PerfectHPackingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HMatching

/-- An instance: vertex count `n` (vertices `Fin n`), edge list of `G`, bound `K`. -/
abbrev HMatchingInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph `G` of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : HMatchingInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `0 < K`. -/
def WellFormed (i : HMatchingInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

/-- `K` pairwise vertex-disjoint subgraphs of `G` isomorphic to `H`: copies of the pattern in `G`
(injective homomorphisms from the pattern graph `edgeGraph m hs`) with pairwise disjoint vertex
images. -/
def HMatchingFeasible (m : ℕ) (hs : List (ℕ × ℕ)) (i : HMatchingInstance) : Prop :=
  ∃ f : Fin i.2.2 → (Cslib.Complexity.Karp.edgeGraph m hs).Copy (Graph i),
    Pairwise fun j j' => Disjoint (Set.range (f j)) (Set.range (f j'))

open Classical in
/-- H-MATCHING for the fixed pattern `(m, hs)` as a decision problem over bitstrings. -/
noncomputable def hMatchingDec (m : ℕ) (hs : List (ℕ × ℕ)) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HMatchingInstance) x with
  | some i => decide (WellFormed i ∧ HMatchingFeasible m hs i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HMatching
