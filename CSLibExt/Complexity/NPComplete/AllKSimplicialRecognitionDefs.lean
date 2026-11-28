/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ALL-K-SIMPLICIAL GRAPH RECOGNITION is NP-complete for every fixed K ≥ 3: definitions

Source:
P. Gambette and S. Vialette, "On restrictions of balanced 2-interval graphs", Graph-Theoretic
Concepts in Computer Science (WG 2007), Lecture Notes in Computer Science 4769 (2007), 55-65,
doi:10.1007/978-3-540-74839-7_6, Theorem 3 (arXiv:0704.1571).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AllKSimplicialRecognition

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev AllKSimplicialRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : AllKSimplicialRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, …, n - 1` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : AllKSimplicialRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `G` is all-`k`-simplicial: for every vertex `v`, the neighborhood of `v` is partitioned into
at most `k` cliques, given by a labeling `c` of the neighbors of `v` with `k` labels in which any
two distinct neighbors with the same label are adjacent. -/
def IsAllKSimplicial {n : ℕ} (k : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v : Fin n, ∃ c : {a : Fin n // G.Adj v a} → Fin k, ∀ a b : {a : Fin n // G.Adj v a},
    a ≠ b → c a = c b → G.Adj a b

/-- The graph of the instance is all-`k`-simplicial. -/
def AllKSimplicialRecognitionFeasible (k : ℕ) (i : AllKSimplicialRecognitionInstance) : Prop :=
  IsAllKSimplicial k (Graph i)

open Classical in
/-- ALL-K-SIMPLICIAL GRAPH RECOGNITION, for the fixed `k`, as a decision problem over
bitstrings. -/
noncomputable def allKSimplicialRecognitionDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := AllKSimplicialRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ AllKSimplicialRecognitionFeasible k i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.AllKSimplicialRecognition
