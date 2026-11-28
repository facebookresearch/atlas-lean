/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE on 3-interval graphs: definitions

Source:
A. Butman, D. Hermelin, M. Lewenstein and D. Rawitz, "Optimization problems in
multiple-interval graphs", ACM Transactions on Algorithms 6(2) (2010), Article 40,
doi:10.1145/1721837.1721856 (SODA 2007, 268-277);
recorded in M. C. Francis, D. Gonçalves and P. Ochem, "The maximum clique problem in multiple
interval graphs", Algorithmica 71 (2015), 812-836, doi:10.1007/s00453-013-9828-6, Section 1
("Butman et al. showed that MAXIMUM CLIQUE is NP-complete for t-interval graphs when t ≥ 3");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE.
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.IntervalNumberAtMostKDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueThreeInterval

open MetaMathlibExt.Complexity.NPComplete.IntervalNumberAtMostK (IsMultipleIntervalGraph)

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev CliqueThreeIntervalInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CliqueThreeIntervalInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), `0 < K ≤ n`, and the
graph is a `3`-interval graph. -/
def WellFormed (i : CliqueThreeIntervalInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧ IsMultipleIntervalGraph 3 (Graph i)

/-- The graph has a clique of size `K` or more. -/
def CliqueThreeIntervalFeasible (i : CliqueThreeIntervalInstance) : Prop :=
  ∃ S : Finset (Fin i.1), i.2.2 ≤ S.card ∧ (Graph i).IsClique (S : Set (Fin i.1))

open Classical in
/-- CLIQUE on 3-interval graphs as a decision problem over bitstrings. -/
noncomputable def cliqueThreeIntervalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CliqueThreeIntervalInstance) x with
  | some i => decide (WellFormed i ∧ CliqueThreeIntervalFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CliqueThreeInterval
