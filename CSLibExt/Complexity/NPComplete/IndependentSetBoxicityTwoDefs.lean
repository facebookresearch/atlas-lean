/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on boxicity-2 graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET, the problem
restricted here;
C. S. Rim and K. Nakajima, "On rectangle intersection and overlap graphs", IEEE Transactions on
Circuits and Systems I: Fundamental Theory and Applications 42(9) (1995), 549-553,
doi:10.1109/81.414831.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Complexity.NPComplete.BoxicityTwoDefs
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetBoxicityTwo

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev IndependentSetBoxicityTwoInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : IndependentSetBoxicityTwoInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`
(`BoxicityTwo.WellFormed`), the graph has boxicity at most 2 (`BoxicityTwo.BoxicityTwoFeasible`),
and `0 < K ≤ |V|`. -/
def WellFormed (i : IndependentSetBoxicityTwoInstance) : Prop :=
  BoxicityTwo.WellFormed (i.1, i.2.1) ∧ BoxicityTwo.BoxicityTwoFeasible (i.1, i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some set of at least `K` vertices contains no two adjacent vertices. -/
def IndependentSetBoxicityTwoFeasible (i : IndependentSetBoxicityTwoInstance) : Prop :=
  ∃ s : Finset (Fin i.1), i.2.2 ≤ s.card ∧ (Graph i).IsIndepSet (s : Set (Fin i.1))

open Classical in
/-- INDEPENDENT SET on boxicity-2 graphs as a decision problem over bitstrings. -/
noncomputable def independentSetBoxicityTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IndependentSetBoxicityTwoInstance) x with
  | some i => decide (WellFormed i ∧ IndependentSetBoxicityTwoFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IndependentSetBoxicityTwo
