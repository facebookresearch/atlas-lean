/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH CONTRACTABILITY: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT51] GRAPH CONTRACTABILITY
(attributed there to R. Statman, unpublished, 1976);
A. E. Brouwer and H. J. Veldman, "Contractibility and NP-completeness", Journal of Graph
Theory 11 (1987), 71-79, doi:10.1002/jgt.3190110111.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphContractability

/-- An instance: vertex count and edge list of `G`, vertex count and edge list of `H`. -/
abbrev GraphContractabilityInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ)

/-- The graph `G` as a `SimpleGraph (Fin n₁)`. -/
def GraphG (i : GraphContractabilityInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The graph `H` as a `SimpleGraph (Fin n₂)`. -/
def GraphH (i : GraphContractabilityInstance) : SimpleGraph (Fin i.2.2.1) :=
  Cslib.Complexity.Karp.edgeGraph i.2.2.1 i.2.2.2

/-- Well-formedness of an instance: both edge lists are simple (in range, no loops, no
repeated edge in either orientation). -/
def WellFormed (i : GraphContractabilityInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.2.Nodup ∧
      ∀ e ∈ i.2.2.2, e.1 < i.2.2.1 ∧ e.2 < i.2.2.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2.2

/-- `G` contracts to `H`: some map `f : V₁ → V₂` has fibers inducing connected subgraphs of
`G`, and the quotient of `G` by its fibers is `H`. -/
def GraphContractabilityFeasible (i : GraphContractabilityInstance) : Prop :=
  ∃ f : Fin i.1 → Fin i.2.2.1,
    (∀ x, ((GraphG i).induce {v | f v = x}).Connected) ∧ (GraphG i).map f = GraphH i

open Classical in
/-- GRAPH CONTRACTABILITY as a decision problem over bitstrings. -/
noncomputable def graphContractabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphContractabilityInstance) x with
  | some i => decide (WellFormed i ∧ GraphContractabilityFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GraphContractability
