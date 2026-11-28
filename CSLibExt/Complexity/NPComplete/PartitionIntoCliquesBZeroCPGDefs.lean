/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES on B₀-CPG graphs: definitions

Source:
N. Champseix, E. Galby, A. Munaro and B. Ries, "CPG graphs: Some structural and hardness
results", Discrete Applied Mathematics 290 (2021), 17-35, doi:10.1016/j.dam.2020.11.018
(arXiv:1903.01805), Theorem 11;
Z. Deniz, E. Galby, A. Munaro and B. Ries, "On contact graphs of paths on a grid", Graph Drawing
and Network Visualization (GD 2018), LNCS 11282, doi:10.1007/978-3-030-04414-5_22 (the class
CPG);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Interval.Set.Basic
public import CSLibExt.Complexity.NPComplete.PartitionIntoCliquesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesBZeroCPG

open PartitionIntoCliques (PartitionIntoCliquesInstance Graph PartitionIntoCliquesFeasible)

/-- The grid point `2p` of the grid refined by a factor of `2`. -/
def double (p : ℕ × ℕ) : ℕ × ℕ := (2 * p.1, 2 * p.2)

/-- The interior points of the segment from `p` to `q` on the refined grid. -/
def interiorPoints (s : (ℕ × ℕ) × (ℕ × ℕ)) : Set (ℕ × ℕ) :=
  Set.Icc (double s.1) (double s.2) \ {double s.1, double s.2}

/-- `G` is a `B₀-CPG` graph: there are horizontal or vertical grid segments `P v` from
`(P v).1` to `(P v).2 > (P v).1`, one per vertex, pairwise without common interior points, such
that two distinct vertices are adjacent exactly when their segments have a common point. -/
def IsBZeroCPG {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ P : Fin n → (ℕ × ℕ) × (ℕ × ℕ),
    (∀ v, (P v).1 < (P v).2 ∧ ((P v).1.1 = (P v).2.1 ∨ (P v).1.2 = (P v).2.2)) ∧
    (∀ u v, u ≠ v → interiorPoints (P u) ∩ interiorPoints (P v) = ∅) ∧
    ∀ u v, u ≠ v → (G.Adj u v ↔ (Set.Icc (P u).1 (P u).2 ∩ Set.Icc (P v).1 (P v).2).Nonempty)

/-- Well-formedness of an instance: well formed for PARTITION INTO CLIQUES (a simple graph on
`Fin n` and `0 < K ≤ n`), and the graph is a `B₀-CPG` graph. -/
def WellFormed (i : PartitionIntoCliquesInstance) : Prop :=
  PartitionIntoCliques.WellFormed i ∧ IsBZeroCPG (Graph i)

open Classical in
/-- PARTITION INTO CLIQUES on `B₀-CPG` graphs as a decision problem over bitstrings. -/
noncomputable def partitionIntoCliquesBZeroCPGDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := PartitionIntoCliquesInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoCliquesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesBZeroCPG
