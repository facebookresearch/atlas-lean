/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# B₁-CPG GRAPH RECOGNITION: definitions

Source:
N. Champseix, E. Galby, A. Munaro and B. Ries, "CPG graphs: Some structural and hardness
results", Discrete Applied Mathematics 290 (2021), 17-35, doi:10.1016/j.dam.2020.11.018
(arXiv:1903.01805; Section 1: the definition of CPG and `B_k`-CPG graphs; Theorem 9:
"Recognition is NP-complete in `B_k`-CPG for any `k ≥ 1`");
ISGCI (https://www.graphclasses.org/classes/gc_1338.html), class B_1-CPG, problem "Recognition":
NP-complete, citing Champseix, Galby, Munaro and Ries.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.CliqueBOneVPGDefs
public import CSLibExt.Complexity.NPComplete.PartitionIntoCliquesBZeroCPGDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BOneCPGRecognition

open CliqueBOneVPG (BendPath pathPoints)
open PartitionIntoCliquesBZeroCPG (double)

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev BOneCPGRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : BOneCPGRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : BOneCPGRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `P = (a, c, b)` is a grid path from `a` to `b` with at most one bend, at `c`: the leg `a`-`c`
is horizontal and the leg `c`-`b` vertical, or the other way round, and `a ≠ b`. -/
def IsOneBendPath (P : BendPath) : Prop :=
  P.1 ≠ P.2.2 ∧
    ((P.1.2 = P.2.1.2 ∧ P.2.1.1 = P.2.2.1) ∨ (P.1.1 = P.2.1.1 ∧ P.2.1.2 = P.2.2.2))

/-- The interior points of the path on the grid refined by a factor of `2`: the refined grid
points of the doubled path other than its doubled endpoints. -/
def interiorPoints (P : BendPath) : Set (ℕ × ℕ) :=
  pathPoints (double P.1, double P.2.1, double P.2.2) \ {double P.1, double P.2.2}

/-- `G` is a `B₁`-CPG graph: there are grid paths `P v` with at most one bend, one per vertex,
pairwise without common interior points, such that two distinct vertices are adjacent exactly
when their paths have a common grid point. -/
def IsBOneCPG {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ P : Fin n → BendPath, (∀ v, IsOneBendPath (P v)) ∧
    (∀ u v, u ≠ v → interiorPoints (P u) ∩ interiorPoints (P v) = ∅) ∧
    ∀ u v, u ≠ v → (G.Adj u v ↔ (pathPoints (P u) ∩ pathPoints (P v)).Nonempty)

/-- The graph of the instance is a `B₁`-CPG graph. -/
def BOneCPGRecognitionFeasible (i : BOneCPGRecognitionInstance) : Prop :=
  IsBOneCPG (Graph i)

open Classical in
/-- `B₁`-CPG GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def bOneCPGRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BOneCPGRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ BOneCPGRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BOneCPGRecognition
