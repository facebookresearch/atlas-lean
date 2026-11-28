/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GEODETIC SET: definitions

Source:
M. Atici, "Computational complexity of geodetic set", International Journal of Computer
Mathematics 79(5) (2002), 587-591, doi:10.1080/00207160210954.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeodeticSet

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), edge list, and the bound `K`. -/
abbrev GeodeticSetInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : GeodeticSetInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph (no duplicate edges
in either orientation, no self-loops, endpoints in range), the graph is connected, and
`0 < K`. -/
def WellFormed (i : GeodeticSetInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).Connected ∧ 0 < i.2.2

/-- Some set `S` of at most `K` vertices is geodetic: every vertex `x` lies on a shortest walk
between two vertices `u, v ∈ S`. -/
def GeodeticSetFeasible (i : GeodeticSetInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2 ∧ ∀ x, ∃ u ∈ S, ∃ v ∈ S,
    ∃ p : (Graph i).Walk u v, p.length = (Graph i).dist u v ∧ x ∈ p.support

open Classical in
/-- GEODETIC SET as a decision problem over bitstrings. -/
noncomputable def geodeticSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeodeticSetInstance) x with
  | some i => decide (WellFormed i ∧ GeodeticSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GeodeticSet
