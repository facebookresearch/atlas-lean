/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNSPLITTABLE FLOW: definitions

Source:
J. M. Kleinberg, "Single-source unsplittable flow", in *Proceedings of the 37th Annual
Symposium on Foundations of Computer Science*, IEEE (1996), 68-77,
doi:10.1109/SFCS.1996.548465 (the single-source unsplittable flow problem, "a natural, NP-hard
generalization" of the single-source disjoint paths problem);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM UNSPLITTABLE FLOW.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnsplittableFlow

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list (an entry `(u, v, c)` is the
edge `{u, v}` of capacity `c`), the source `s`, the commodities (an entry `(t, ρ)` is a sink with
its demand), and the bound `K`. -/
abbrev UnsplittableFlowInstance := ℕ × List (ℕ × ℕ × ℕ) × ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : UnsplittableFlowInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (i.2.1.map fun e => (e.1, e.2.1))

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range) with positive
capacities, the source and the sinks are vertices, the sinks are distinct and differ from the
source, every demand is positive and at most every capacity, and `0 < K`. -/
def WellFormed (i : UnsplittableFlowInstance) : Prop :=
  ((i.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧
      (e.2.1, e.1) ∉ i.2.1.map fun e => (e.1, e.2.1)) ∧
    (∀ e ∈ i.2.1, 0 < e.2.2) ∧ i.2.2.1 < i.1 ∧ (∀ t ∈ i.2.2.2.1, t.1 < i.1) ∧
    (i.2.2.2.1.map Prod.fst).Nodup ∧ i.2.2.1 ∉ i.2.2.2.1.map Prod.fst ∧
    (∀ t ∈ i.2.2.2.1, 0 < t.2 ∧ ∀ e ∈ i.2.1, t.2 ≤ e.2.2) ∧ 0 < i.2.2.2.2

/-- One path from `s` to each sink such that every edge `e` carries total demand at most
`K · c(e)`. -/
def UnsplittableFlowFeasible (i : UnsplittableFlowInstance) : Prop :=
  ∀ (hs : i.2.2.1 < i.1) (ht : ∀ k, (i.2.2.2.1.get k).1 < i.1),
    ∃ paths : (k : Fin i.2.2.2.1.length) →
        (Graph i).Path ⟨i.2.2.1, hs⟩ ⟨(i.2.2.2.1.get k).1, ht k⟩,
      ∀ e ∈ i.2.1, (∑ k ∈ Finset.univ.filter fun k =>
        s(e.1, e.2.1) ∈ (paths k).1.edges.map (Sym2.map Fin.val),
          (i.2.2.2.1.get k).2) ≤ i.2.2.2.2 * e.2.2

open Classical in
/-- UNSPLITTABLE FLOW as a decision problem over bitstrings. -/
noncomputable def unsplittableFlowDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnsplittableFlowInstance) x with
  | some i => decide (WellFormed i ∧ UnsplittableFlowFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnsplittableFlow
