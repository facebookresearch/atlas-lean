/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERVAL NUMBER AT MOST K is NP-complete for every fixed K ≥ 2: definitions

Source:
D. B. West and D. B. Shmoys, "Recognizing graphs with fixed interval number is NP-complete",
Discrete Applied Mathematics 8 (1984), 295-305, doi:10.1016/0166-218X(84)90127-6;
W. T. Trotter and F. Harary, "On double and multiple interval graphs", Journal of Graph Theory 3
(1979), 205-211, doi:10.1002/jgt.3190030302 (definition of `t`-interval graphs).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.SetNotation
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntervalNumberAtMostK

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev IntervalNumberAtMostKInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : IntervalNumberAtMostKInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : IntervalNumberAtMostKInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `H` is a `t`-interval graph: each vertex `v` is assigned `t` closed real intervals
`[l v j, r v j]` (`j : Fin t`, possibly repeated), and two distinct vertices are adjacent in `H`
exactly when the unions of their intervals intersect. -/
def IsMultipleIntervalGraph (t : ℕ) {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  ∃ l r : Fin n → Fin t → ℝ, (∀ v j, l v j ≤ r v j) ∧
    ∀ u v, u ≠ v →
      (H.Adj u v ↔
        ((⋃ j, Set.Icc (l u j) (r u j)) ∩ (⋃ j, Set.Icc (l v j) (r v j))).Nonempty)

/-- The interval number of the graph is at most `t`: it is a `t`-interval graph. -/
def IntervalNumberAtMostKFeasible (t : ℕ) (i : IntervalNumberAtMostKInstance) : Prop :=
  IsMultipleIntervalGraph t (Graph i)

open Classical in
/-- INTERVAL NUMBER AT MOST K, for the fixed bound `t`, as a decision problem over bitstrings. -/
noncomputable def intervalNumberAtMostKDec (t : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntervalNumberAtMostKInstance) x with
  | some i => decide (WellFormed i ∧ IntervalNumberAtMostKFeasible t i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IntervalNumberAtMostK
