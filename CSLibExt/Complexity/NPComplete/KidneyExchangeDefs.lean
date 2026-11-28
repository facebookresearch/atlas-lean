/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KIDNEY EXCHANGE (perfect cycle cover with cycles of length at most L): definitions

Source:
D. J. Abraham, A. Blum and T. Sandholm, "Clearing algorithms for barter exchange markets:
enabling nationwide kidney exchanges", Proceedings of the 8th ACM Conference on Electronic
Commerce (EC 2007), 295-304, doi:10.1145/1250910.1250954, Theorem 1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KidneyExchange

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list (a pair `(u, v)` is the
edge `u → v`), and the cycle-length bound `L`. -/
abbrev KidneyExchangeInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The directed graph of the instance, with an edge `u → v` for each pair `(u, v)` of the
edge list. -/
def Graph (i : KidneyExchangeInstance) : Digraph (Fin i.1) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: no repeated edges, endpoints in range, no loops (an edge
goes from one agent to another), and `L ≥ 3`. Opposite edges `u → v` and `v → u` may both
occur. -/
def WellFormed (i : KidneyExchangeInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2) ∧ 3 ≤ i.2.2

/-- `G` admits a perfect cycle cover containing cycles of length at most `L`: there is a
permutation `σ` of the vertices with an edge from every vertex `v` to `σ v` and with every
cycle of length at most `L`. -/
def KidneyExchangeFeasible (i : KidneyExchangeInstance) : Prop :=
  ∃ σ : Equiv.Perm (Fin i.1), ∀ v, (Graph i).Adj v (σ v) ∧ Function.minimalPeriod σ v ≤ i.2.2

open Classical in
/-- KIDNEY EXCHANGE as a decision problem over bitstrings. -/
noncomputable def kidneyExchangeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KidneyExchangeInstance) x with
  | some i => decide (WellFormed i ∧ KidneyExchangeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.KidneyExchange
