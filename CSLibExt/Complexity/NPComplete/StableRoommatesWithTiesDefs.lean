/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STABLE ROOMMATES WITH TIES (weak stability, complete lists): definitions

Source:
E. Ronn, "NP-complete stable matching problems", Journal of Algorithms 11 (1990), 285-304,
doi:10.1016/0196-6774(90)90007-2;
problem definitions as in Á. Cseh, R. W. Irving and D. F. Manlove, "The stable roommates
problem with short lists", Theory of Computing Systems 63 (2019), 128-149,
doi:10.1007/s00224-017-9810-9, Section 1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Fin.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StableRoommatesWithTies

/-- An instance: the number `n` of agents and the rank table; row `v`, entry `w` is the rank of
`w` in agent `v`'s preference list (smaller is better, equal ranks are ties). -/
abbrev StableRoommatesWithTiesInstance := ℕ × List (List ℕ)

/-- The rank of agent `w` in agent `v`'s preference list. -/
def rank (i : StableRoommatesWithTiesInstance) (v w : Fin i.1) : ℕ :=
  (i.2.getD v []).getD w 0

/-- The edge `vw` blocks the matching with partner function `μ`: `v ≠ w`, they are not matched
to each other, `v` is unmatched or strictly prefers `w` to its partner, and `w` is unmatched
or strictly prefers `v` to its partner. -/
def Blocks (i : StableRoommatesWithTiesInstance) (μ : Fin i.1 → Fin i.1) (v w : Fin i.1) :
    Prop :=
  v ≠ w ∧ μ v ≠ w ∧ (μ v = v ∨ rank i v w < rank i v (μ v)) ∧
    (μ w = w ∨ rank i w v < rank i w (μ w))

/-- Well-formedness of an instance: one rank row per agent, each with an entry for every
agent. -/
def WellFormed (i : StableRoommatesWithTiesInstance) : Prop :=
  i.2.length = i.1 ∧ ∀ row ∈ i.2, row.length = i.1

/-- The instance is solvable: some matching (an involutive partner function) is blocked by no
edge. -/
def StableRoommatesWithTiesFeasible (i : StableRoommatesWithTiesInstance) : Prop :=
  ∃ μ : Fin i.1 → Fin i.1, Function.Involutive μ ∧ ∀ v w, ¬ Blocks i μ v w

open Classical in
/-- STABLE ROOMMATES WITH TIES as a decision problem over bitstrings. -/
noncomputable def stableRoommatesWithTiesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StableRoommatesWithTiesInstance) x with
  | some i => decide (WellFormed i ∧ StableRoommatesWithTiesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.StableRoommatesWithTies
