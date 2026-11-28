/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM NASH SOCIAL WELFARE with additive valuations: definitions

Source:
S. Ramezani and U. Endriss, "Nash social welfare in multiagent resource allocation",
Agent-Mediated Electronic Commerce (AMEC/TADA 2009), Lecture Notes in Business Information
Processing 59 (2010), 117-131, doi:10.1007/978-3-642-15117-0_9 (Section 1.2: allocations and
the Nash collective utility function; Section 1.3.2: the decision problem Nash).
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumNashSocialWelfare

/-- An instance `(m, v, W)`: the number `m` of goods (goods `Fin m`), the value matrix `v` with
one row `v_i = [v_i(0), …, v_i(m - 1)]` per agent, and the bound `W`. -/
abbrev MaximumNashSocialWelfareInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: there is at least one agent and every row of the value
matrix has one entry per good. -/
def WellFormed (i : MaximumNashSocialWelfareInstance) : Prop :=
  0 < i.2.1.length ∧ ∀ row ∈ i.2.1, row.length = i.1

/-- The utility of agent `a` under the allocation `f : goods → agents`: the sum of `a`'s values
of the goods `f` gives it (`getD` reads the value matrix; under `WellFormed` every entry
exists). -/
def utility (i : MaximumNashSocialWelfareInstance) (f : Fin i.1 → Fin i.2.1.length)
    (a : Fin i.2.1.length) : ℕ :=
  ∑ r ∈ Finset.univ.filter (fun r => f r = a), (i.2.1[a].getD r 0)

/-- Some allocation of all goods has Nash social welfare, the product of the agents' utilities,
at least `W`. -/
def MaximumNashSocialWelfareFeasible (i : MaximumNashSocialWelfareInstance) : Prop :=
  ∃ f : Fin i.1 → Fin i.2.1.length, i.2.2 ≤ ∏ a, utility i f a

open Classical in
/-- MAXIMUM NASH SOCIAL WELFARE as a decision problem over bitstrings. -/
noncomputable def maximumNashSocialWelfareDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumNashSocialWelfareInstance) x with
  | some i => decide (WellFormed i ∧ MaximumNashSocialWelfareFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaximumNashSocialWelfare
