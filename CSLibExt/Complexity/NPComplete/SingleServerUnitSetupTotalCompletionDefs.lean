/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARALLEL MACHINES WITH A SINGLE SERVER, unit setups, total completion time: definitions
(`P;S1|s_i=1|ΣC_i`) is NP-complete

Source:
P. Brucker, C. Dhaenens-Flipo, S. Knust, S. A. Kravchenko and F. Werner, "Complexity results
for parallel machine problems with a single server", Journal of Scheduling 5 (2002), 429-457,
doi:10.1002/jos.120;
N. G. Hall, C. N. Potts and C. Sriskandarajah, "Parallel machine scheduling with a common
server", Discrete Applied Mathematics 102 (2000), 223-243, doi:10.1016/S0166-218X(99)00206-1
(the model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel machine problems with a single server" (`P;S1|s_i=1|ΣC_i`, minimal NP-hard in
the strong sense, citing Brucker et al. 2002).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleServerUnitSetupTotalCompletion

/-- An instance `(m, p, K)`: the number `m` of machines, the processing times `p_i` of the jobs
`0, …, n - 1` (`n` is the length of the list), and the bound `K`. -/
abbrev SingleServerUnitSetupTotalCompletionInstance := ℕ × List ℕ × ℕ

/-- Well-formedness of an instance: there is at least one machine. -/
def WellFormed (i : SingleServerUnitSetupTotalCompletionInstance) : Prop :=
  0 < i.1

/-- Some schedule, a machine `μ j` and a setup start time `t j` for each job `j`, has total
completion time `Σ_j (t j + 1 + p_j)` at most `K`: different jobs start their unit setups at
different times (single server), and different jobs on the same machine occupy disjoint
intervals `[t j, t j + 1 + p_j)` (setup followed immediately by processing). -/
def SingleServerUnitSetupTotalCompletionFeasible
    (i : SingleServerUnitSetupTotalCompletionInstance) : Prop :=
  ∃ μ : Fin i.2.1.length → Fin i.1, ∃ t : Fin i.2.1.length → ℕ,
    (∀ j k, j ≠ k → t j ≠ t k) ∧
    (∀ j k, j ≠ k → μ j = μ k →
      t j + 1 + i.2.1.get j ≤ t k ∨ t k + 1 + i.2.1.get k ≤ t j) ∧
    (∑ j, (t j + 1 + i.2.1.get j)) ≤ i.2.2

open Classical in
/-- `P;S1|s_i=1|ΣC_i` as a decision problem over bitstrings. -/
noncomputable def singleServerUnitSetupTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SingleServerUnitSetupTotalCompletionInstance) x with
  | some i => decide (WellFormed i ∧ SingleServerUnitSetupTotalCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SingleServerUnitSetupTotalCompletion
