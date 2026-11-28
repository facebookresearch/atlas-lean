/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, equal processing times, total completion time: definitions
(`P2;S1|p_i=p|ΣC_i`) is NP-complete

Source:
P. Brucker, C. Dhaenens-Flipo, S. Knust, S. A. Kravchenko and F. Werner, "Complexity results
for parallel machine problems with a single server", Journal of Scheduling 5 (2002), 429-457,
doi:10.1002/jos.120;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel machine problems with a single server" (`P2;S1|p_i=p|ΣC_i`, minimal NP-hard,
citing Brucker et al. 2002).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CSLibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualSetupMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualProcessingTotalCompletion

open MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualSetupMakespan
  (IsSingleServerSchedule)

/-- An instance `(p, s, K)`: the common processing time `p`, the setup times `s_i` of the jobs
`0, …, n - 1`, one per entry (`n` is the length of the list), and the bound `K`. -/
abbrev SingleServerTwoMachinesEqualProcessingTotalCompletionInstance := ℕ × List ℕ × ℕ

/-- Well-formedness of an instance: the common processing time `p` is positive. -/
def WellFormed (i : SingleServerTwoMachinesEqualProcessingTotalCompletionInstance) : Prop :=
  0 < i.1

/-- Some single-server schedule on two machines, with setup times `s_j` and processing time `p`
for every job, has total completion time `Σ_j (t j + s_j + p)` at most `K`. -/
def SingleServerTwoMachinesEqualProcessingTotalCompletionFeasible
    (i : SingleServerTwoMachinesEqualProcessingTotalCompletionInstance) : Prop :=
  ∃ μ : Fin i.2.1.length → Fin 2, ∃ t : Fin i.2.1.length → ℕ,
    IsSingleServerSchedule i.2.1.get (fun _ => i.1) μ t ∧
      (∑ j, (t j + i.2.1.get j + i.1)) ≤ i.2.2

open Classical in
/-- `P2;S1|p_i=p|ΣC_i` as a decision problem over bitstrings. -/
noncomputable def singleServerTwoMachinesEqualProcessingTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SingleServerTwoMachinesEqualProcessingTotalCompletionInstance) x with
  | some i =>
    decide (WellFormed i ∧ SingleServerTwoMachinesEqualProcessingTotalCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualProcessingTotalCompletion
