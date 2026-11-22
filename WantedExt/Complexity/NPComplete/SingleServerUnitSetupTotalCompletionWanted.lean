/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARALLEL MACHINES WITH A SINGLE SERVER, unit setups, total completion time
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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleServerUnitSetupTotalCompletion

/-!
# PARALLEL MACHINES WITH A SINGLE SERVER, unit setups, total completion time, is NP-complete

INSTANCE: `m` identical parallel machines (`m` part of the input), each processing at most one
job at a time; jobs `1, …, n`, job `i` with a processing time `p_i ∈ ℤ₀⁺`; and an integer bound
`K`. Each job is processed on one machine, without interruption. Immediately before its
processing, job `i` must be loaded (set up) on its machine, which takes the setup time
`s_i = 1`; all setups are done by a single server, which handles at most one job at a time.
QUESTION: is there a feasible schedule whose total completion time `Σ_i C_i` is at most `K`,
where `C_i` is the completion time of job `i`?

This is `P;S1|s_i=1|ΣC_i` in the notation of Brucker et al. and of the Brucker-Knust
classification. A schedule gives each job `i` a machine `μ(i) ∈ Fin m` and the start time
`t(i)` of its setup: the setup occupies the server and the machine `μ(i)` during
`[t(i), t(i) + 1)`, the processing occupies `μ(i)` during `[t(i) + 1, t(i) + 1 + p_i)`, and
`C_i = t(i) + 1 + p_i`. So two different jobs have different setup start times (the server
handles one unit setup at a time), and two different jobs on the same machine occupy disjoint
intervals `[t(i), C_i)`. Integral start times lose no generality: for fixed job orders on the
server and on the machines, the earliest start times are integral. Binary encoding of all
numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **PARALLEL MACHINES WITH A SINGLE SERVER, unit setups, total completion time
(`P;S1|s_i=1|ΣC_i`) is NP-complete.** Source: Brucker, Dhaenens-Flipo, Knust, Kravchenko and
Werner (2002), as recorded in the Brucker-Knust classification. -/
public theorem_wanted singleServerUnitSetupTotalCompletion_npComplete :
    singleServerUnitSetupTotalCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L singleServerUnitSetupTotalCompletionDec

end MetaMathlibExt.Complexity.NPComplete.SingleServerUnitSetupTotalCompletion
