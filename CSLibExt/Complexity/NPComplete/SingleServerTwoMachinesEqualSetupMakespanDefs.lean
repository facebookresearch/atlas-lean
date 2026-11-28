/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, equal setups, makespan (`P2;S1|s_i=s|Cmax`): definitions
is NP-complete

Source:
N. G. Hall, C. N. Potts and C. Sriskandarajah, "Parallel machine scheduling with a common
server", Discrete Applied Mathematics 102 (2000), 223-243,
doi:10.1016/S0166-218X(99)00206-1;
P. Brucker, C. Dhaenens-Flipo, S. Knust, S. A. Kravchenko and F. Werner, "Complexity results
for parallel machine problems with a single server", Journal of Scheduling 5 (2002), 429-457,
doi:10.1002/jos.120 (the model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel machine problems with a single server" (`P2;S1|s_i=s|C_max`, minimal NP-hard
in the strong sense, citing Hall et al. 2000).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualSetupMakespan

/-- A single-server schedule of the jobs `Fin n` on the machines `Fin m`, with setup times `s`
and processing times `p`: job `j` is set up on machine `μ j` during `[t j, t j + s j)` and then
processed there during `[t j + s j, t j + s j + p j)`. The server performs one setup at a time
(the setup intervals of different jobs are disjoint), and each machine handles one job at a time
(different jobs on the same machine occupy disjoint intervals `[t j, t j + s j + p j)`). -/
def IsSingleServerSchedule {n m : ℕ} (s p : Fin n → ℕ) (μ : Fin n → Fin m) (t : Fin n → ℕ) :
    Prop :=
  (∀ j k, j ≠ k → Disjoint (Finset.Ico (t j) (t j + s j)) (Finset.Ico (t k) (t k + s k))) ∧
    ∀ j k, j ≠ k → μ j = μ k →
      Disjoint (Finset.Ico (t j) (t j + s j + p j)) (Finset.Ico (t k) (t k + s k + p k))

/-- An instance `(s, p, K)`: the common setup time `s`, the processing times `p_i` of the jobs
`0, …, n - 1`, one per entry (`n` is the length of the list), and the bound `K`. -/
abbrev SingleServerTwoMachinesEqualSetupMakespanInstance := ℕ × List ℕ × ℕ

/-- Every instance is well-formed: the setup time, the processing times and the bound are
nonnegative integers by their type. -/
def WellFormed (_i : SingleServerTwoMachinesEqualSetupMakespanInstance) : Prop := True

/-- Some single-server schedule on two machines, with setup time `s` for every job, completes
every job `j` by `K`: `t j + s + p_j ≤ K`. -/
def SingleServerTwoMachinesEqualSetupMakespanFeasible
    (i : SingleServerTwoMachinesEqualSetupMakespanInstance) : Prop :=
  ∃ μ : Fin i.2.1.length → Fin 2, ∃ t : Fin i.2.1.length → ℕ,
    IsSingleServerSchedule (fun _ => i.1) i.2.1.get μ t ∧
      ∀ j, t j + i.1 + i.2.1.get j ≤ i.2.2

open Classical in
/-- `P2;S1|s_i=s|Cmax` as a decision problem over bitstrings. -/
noncomputable def singleServerTwoMachinesEqualSetupMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SingleServerTwoMachinesEqualSetupMakespanInstance) x with
  | some i => decide (WellFormed i ∧ SingleServerTwoMachinesEqualSetupMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualSetupMakespan
