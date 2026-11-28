/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, unit processing times, total weighted tardiness
(`P2;S1|p_i=1|Σw_iT_i`): definitions

Source:
N. G. Hall, C. N. Potts and C. Sriskandarajah, "Parallel machine scheduling with a common
server", Discrete Applied Mathematics 102 (2000), 223-243, doi:10.1016/S0166-218X(99)00206-1;
P. Brucker, C. Dhaenens-Flipo, S. Knust, S. A. Kravchenko and F. Werner, "Complexity results
for parallel machine problems with a single server", Journal of Scheduling 5 (2002), 429-457,
doi:10.1002/jos.120 (the model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel machine problems with a single server" (`P2;S1|p_i=1|Σw_iT_i`, minimal NP-hard
in the strong sense: "Single-machine problem, Hall et al. (2000)");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS5] SEQUENCING TO MINIMIZE WEIGHTED TARDINESS
(the single-machine problem).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineSingleServerUnitWeightedTardiness

/-- An instance `(jobs, K)`: job `j` is the `j`-th triple `(s_j, w_j, d_j)` of setup time,
weight and due date (every processing time is `1`), and `K` is the bound. -/
abbrev TwoMachineSingleServerUnitInstance := List (ℕ × ℕ × ℕ) × ℕ

/-- A schedule of the jobs `Fin n`, with setup times `s` and processing times `p`, on `m`
identical parallel machines with a single server: job `j` is processed on machine `μ j`, and
its setup starts at `t j`, occupying the server during `[t j, t j + s j)`, immediately followed
by its processing; job `j` occupies machine `μ j` during `[t j, t j + s j + p j)`. Setups of
different jobs are disjoint, and different jobs on the same machine are disjoint. -/
def IsSingleServerSchedule (m : ℕ) {n : ℕ} (s p : Fin n → ℕ) (μ : Fin n → Fin m)
    (t : Fin n → ℕ) : Prop :=
  (∀ j k, j ≠ k → Disjoint (Finset.Ico (t j) (t j + s j)) (Finset.Ico (t k) (t k + s k))) ∧
    ∀ j k, j ≠ k → μ j = μ k →
      Disjoint (Finset.Ico (t j) (t j + s j + p j)) (Finset.Ico (t k) (t k + s k + p k))

/-- Some schedule on two machines with a single server and unit processing times has total
weighted tardiness `Σ_j w_j · max(0, C_j - d_j)` at most `K`, where `C_j = t j + s_j + 1`
(natural-number subtraction truncates at `0`). -/
def TwoMachineSingleServerUnitWeightedTardinessFeasible
    (i : TwoMachineSingleServerUnitInstance) : Prop :=
  ∃ μ : Fin i.1.length → Fin 2, ∃ t : Fin i.1.length → ℕ,
    IsSingleServerSchedule 2 (fun j => (i.1.get j).1) (fun _ => 1) μ t ∧
      (∑ j, (i.1.get j).2.1 * (t j + (i.1.get j).1 + 1 - (i.1.get j).2.2)) ≤ i.2

open Classical in
/-- `P2;S1|p_i=1|Σw_iT_i` as a decision problem over bitstrings. -/
noncomputable def twoMachineSingleServerUnitWeightedTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoMachineSingleServerUnitInstance) x with
  | some i => decide (TwoMachineSingleServerUnitWeightedTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoMachineSingleServerUnitWeightedTardiness
