/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIFORM PARALLEL MACHINE SCHEDULING, total weighted completion time (`Qm||Σw_iC_i`) is: definitions
NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel machine problems without preemption" (`Qm||Σw_iC_i` maximal pseudopolynomially
solvable, citing Lawler, Lenstra, Rinnooy Kan and Shmoys (1989); `P2||Σw_iC_i` minimal NP-hard,
citing Bruno et al. (1974));
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling problems",
Annals of Discrete Mathematics 1 (1977), 343-362, doi:10.1016/S0167-5060(08)70743-X,
Theorem 3(b) (PARTITION reduces to `P2||Σw_iC_i`);
J. Bruno, E. G. Coffman, Jr. and R. Sethi, "Scheduling independent tasks to reduce mean
finishing time", Communications of the ACM 17 (1974), 382-387, doi:10.1145/361011.361064;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS13] SCHEDULING TO MINIMIZE WEIGHTED
COMPLETION TIME (comment: remains NP-complete for `m = 2`);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 1 (notation).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UniformMachinesReleaseMakespanDefs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Field.Rat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UniformMachinesWeightedCompletion

open MetaMathlibExt.Complexity.NPComplete.MultiprocessorScheduling (Task)
open MetaMathlibExt.Complexity.NPComplete.MultiprocessorSchedulingSpeedFactors
  (MultiprocessorSchedulingSpeedFactorsInstance toMultiprocessorScheduling)
open MetaMathlibExt.Complexity.NPComplete.UniformMachinesReleaseMakespan
  (completion IsNonOverlapping)

/-- An instance: the processing times `p_i` (job `i` is the `i`-th entry), the speeds (the
`k`-th entry `(a, b)` is `s_k = a / b`) and the bound `K`, as a
`MultiprocessorSchedulingSpeedFactors` instance; and the weights `w_i`, one per job. -/
abbrev UniformMachinesWeightedCompletionInstance :=
  MultiprocessorSchedulingSpeedFactorsInstance × List ℕ

/-- The weight `w_t` of job `t` (the `t`-th entry of the weight list). -/
def weight (i : UniformMachinesWeightedCompletionInstance)
    (t : Task (toMultiprocessorScheduling i.1)) : ℕ :=
  i.2.getD t 0

/-- Some schedule, a machine `μ(t)` and a start time `S(t) ≥ 0` for each job `t`, has total
weighted completion time `Σ_t w_t C_t` at most `K`, where jobs on the same machine do not
overlap. -/
def UniformMachinesWeightedCompletionFeasible (i : UniformMachinesWeightedCompletionInstance) :
    Prop :=
  ∃ μ : Task (toMultiprocessorScheduling i.1) → Fin i.1.2.1.length,
    ∃ S : Task (toMultiprocessorScheduling i.1) → ℚ,
      IsNonOverlapping i.1 μ S ∧ (∀ t, 0 ≤ S t) ∧
        ∑ t, (weight i t : ℚ) * completion i.1 μ S t ≤ i.1.2.2

/-- Well-formedness of an instance for the fixed number `m` of machines: the
`UniformMachinesReleaseMakespan` conditions (positive processing times, exactly `m` positive
speeds, one entry of the second list, here a weight, per job), every weight is positive, and
`K` is positive. -/
def WellFormed (m : ℕ) (i : UniformMachinesWeightedCompletionInstance) : Prop :=
  UniformMachinesReleaseMakespan.WellFormed m i ∧ (∀ w ∈ i.2, 0 < w) ∧ 0 < i.1.2.2

open Classical in
/-- UNIFORM PARALLEL MACHINE SCHEDULING on `m` machines, total weighted completion time
(`Qm||Σw_iC_i`), as a decision problem over bitstrings. -/
noncomputable def uniformMachinesWeightedCompletionDec (m : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UniformMachinesWeightedCompletionInstance) x with
  | some i => decide (WellFormed m i ∧ UniformMachinesWeightedCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UniformMachinesWeightedCompletion
