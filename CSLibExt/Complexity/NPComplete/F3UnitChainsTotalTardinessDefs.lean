/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLOW SHOP `F3|p_ij=1;chains|ΣT_i`: definitions

Source:
P. Brucker and S. Knust, "Complexity results for single-machine problems with positive
finish-start time-lags", Computing 63 (1999), 299-316, doi:10.1007/s006070050036; recorded as
strongly NP-hard (a minimal NP-hard problem) in P. Brucker and S. Knust, *Complexity results for
scheduling problems*, class "Flow-shop problems without preemption" (University of Osnabrück,
http://www2.informatik.uni-osnabrueck.de/knust/class/), problem `F3|p_ij=1;chains|ΣT_i`, credited
to Brucker and Knust (1999).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CSLibExt.Complexity.NPComplete.F3UnitChainsLateJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.F3UnitChainsTotalTardiness

open F3UnitChainsLateJobs (IsSchedule)

/-- An instance `(d, chains, K)`: due dates, chain arcs `(i, j)` (job `i` immediately precedes job
`j`) and the bound `K`, as in `F3UnitChainsLateJobs.F3UnitChainsLateJobsInstance`. -/
abbrev F3UnitChainsTotalTardinessInstance := F3UnitChainsLateJobs.F3UnitChainsLateJobsInstance

/-- Well-formedness: the arcs form chains on the jobs (`F3UnitChainsLateJobs.WellFormed`). -/
def WellFormed (i : F3UnitChainsTotalTardinessInstance) : Prop :=
  F3UnitChainsLateJobs.WellFormed i

/-- Some feasible schedule (`F3UnitChainsLateJobs.IsSchedule`) has total tardiness at most `K`:
the sum over the jobs of `C_j - d_j` truncated at `0` (natural-number subtraction), with
`C_j = S j 2 + 1`. -/
def F3UnitChainsTotalTardinessFeasible (i : F3UnitChainsTotalTardinessInstance) : Prop :=
  ∃ S : Fin i.1.length → Fin 3 → ℕ, IsSchedule i.1.length i.2.1 S ∧
    ∑ j, (S j 2 + 1 - i.1.get j) ≤ i.2.2

open Classical in
/-- `F3|p_ij=1;chains|ΣT_i` as a decision problem over bitstrings. -/
noncomputable def f3UnitChainsTotalTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := F3UnitChainsTotalTardinessInstance) x with
  | some i => decide (WellFormed i ∧ F3UnitChainsTotalTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.F3UnitChainsTotalTardiness
