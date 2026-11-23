/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP O2|r_i|Cmax is NP-complete

Source:
E. L. Lawler, J. K. Lenstra, and A. H. G. Rinnooy Kan, "Minimizing maximum lateness in a
two-machine open shop", Mathematics of Operations Research 6 (1981), 153-158,
doi:10.1287/moor.6.1.153; Erratum, Mathematics of Operations Research 7 (1982), 635,
doi:10.1287/moor.7.4.635;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
table "Open-shop problems without preemption" (`O2|r_i|C_max`, minimal NP-hard in the strong
sense, credited to Lawler, Lenstra, and Rinnooy Kan 1981, 1982);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS14] OPEN-SHOP SCHEDULING (the
parent problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.FlowShopSchedulingWanted
public import WantedExt.Complexity.NPComplete.TwoMachineFlowShopReleaseDatesWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineOpenShopReleaseDates

open TwoMachineFlowShopReleaseDates (TwoMachineFlowShopReleaseDatesInstance WellFormed)

/-!
# OPEN SHOP O2|r_i|Cmax is NP-complete

INSTANCE: two machines `M₁, M₂` in an open shop and jobs `j`, each consisting of an operation of
length `p₁ⱼ ∈ ℤ₀⁺` on `M₁` and an operation of length `p₂ⱼ ∈ ℤ₀⁺` on `M₂`, which may be processed
in either order but not at the same time; each machine processes at most one operation at a
time; job `j` has a release date `rⱼ ∈ ℤ₀⁺` and cannot start before it; and a bound `K`.
QUESTION: is there a feasible schedule with makespan `max_j Cⱼ ≤ K`, where `Cⱼ` is the
completion time of job `j` (of its last operation)?

This is Brucker and Knust's `O2|r_i|C_max`, which they classify as NP-hard in the strong sense,
citing Lawler, Lenstra, and Rinnooy Kan (1981, with their 1982 erratum); it is the time reversal
of `O2||L_max` (the operations run backwards from the bound, due dates becoming release dates).
It is OPEN-SHOP SCHEDULING ([SS14], `OpenShopSchedulingWanted`) with `m = 2` processors, the
deadline `D` read as the makespan bound `K` (every task ends by `D` iff the makespan is at most
`D`), and release dates added. The instance type and its well-formedness (`m = 2`, two tasks per
job, one release date per job; all data, `K` included, may be `0`) are those of the flow shop
`F2|r_j|C_max` (`TwoMachineFlowShopReleaseDatesWanted`), which pairs the [SS14]/[SS15] instance
`(m, task lengths per job, D)` with the list of release dates. The schedule conditions are that
module's, with its processor-order condition replaced by the open-shop condition: every task
ends by `D`, two tasks on one processor do not overlap, the two tasks of a job do not overlap
(non-overlap read, as there, as `s + l ≤ s'` or `s' + l' ≤ s`), and `rⱼ ≤ σ(p, j)` for both
tasks of job `j`. Processors are `Fin m`, jobs `Fin |J|`. Binary
encoding of all numbers. Membership in NP is the certificate argument: the `2n` start times,
each at most `K`, are checked in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some open-shop schedule `σ p j` (start of job `j`'s task on processor `p`) ends every task
by `K`, runs one task at a time on each processor, never runs the two tasks of a job at the same
time, and starts both tasks of every job `j` no earlier than its release date `rⱼ`. -/
def TwoMachineOpenShopReleaseDatesFeasible (i : TwoMachineFlowShopReleaseDatesInstance) :
    Prop :=
  ∃ σ : Fin i.1.1 → Fin i.1.2.1.length → ℕ,
    (∀ p j, σ p j + FlowShopScheduling.len i.1 p j ≤ i.1.2.2) ∧
    (∀ p j k, j ≠ k → σ p j + FlowShopScheduling.len i.1 p j ≤ σ p k ∨
      σ p k + FlowShopScheduling.len i.1 p k ≤ σ p j) ∧
    (∀ j p q, p ≠ q → σ p j + FlowShopScheduling.len i.1 p j ≤ σ q j ∨
      σ q j + FlowShopScheduling.len i.1 q j ≤ σ p j) ∧
    ∀ (p : Fin i.1.1) (j : Fin i.1.2.1.length), i.2.getD j 0 ≤ σ p j

open Classical in
/-- OPEN SHOP O2|r_i|Cmax as a decision problem over bitstrings. -/
noncomputable def twoMachineOpenShopReleaseDatesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoMachineFlowShopReleaseDatesInstance) x with
  | some i => decide (WellFormed i ∧ TwoMachineOpenShopReleaseDatesFeasible i)
  | none => false

/-- **OPEN SHOP O2|r_i|Cmax is NP-complete.** Source: Lawler, Lenstra, and Rinnooy Kan (1981;
erratum 1982); Brucker and Knust's classification (`O2|r_i|C_max`, strongly NP-hard). -/
public theorem_wanted twoMachineOpenShopReleaseDates_npComplete :
    twoMachineOpenShopReleaseDatesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoMachineOpenShopReleaseDatesDec

end MetaMathlibExt.Complexity.NPComplete.TwoMachineOpenShopReleaseDates
