/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP O2||Lmax is NP-complete

Source:
E. L. Lawler, J. K. Lenstra, and A. H. G. Rinnooy Kan, "Minimizing maximum lateness in a
two-machine open shop", Mathematics of Operations Research 6 (1981), 153-158,
doi:10.1287/moor.6.1.153; Erratum, Mathematics of Operations Research 7 (1982), 635,
doi:10.1287/moor.7.4.635 (the nonpreemptive problem is NP-hard);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
table "Open-shop problems without preemption" (`O2||L_max`, minimal NP-hard in the strong sense,
credited to Lawler, Lenstra, and Rinnooy Kan 1981, 1982).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.TwoProcessorFlowShopMaximumLatenessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorOpenShopMaximumLateness

open TwoProcessorFlowShopMaximumLateness
  (TwoProcessorFlowShopMaximumLatenessInstance Job time₁ time₂ dueDate WellFormed)

/-!
# OPEN SHOP O2||Lmax is NP-complete

INSTANCE: jobs `J₁, …, Jₙ` in a two-machine open shop, job `Jⱼ` consisting of an operation on
machine `M₁` with processing time `pⱼ₁` and an operation on machine `M₂` with processing time
`pⱼ₂`, which may be processed in either order but not at the same time; each machine processes
at most one operation at a time; a due date `dⱼ` for each job; and an integer bound `y`; all
processing times and due dates are nonnegative integers. QUESTION: is there a schedule whose
maximum lateness `L_max = maxⱼ (Cⱼ - dⱼ)` is at most `y`, `Cⱼ` being the completion time of
`Jⱼ` (of its last operation)?

This is Brucker and Knust's `O2||L_max`. Lawler, Lenstra, and Rinnooy Kan (1981, with their
1982 erratum on the proof in §3) show the nonpreemptive problem NP-hard; Brucker and Knust
classify it as NP-hard in the strong sense, citing both. It differs from the
flow shop `F2||L_max` (`TwoProcessorFlowShopMaximumLatenessWanted`) only in the order of a job's
two operations, which is free here. The instance type (each job listed as the triple
`(pⱼ₁, pⱼ₂, dⱼ)`, the bound `y` as a pair `(y⁺, y⁻)` of naturals standing for `y⁺ - y⁻`), the
accessors `time₁`, `time₂`, `dueDate` and the well-formedness (every instance) are reused from
that module. A schedule is given by the starting times `s₁ⱼ`, `s₂ⱼ ∈ ℤ₀⁺` of the two operations
of job `j`. Non-overlap of two operations (on one machine, or of one job) is read, as in that
module, as `s + p ≤ s'` or `s' + p' ≤ s`. `Cⱼ - dⱼ ≤ y` for the later of the two completions is
stated for both operations of `j`, over `ℕ` as `s + p + y⁻ ≤ dⱼ + y⁺`. Jobs are `Fin n`. Binary
encoding of all numbers. Membership in NP is the certificate argument: the `2n` starting times
(each below `dⱼ + y⁺` for its job `j`) are checked in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some schedule, with starting times `s₁ j` on `M₁` and `s₂ j` on `M₂`, runs one operation at
a time on each machine, never runs the two operations of a job at the same time, and completes
both operations of every job `j` with lateness `Cⱼ - dⱼ ≤ y⁺ - y⁻`. -/
def TwoProcessorOpenShopMaximumLatenessFeasible
    (i : TwoProcessorFlowShopMaximumLatenessInstance) : Prop :=
  ∃ s₁ s₂ : Job i → ℕ,
    (∀ j k, j ≠ k → s₁ j + time₁ i j ≤ s₁ k ∨ s₁ k + time₁ i k ≤ s₁ j) ∧
    (∀ j k, j ≠ k → s₂ j + time₂ i j ≤ s₂ k ∨ s₂ k + time₂ i k ≤ s₂ j) ∧
    (∀ j, s₁ j + time₁ i j ≤ s₂ j ∨ s₂ j + time₂ i j ≤ s₁ j) ∧
    ∀ j, s₁ j + time₁ i j + i.2.2 ≤ dueDate i j + i.2.1 ∧
      s₂ j + time₂ i j + i.2.2 ≤ dueDate i j + i.2.1

open Classical in
/-- OPEN SHOP O2||Lmax as a decision problem over bitstrings. -/
noncomputable def twoProcessorOpenShopMaximumLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorFlowShopMaximumLatenessInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorOpenShopMaximumLatenessFeasible i)
  | none => false

/-- **OPEN SHOP O2||Lmax is NP-complete.** Source: Lawler, Lenstra, and Rinnooy Kan (1981;
erratum 1982); Brucker and Knust's classification (`O2||L_max`, strongly NP-hard). -/
public theorem_wanted twoProcessorOpenShopMaximumLateness_npComplete :
    twoProcessorOpenShopMaximumLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorOpenShopMaximumLatenessDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorOpenShopMaximumLateness
