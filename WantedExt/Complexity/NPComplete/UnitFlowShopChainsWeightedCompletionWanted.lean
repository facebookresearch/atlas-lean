/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLOW SHOP F2|p_ij=1;chains|Σw_iC_i is NP-complete

Source:
V. S. Tanaev, Y. N. Sotskov and V. A. Strusevich, *Scheduling Theory. Multi-Stage Systems*,
Mathematics and its Applications 285, Kluwer Academic Publishers, Dordrecht (1994),
doi:10.1007/978-94-011-1192-8;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `f_nop` (flow-shop problems without preemption), Universität Osnabrück (last update 2006).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import WantedExt.Complexity.NPComplete.TwoProcessorUnitFlowShopChainsTardinessWanted
public import WantedExt.Complexity.NPComplete.UnitFlowShopTransportationDelaysWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitFlowShopChainsWeightedCompletion

open UnitFlowShopTransportationDelays (IsUnitFlowShopSchedule)
open TwoProcessorUnitFlowShopChainsTardiness
  (TwoProcessorUnitFlowShopChainsTardinessInstance Job Arc WellFormed)

/-!
# FLOW SHOP F2|p_ij=1;chains|Σw_iC_i is NP-complete

INSTANCE: `n` jobs, each consisting of two unit-time operations, the first on machine `M₁` and
the second on machine `M₂` (the second cannot start before the first is completed); a
precedence relation on the jobs consisting of disjoint chains (each job has at most one
immediate predecessor and at most one immediate successor), where `i` preceding `j` means that
no operation of `j` starts before every operation of `i` is completed; for each job `j` a weight
`w_j ∈ ℤ₀⁺`; a bound `K`. Each machine processes at most one operation at a time. QUESTION: is
there a schedule whose total weighted completion time `∑_j w_j C_j` is at most `K`, where `C_j`
is the completion time of job `j`'s second operation?

In the three-field notation this is `F2|p_ij=1; chains|∑ w_i C_i`. Brucker and Knust's
classification lists it as minimal strongly NP-hard, citing Tanaev, Sotskov and Strusevich
(1994); the book itself was not available to this formalization.

The instance, jobs, chain arcs and well-formedness are those of
`TwoProcessorUnitFlowShopChainsTardinessWanted` (`F2|p_ij=1; chains|∑ T_i`), with the job list
carrying weights instead of due dates: the instance type
`TwoProcessorUnitFlowShopChainsTardinessInstance` (the `j`-th listed number is now `w_j`), `Job`,
the immediate-predecessor arcs `Arc`, and `WellFormed` (every arc names two jobs, at most one
immediate successor and one immediate predecessor per job, no cycle) are reused. A schedule is
`IsUnitFlowShopSchedule` (from `UnitFlowShopTransportationDelaysWanted`) with zero delays that
obeys the chains. Start times are natural numbers: with integer data, shifting every operation of a
feasible schedule as early as its machine order allows gives an integral schedule with no later
completion times, so this does not change the answer. Binary encoding of all numbers (the
problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The weight `w_j` of job `j`: the `j`-th listed number. -/
def weight (i : TwoProcessorUnitFlowShopChainsTardinessInstance) (j : Job i) : ℕ :=
  i.1.get j

/-- Some unit-time two-machine flow-shop schedule obeys the chains (job `b` starts on `M₁` only
after its immediate predecessor `a` completes on `M₂`) and has total weighted completion time
`∑_j w_j C_j` at most `K`, where `C_j = σ 1 j + 1`. -/
def UnitFlowShopChainsWeightedCompletionFeasible
    (i : TwoProcessorUnitFlowShopChainsTardinessInstance) : Prop :=
  ∃ σ : Fin 2 → Job i → ℕ, IsUnitFlowShopSchedule (fun _ => 0) σ ∧
    (∀ a b, Arc i a b → σ 1 a + 1 ≤ σ 0 b) ∧
    ∑ j, weight i j * (σ 1 j + 1) ≤ i.2.2

open Classical in
/-- FLOW SHOP `F2|p_ij=1;chains|∑ w_i C_i` as a decision problem over bitstrings. -/
noncomputable def unitFlowShopChainsWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorUnitFlowShopChainsTardinessInstance) x with
  | some i => decide (WellFormed i ∧ UnitFlowShopChainsWeightedCompletionFeasible i)
  | none => false

/-- **FLOW SHOP `F2|p_ij=1;chains|∑ w_i C_i` is NP-complete.** Source: Tanaev, Sotskov and
Strusevich (1994); Brucker and Knust, scheduling classification, class `f_nop`. -/
public theorem_wanted unitFlowShopChainsWeightedCompletion_npComplete :
    unitFlowShopChainsWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitFlowShopChainsWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.UnitFlowShopChainsWeightedCompletion
