/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR FLOW-SHOP MAXIMUM LATENESS is NP-complete

Source:
J. K. Lenstra, A. H. G. Rinnooy Kan, and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362, doi:10.1016/S0167-5060(08)70743-X,
Theorem 1(k) and Theorem 4(c) in the preprint, Mathematisch Centrum report BW 43/75 (1975),
https://ir.cwi.nl/pub/9725 (KNAPSACK reduces to `n|1|r_n ≥ 0|Lmax`, which reduces to
`n|2|F|Lmax`: `F2||Lmax`);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
table "Flow-shop problems without preemption" (`F2||Lmax`, minimal NP-hard, credited to Lenstra,
Rinnooy Kan, and Brucker 1977).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoProcessorFlowShopMaximumLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorFlowShopMaximumLateness

/-!
# TWO-PROCESSOR FLOW-SHOP MAXIMUM LATENESS is NP-complete

INSTANCE: a set of jobs `J₁, …, Jₙ` in a two-machine flow shop, job `Jⱼ` consisting of an
operation on machine `M₁` with processing time `pⱼ₁` followed by an operation on machine `M₂`
with processing time `pⱼ₂`, a due date `dⱼ` for each job, and an integer `y`; all processing
times and due dates are nonnegative integers. QUESTION: is there a schedule (each machine
handles at most one job at a time, and the operation of `Jⱼ` on `M₂` starts only after its
operation on `M₁` is completed) whose maximum lateness `L_max = maxⱼ (Cⱼ - dⱼ)` is at most `y`,
`Cⱼ` being the completion time of `Jⱼ` on `M₂`?

This is `F2||Lmax` in the notation of Lenstra, Rinnooy Kan, and Brucker (`n|2|F|Lmax`), with the
optimization problem replaced, as in their paper, by the recognition problem "is there a
schedule with value `≤ y`". A schedule is given by the starting times `s₁ⱼ`, `s₂ⱼ ∈ ℤ₀⁺` of the
two operations of job `j`. That each machine handles at most one job at a time is read, as in
`FlowShopSchedulingWanted`, as non-overlap of the operations of two distinct jobs on the same
machine (`s + p ≤ s'` or `s' + p' ≤ s`). The bound `y` is an integer, encoded as a pair
`(y⁺, y⁻)` of naturals representing `y⁺ - y⁻`, as in `ZeroOneILPWanted`; `Cⱼ - dⱼ ≤ y⁺ - y⁻` is
stated over `ℕ` as `Cⱼ + y⁻ ≤ dⱼ + y⁺`. The flow-shop schedule predicates of
`FlowShopSchedulingWanted` and `NoWaitFlowShopSchedulingWanted` carry the overall deadline in
their instance and schedule conditions, so they do not apply to a lateness objective. Jobs are
`Fin n`. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO-PROCESSOR FLOW-SHOP MAXIMUM LATENESS is NP-complete.** Source: Lenstra, Rinnooy Kan,
and Brucker (1977), Theorems 1(k) and 4(c); Brucker and Knust's classification (`F2||Lmax`). -/
public theorem_wanted twoProcessorFlowShopMaximumLateness_npComplete :
    twoProcessorFlowShopMaximumLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorFlowShopMaximumLatenessDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorFlowShopMaximumLateness
