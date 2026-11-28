/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR NO-WAIT FLOW-SHOP MAXIMUM LATENESS is NP-complete

Source:
H. Röck, "Some new results in flow shop scheduling", Zeitschrift für Operations Research 28
(1984), 1-16, doi:10.1007/BF01919082 (`F2|no-wait|Lmax` is NP-hard in the strong sense);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
table "Flow-shop problems with no-wait" (`F2|no-wait|Lmax`, minimal NP-hard, credited to Röck
1984);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS16] NO-WAIT FLOW-SHOP SCHEDULING,
p. 242 (the deadline version, solvable in polynomial time for `m = 2`, Gilmore and Gomory 1964).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoProcessorNoWaitFlowShopMaximumLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitFlowShopMaximumLateness

/-!
# TWO-PROCESSOR NO-WAIT FLOW-SHOP MAXIMUM LATENESS is NP-complete

INSTANCE: a set of jobs `J₁, …, Jₙ` in a two-machine flow shop, job `Jⱼ` consisting of an
operation on machine `M₁` with processing time `pⱼ₁` followed by an operation on machine `M₂`
with processing time `pⱼ₂`, a due date `dⱼ` for each job, and an integer `y`; all processing
times and due dates are nonnegative integers. QUESTION: is there a schedule (each machine
handles at most one job at a time, and the operation of `Jⱼ` on `M₂` starts only after its
operation on `M₁` is completed, with no wait: it starts exactly when that operation is
completed) whose maximum lateness `L_max = maxⱼ (Cⱼ - dⱼ)` is at most `y`,
`Cⱼ` being the completion time of `Jⱼ` on `M₂`?

This is `F2|no-wait|Lmax` (`n|2|F,no wait|Lmax` in the notation of Lenstra, Rinnooy Kan, and Brucker
1977, who also define the data and the recognition version "is there a schedule with value `≤ y`").
With the deadline objective in place of `L_max` the two-machine no-wait problem is solvable in
polynomial time (Gilmore and Gomory 1964; Garey and Johnson, [SS16]). A schedule is given by the
starting times `s₁ⱼ`, `s₂ⱼ ∈ ℤ₀⁺` of the two operations of job `j`. That each machine handles at
most one job at a time is read, as in `FlowShopSchedulingWanted`, as non-overlap of the operations
of two distinct jobs on the same machine (`s + p ≤ s'` or `s' + p' ≤ s`). The bound `y` is an
integer, encoded as a pair `(y⁺, y⁻)` of naturals representing `y⁺ - y⁻`, as in `ZeroOneILPWanted`;
`Cⱼ - dⱼ ≤ y⁺ - y⁻` is stated over `ℕ` as `Cⱼ + y⁻ ≤ dⱼ + y⁺`. The flow-shop schedule predicates of
`FlowShopSchedulingWanted` and `NoWaitFlowShopSchedulingWanted` carry the overall deadline in their
instance and schedule conditions, so they do not apply to a lateness objective. Jobs are `Fin n`.
Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO-PROCESSOR NO-WAIT FLOW-SHOP MAXIMUM LATENESS is NP-complete.** Source: Röck (1984);
Brucker and Knust's classification (`F2|no-wait|Lmax`). -/
public theorem_wanted twoProcessorNoWaitFlowShopMaximumLateness_npComplete :
    twoProcessorNoWaitFlowShopMaximumLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorNoWaitFlowShopMaximumLatenessDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitFlowShopMaximumLateness
