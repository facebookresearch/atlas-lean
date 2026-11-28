/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE OPEN SHOP WITH EQUAL DELAYS is NP-complete

Source:
W. Yu, *The two-machine flow shop problem with delays and the one-machine total tardiness
problem*, PhD thesis, Technische Universiteit Eindhoven (1996), Chapter 2, Appendix "The Open
Shop Problem with Equal Delays", Theorem 5 (pp. 17-18);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück
(online tables), class "Open-shop problems with transportation delays" (records the problem
`O2|t_ikl = T|Cmax` as minimal NP-hard, citing Yu (1996)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoMachineOpenShopEqualDelaysDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineOpenShopEqualDelays

open TwoMachineFlowShopTwoDelayValues (TwoMachineFlowShopTwoDelayValuesInstance)
open TwoMachineOpenShopTwoDelayValues (TwoMachineOpenShopTwoDelayValuesFeasible)

/-!
# TWO-MACHINE OPEN SHOP WITH EQUAL DELAYS is NP-complete

INSTANCE: two machines `M₁`, `M₂` in an open shop, each processing at most one operation at a
time; `n` jobs, job `j` consisting of an operation of processing time `p₁ⱼ ∈ ℤ₀⁺` on `M₁` and an
operation of processing time `p₂ⱼ ∈ ℤ₀⁺` on `M₂`, which may be processed in either order; a
delay `T ∈ ℤ₀⁺`, common to all jobs and both directions: between the completion of the operation
of a job processed first and the start of its operation processed second, at least `T` time
units must elapse; and a bound `K ∈ ℤ₀⁺`. QUESTION: is there a feasible schedule whose makespan
(the largest completion time of an operation) is at most `K`?

This is the decision version of `O2|t_ikl = T|Cmax` in the Brucker-Knust tables (transportation
time `T` for every job between every pair of machines). Delays occupy no machine, and any number
of jobs may be between the machines at once. Yu proves the problem NP-hard (in the ordinary
sense, by a reduction from PARTITION) already when `p₁ⱼ = p₂ⱼ` for every job. Numbers use the
binary encoding.

The problem is the two-machine open shop with two delay values
(`TwoMachineOpenShopTwoDelayValuesWanted`, `O2|tᵢ ∈ {T₁, T₂}|Cmax`) restricted to `T₁ = T₂`: the
instance is that module's (the delay values `T₁`, `T₂`, the jobs `(p₁ⱼ, p₂ⱼ, lⱼ)` listed one per
entry, and `K`), well-formedness adds `T₁ = T₂` to its condition that every delay is `T₁` or
`T₂`, so every job's delay is `T = T₁`, and the schedule is that module's
(`TwoMachineOpenShopTwoDelayValuesFeasible`). Membership in NP is the certificate argument given
there.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO-MACHINE OPEN SHOP WITH EQUAL DELAYS is NP-complete.** Source: Yu (1996), Chapter 2,
Appendix, Theorem 5; Brucker and Knust (classification tables). -/
public theorem_wanted twoMachineOpenShopEqualDelays_npComplete :
    twoMachineOpenShopEqualDelaysDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoMachineOpenShopEqualDelaysDec

end MetaMathlibExt.Complexity.NPComplete.TwoMachineOpenShopEqualDelays
