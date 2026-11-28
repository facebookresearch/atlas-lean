/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE MAXIMUM CUMULATIVE COST is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS7] SEQUENCING TO MINIMIZE
MAXIMUM CUMULATIVE COST (reference: [Abdel-Wahab, 1976], transformation from REGISTER SUFFICIENCY);
H. M. Abdel-Wahab, *Scheduling with Applications to Register Allocation and Deadlock Problems*,
Ph.D. thesis, University of Waterloo (1976) (not available to this formalization);
H. M. Abdel-Wahab and T. Kameda, "Scheduling to minimize maximum cumulative cost subject to
series-parallel precedence constraints", Operations Research 26 (1978), 141-158,
doi:10.1287/opre.26.1.141.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeMaximumCumulativeCostDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeMaximumCumulativeCost

/-!
# SEQUENCING TO MINIMIZE MAXIMUM CUMULATIVE COST is NP-complete

INSTANCE: a set `T` of tasks, a partial order `<` on `T`, a "cost" `c(t) ∈ ℤ` for each `t ∈ T`
(if `c(t) < 0`, it can be viewed as a "profit"), and a constant `K ∈ ℤ`.
QUESTION: is there a one-processor schedule `σ` for `T` that obeys the precedence constraints
and which has the property that, for every task `t ∈ T`, the sum of the costs for all tasks `t'`
with `σ(t') ≤ σ(t)` is at most `K`?

Garey and Johnson credit the NP-completeness to Abdel-Wahab's 1976 thesis (a transformation from
REGISTER SUFFICIENCY) and note that it remains NP-complete when every cost is in `{-1, 0, 1}`;
Abdel-Wahab and Kameda (abstract) restate it: "It is known that this problem is in general
NP-complete." Membership in NP: the order of the tasks is a certificate.

The tasks carry no lengths, so a one-processor schedule (Garey and Johnson's [SS1] notion, a
one-to-one `σ : T → ℤ₀⁺`) is here only an order of the tasks: a one-to-one `σ : T → ℕ`, obeying
the precedence constraints when `t < t'` implies `σ(t) < σ(t')`; the question depends only on the
order. The tasks are `Fin n`, one per listed cost. Integers (the costs and `K`) are given as pairs
`(p, q)` of natural numbers standing for `p - q`, as in `ZeroOneILPWanted`. The partial order is
given by the list of its pairs `(t, t')` with `t < t'`, required to be a strict order (Mathlib's
`IsStrictOrder`). Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SEQUENCING TO MINIMIZE MAXIMUM CUMULATIVE COST is NP-complete.** Source: Garey and
Johnson (1979), [SS7] (Abdel-Wahab 1976); Abdel-Wahab and Kameda (1978). -/
public theorem_wanted sequencingToMinimizeMaximumCumulativeCost_npComplete :
    sequencingToMinimizeMaximumCumulativeCostDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L sequencingToMinimizeMaximumCumulativeCostDec

end MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeMaximumCumulativeCost
