/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ENVY-FREE PRICING for unit-demand consumers with unlimited supply is NP-complete

Source:
V. Guruswami, J. D. Hartline, A. R. Karlin, D. Kempe, C. Kenyon and F. McSherry, "On
profit-maximizing envy-free pricing", Proceedings of the Sixteenth Annual ACM-SIAM Symposium on
Discrete Algorithms (SODA 2005), 1164-1173, doi:10.5555/1070432.1070598 (Section 2,
Definitions 2.1 and 2.2; Section 1: the problems are "not only NP-complete, but APX-hard";
Theorem 3.1: the unit-demand problem is APX-hard even with unlimited supply, by a reduction from
VERTEX COVER).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EnvyFreePricingUnitDemandDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EnvyFreePricingUnitDemand

/-!
# ENVY-FREE PRICING for unit-demand consumers with unlimited supply is NP-complete

INSTANCE: `m` items, each available in unlimited supply, consumers `1, …, n` with a valuation
`vᵢ(j) ∈ ℤ₀⁺` of consumer `i` for item `j` (unit demand: each consumer buys at most one item),
and a revenue bound `R`.
QUESTION: is there a pricing `p = (p₁, …, pₘ)` and an envy-free allocation with seller profit at
least `R`?

Definitions of Guruswami et al. (Section 2). Given prices, the utility of item `j` to consumer
`i` is `vᵢ(j) - pⱼ`, and not buying has utility `0`; the demand set `Dᵢ` of consumer `i` consists
of the options of maximum utility. An allocation is envy-free if every consumer receives an
option from its demand set; with unlimited supply every such choice is feasible. The profit is
the sum of the prices of the allocated items. The problem asks for a pricing together with an
envy-free allocation (so ties within a demand set may be resolved in the seller's favour), and
Theorem 3.1 shows that maximizing the profit is APX-hard already with unlimited supply. A
unit-demand consumer values a bundle at the value of its best item. With nonnegative additive
prices, a bundle `S` in a demand set can be replaced by a highest-valued item `j` of `S`: the
utility of `{j}` is at least that of `S`, so `{j}` is also in the demand set, and equality forces
the other items of `S` to cost `0`, so the profit is unchanged. Hence allocations of at most one
item suffice.

Prices are nonnegative integers. With integer valuations this loses no generality: for a fixed
allocation, envy-freeness consists of the constraints `pⱼ ≤ vᵢ(j)` and
`pⱼ - pⱼ' ≤ vᵢ(j) - vᵢ(j')` for a consumer `i` allocated item `j`, and `vᵢ(j') ≤ pⱼ'` for a
consumer `i` allocated nothing, a system of difference constraints with integer right-hand sides
(a totally unimodular matrix), on which the profit is bounded; so its maximum over real
nonnegative prices is attained at integer prices. Membership in NP: capping each price at the
largest valuation of its item keeps the allocation envy-free and the profit unchanged (an item
priced above every valuation is allocated to nobody, and after capping its utility is still at
most `0` for every consumer), so a pricing and an allocation are a certificate of polynomial size
(when there are no consumers, the question only asks whether `R = 0`).

The instance lists `m`, the valuations (one list of `m` values per consumer, read as
`j ↦ vᵢ(j)`), and `R`. An allocation assigns to each consumer `none` (no purchase) or `some j`.
All numbers use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ENVY-FREE PRICING for unit-demand consumers with unlimited supply is NP-complete.**
Source: Guruswami et al. (2005), Section 1 and Theorem 3.1 (hardness with unlimited supply). -/
public theorem_wanted envyFreePricing_npComplete :
    envyFreePricingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L envyFreePricingDec

end MetaMathlibExt.Complexity.NPComplete.EnvyFreePricingUnitDemand
