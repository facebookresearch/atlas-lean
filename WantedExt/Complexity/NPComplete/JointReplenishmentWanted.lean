/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# JOINT REPLENISHMENT (FINITE HORIZON) is NP-complete

Source:
E. Arkin, D. Joneja, and R. Roundy, "Computational complexity of uncapacitated multi-echelon
production planning problems", Operations Research Letters 8 (1989), 61-66,
doi:10.1016/0167-6377(89)90001-1;
M. Bienkowski, J. Byrka, M. Chrobak, N. Dobbs, T. Nowicki, M. Sviridenko, G. Świrszcz, and
N. E. Young, "Approximation algorithms for the joint replenishment problem with deadlines",
Journal of Scheduling 18 (2015), 545-560, doi:10.1007/s10951-014-0392-y (records that the
problem is NP-complete even with linear waiting costs, crediting Arkin, Joneja, and Roundy).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.JointReplenishmentDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.JointReplenishment

/-!
# JOINT REPLENISHMENT (FINITE HORIZON) is NP-complete

INSTANCE: `T` periods `0, …, T - 1`; `N` items, item `i` with a demand `d_{i,t} ∈ ℤ₀⁺` in each
period `t`, a holding cost `h_i ∈ ℤ₀⁺` per unit and period, and a minor ordering cost
`k_i ∈ ℤ₀⁺`; a major ordering cost `K₀ ∈ ℤ₀⁺`; a bound `B`. QUESTION: is there an ordering
plan, order quantities `x_{i,t} ∈ ℤ₀⁺`, without backlogging (for every item and period, the
units ordered up to and including that period cover the demand up to and including it) whose
total cost is at most `B`? The cost of a plan is `K₀` for every period with an order of some
item, plus `k_i` for every period with an order of item `i`, plus `h_i` per unit of item `i`
held in stock at the end of each period.

This is the classical (uncapacitated, finite-horizon, dynamic-demand) joint replenishment
problem in its inventory form, shown strongly NP-hard by Arkin, Joneja, and Roundy (1989).
Bienkowski et al. (2015) record that the problem is NP-complete even when waiting costs are
linear: read backwards in time, a unit of item `i` ordered in period `s` for the demand of
period `t ≥ s` costs `h_i (t - s)` in holding, so the case `h_i = 1` for every item is that
linear-cost version. Stock starts at zero, and demand must be met from stock or the order of
the same period. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **JOINT REPLENISHMENT (FINITE HORIZON) is NP-complete.** Source: Arkin, Joneja, and Roundy
(1989); Bienkowski et al. (2015). -/
public theorem_wanted jointReplenishment_npComplete :
    jointReplenishmentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L jointReplenishmentDec

end MetaMathlibExt.Complexity.NPComplete.JointReplenishment
