/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SANTA CLAUS (MAX-MIN FAIR ALLOCATION) is NP-complete

Source:
I. Bezáková and V. Dani, "Allocating indivisible goods", ACM SIGecom Exchanges 5(3) (2005),
11-18, doi:10.1145/1120680.1120683 (the Max-Min Fairness problem);
B. L. Deuermeyer, D. K. Friesen and M. A. Langston, "Scheduling to maximize the minimum
processor finish time in a multiprocessor system", SIAM Journal on Algebraic and Discrete
Methods 3 (1982), 190-196, doi:10.1137/0603019 (NP-hardness when all agents value the goods
alike).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SantaClausDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SantaClaus

/-!
# SANTA CLAUS (MAX-MIN FAIR ALLOCATION) is NP-complete

INSTANCE: a set of `k ≥ 1` agents, a set of `m` indivisible goods, an additive valuation
`vᵢ(j) ∈ ℤ₀⁺` of each good `j` for each agent `i`, and a bound `T ∈ ℤ₀⁺`. QUESTION: is there an
allocation of the goods to the agents (each good to exactly one agent) under which every agent
`i` receives goods of total value `∑_{j allocated to i} vᵢ(j) ≥ T`?

This is the decision version of Bezáková and Dani's Max-Min Fairness problem with additive
valuations that are part of the input ("split the goods between the players so as to maximize
the minimum valuation"), also called the Santa Claus problem. When all agents value the goods
alike (`vᵢ(j) = s(j)`) it is the problem of assigning independent tasks to `k` identical
processors so as to maximize the earliest processor finishing time, which Deuermeyer, Friesen
and Langston show NP-hard. With `k` agents, `T = B` and the `3k` sizes `s(j)` of a 3-PARTITION
instance (`B/4 < s(j) < B/2`, summing to `kB`), every agent must receive exactly `B`, hence
exactly three goods, so the question is 3-PARTITION and the problem is NP-complete in the strong
sense. An allocation is a map from goods to agents; allocating every good loses nothing, since
valuations are nonnegative. Numbers use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SANTA CLAUS (MAX-MIN FAIR ALLOCATION) is NP-complete.** Source: Bezáková and Dani (2005);
Deuermeyer, Friesen and Langston (1982). -/
public theorem_wanted santaClaus_npComplete :
    santaClausDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L santaClausDec

end MetaMathlibExt.Complexity.NPComplete.SantaClaus
