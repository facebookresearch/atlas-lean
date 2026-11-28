/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MOST PROBABLE EXPLANATION in Bayesian networks is NP-complete

Source:
S. E. Shimony, "Finding MAPs for belief networks is NP-hard", Artificial Intelligence 68
(1994), 399-410, doi:10.1016/0004-3702(94)90072-8;
J. D. Park and A. Darwiche, "Complexity results and approximation strategies for MAP
explanations", Journal of Artificial Intelligence Research 21 (2004), 101-133,
doi:10.1613/jair.1236, arXiv:1107.0024 (§2.2: the decision problem D-MPE, and "D-MPE is
NP-complete (Shimony, 1994)").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MostProbableExplanationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MostProbableExplanation

open Cslib.MachineLearning.GraphicalModels

/-!
# MOST PROBABLE EXPLANATION in Bayesian networks is NP-complete

INSTANCE: a Bayesian network `(G, Θ)` with rational parameters: a directed acyclic graph `G`
over discrete variables `X`, and for each variable `X` with parents `U` a conditional
probability table assigning a number `θ_{x|u} ∈ [0, 1]` to each value `x` of `X` and each
instantiation `u` of `U`, with `∑ₓ θ_{x|u} = 1`; evidence `e` (an instantiation of a set `E` of
variables); and a rational number `p`.
QUESTION (D-MPE): is there an instantiation `x` of all the network variables such that
`Pr(x, e) > p`? Here `Pr(x) = ∏ θ_{x|u}` over the families of the network, and `Pr(x, e)` is
`Pr(x)` when `x` agrees with `e` and `0` otherwise.

The network is CSLib's `BayesNet (Fin d) n`: the variables `0, …, n - 1` are listed in a
topological order of `G` (every parent of node `k` is a node `j < k`; every DAG has such an
order), and all take values in `{0, …, d - 1}` (a variable with fewer values is padded with
values of probability `0`, which changes no answer). Its joint distribution
`BayesNet.joint` is `Pr`, the product of the table entries (`BayesNet.joint_eq_prod`).

The instance lists, for each node `k`, its parents and its table, row by row: a row `(u, θ)`
gives the parents' values `u` (in the order of the parent list) and the distribution
`θ = (θ_{0|u}, …, θ_{d-1|u})` as fractions `(num, den)`; the table has one row per
instantiation of the parents (`IsNode`). `Encodes i b` says that the network `b` has these
parents and tables. The threshold is `p = (p⁺ - p⁻) / q`, given as `((p⁺, p⁻), q)` with
`q > 0`; the evidence is a list of pairs `(variable, value)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding` (numbers in binary). Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MOST PROBABLE EXPLANATION (D-MPE) in Bayesian networks is NP-complete.** Source:
Shimony (1994); Park and Darwiche (2004). -/
public theorem_wanted mostProbableExplanation_npComplete :
    mostProbableExplanationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L mostProbableExplanationDec

end MetaMathlibExt.Complexity.NPComplete.MostProbableExplanation
