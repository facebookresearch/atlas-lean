/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EQUILIBRIUM POINT with range-sets {0, 1} is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN15] EQUILIBRIUM POINT, p. 252
(comment: "Remains NP-complete even if M_i = {0,1} for 1 ≤ i ≤ n.");
S. Sahni, "Computationally related problems", SIAM Journal on Computing 3 (1974),
262-279, doi:10.1137/0203021, Section 2.4, Theorem 2.4.1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EquilibriumPointBinaryDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EquilibriumPointBinary

open MetaMathlibExt.Complexity.NPComplete.EquilibriumPoint (EquilibriumPointInstance rangeSet
  EquilibriumPointFeasible)

/-!
# EQUILIBRIUM POINT with range-sets {0, 1} is NP-complete

EQUILIBRIUM POINT ([AN15], `EquilibriumPointWanted`) restricted to instances in which every
range-set is `Mᵢ = {0, 1}`. INSTANCE: a set `X = {x₁, ..., xₙ}` of variables and a collection
`{Fᵢ : 1 ≤ i ≤ n}` of product polynomials over `X` and the integers, with `Mᵢ = {0, 1}` for
`1 ≤ i ≤ n`. QUESTION: is there a sequence `y₁, ..., yₙ` with `yᵢ ∈ {0, 1}` such that for
`1 ≤ i ≤ n` and all `y ∈ {0, 1}`,
`Fᵢ(y₁, ..., yᵢ₋₁, yᵢ, yᵢ₊₁, ..., yₙ) ≥ Fᵢ(y₁, ..., yᵢ₋₁, y, yᵢ₊₁, ..., yₙ)`?

The instance, the game and the question are those of `EquilibriumPointWanted`; only the
restriction is new, in `WellFormed`: each listed range-set `Mᵢ` has exactly the elements `0`
and `1` (a range-set is a set, so the order and repetitions of its list do not matter).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EQUILIBRIUM POINT with range-sets `{0, 1}` is NP-complete.** Source: Garey and Johnson
(1979), [AN15], comment; Sahni (1974). -/
public theorem_wanted equilibriumPointBinary_npComplete :
    equilibriumPointBinaryDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L equilibriumPointBinaryDec

end MetaMathlibExt.Complexity.NPComplete.EquilibriumPointBinary
