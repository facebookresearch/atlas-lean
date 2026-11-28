/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TEMPORAL CONSTRAINT SATISFACTION is NP-complete

Source:
R. Dechter, I. Meiri, and J. Pearl, "Temporal constraint networks", Artificial
Intelligence 49 (1991), 61-95, doi:10.1016/0004-3702(91)90006-6, Section 2
(TCSP) and Theorem 4.1 (deciding consistency of a TCSP is NP-hard; credited there
to E. Davis, private communication, 1989).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TemporalConstraintSatisfactionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TemporalConstraintSatisfaction

/-!
# TEMPORAL CONSTRAINT SATISFACTION is NP-complete

INSTANCE: time-point variables `X₁, ..., Xₙ` with continuous domains, and constraints, each a
finite set of closed intervals `{[a₁, b₁], ..., [aₖ, bₖ]}` with rational endpoints: a unary
constraint on `Xᵢ` represents `(a₁ ≤ Xᵢ ≤ b₁) ∨ ... ∨ (aₖ ≤ Xᵢ ≤ bₖ)`, and a binary constraint on
`(Xᵢ, Xⱼ)` represents `(a₁ ≤ Xⱼ - Xᵢ ≤ b₁) ∨ ... ∨ (aₖ ≤ Xⱼ - Xᵢ ≤ bₖ)`. QUESTION: is the network
consistent, i.e. is there an assignment of real values to the variables satisfying all
constraints?

Variables are `0, ..., n - 1`. A rational endpoint is a triple `(p, m, d)` standing for
`(p - m) / d` with `d > 0` (`Endpoint.val`). Dechter, Meiri and Pearl assume constraints are
given with pairwise disjoint intervals; overlapping intervals denote the same disjunction, so
that canonical form is not required here. The problem is in NP because choosing one interval per
constraint leaves a simple temporal problem, decidable in polynomial time (their Section 3), and
NP-hard by their Theorem 4.1, a reduction from graph 3-coloring with integer point intervals.
Numbers use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TEMPORAL CONSTRAINT SATISFACTION is NP-complete.** Source: Dechter, Meiri, and Pearl (1991),
Theorem 4.1. -/
public theorem_wanted temporalConstraintSatisfaction_npComplete :
    temporalConstraintSatisfactionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L temporalConstraintSatisfactionDec

end MetaMathlibExt.Complexity.NPComplete.TemporalConstraintSatisfaction
