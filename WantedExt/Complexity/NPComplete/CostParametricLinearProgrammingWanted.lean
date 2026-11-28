/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COST-PARAMETRIC LINEAR PROGRAMMING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [MP3] COST-PARAMETRIC LINEAR PROGRAMMING,
p. 245, crediting R. G. Jeroslow, "Bracketing discrete problems by two problems of linear
optimization", Proceedings of the First Symposium on Operations Research (Heidelberg), Verlag
Anton Hain, Meisenheim (1976), 205-216 (transformation from 3SAT).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CostParametricLinearProgrammingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CostParametricLinearProgramming

open MetaMathlibExt.Complexity.NPComplete.IntegerProgramming (toInt)

/-!
# COST-PARAMETRIC LINEAR PROGRAMMING is NP-complete

INSTANCE: a finite set `X` of pairs `(x, b)`, where `x` is an `m`-tuple of integers and `b` is an
integer, a set `J ⊆ {1, 2, …, m}`, and a positive rational number `q`.
QUESTION: is there an `m`-tuple `c` with rational entries such that `(c · c)^{1/2} ≤ q` and such
that, if `Y` is the set of all `m`-tuples `y` with non-negative rational entries satisfying
`x · y ≥ b` for all `(x, b) ∈ X`, then the minimum of `∑_{j ∈ J} cⱼ yⱼ` over all `y ∈ Y` exceeds
`½ max {|cⱼ| : j ∈ J} + ∑_{j ∈ J} min {0, cⱼ}`?

Conventions. Coordinates are `0`-based, so `J ⊆ {0, …, m - 1}`. `(c · c)^{1/2} ≤ q` is stated as
`c · c ≤ q²`, which is equivalent because both sides of the original are nonnegative. "The
minimum ... exceeds `T`" is stated as: the set of values `{∑_{j ∈ J} cⱼ yⱼ : y ∈ Y}` has a least
element (Mathlib's `IsLeast`) and it is greater than `T`; when `Y` is empty or the objective is
unbounded below there is no minimum. `max {|cⱼ| : j ∈ J}` needs `J ≠ ∅`, which `WellFormed`
requires; it is computed as `Finset.fold max 0`, which equals the maximum because every `|cⱼ|` is
nonnegative.

Encoding: `X` is a list of constraints in the encoding of INTEGER PROGRAMMING
(`IntegerProgramming.toInt` reads an integer from a `(positive part, negative part)` pair), `J`
is a list of coordinates, and `q` is a pair `(numerator, denominator)` of positive naturals. The
instance is decoded from a bitstring with the repository's canonical
`MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and bitstrings decoding to malformed
instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **COST-PARAMETRIC LINEAR PROGRAMMING is NP-complete.** Source: Garey and Johnson (1979),
[MP3]; Jeroslow (1976). -/
public theorem_wanted costParametricLinearProgramming_npComplete :
    costParametricLinearProgrammingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L costParametricLinearProgrammingDec

end MetaMathlibExt.Complexity.NPComplete.CostParametricLinearProgramming
