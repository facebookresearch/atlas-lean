/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNSIGNED TRANSLOCATION DISTANCE is NP-complete

Source:
D. Zhu and L. Wang, "On the complexity of unsigned translocation distance", Theoretical
Computer Science 352 (2006), 322-328, doi:10.1016/j.tcs.2005.09.078 (Section 2: the model;
Theorem 3: computing the unsigned translocation distance is NP-hard).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UnsignedTranslocationDistanceDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnsignedTranslocationDistance

/-!
# UNSIGNED TRANSLOCATION DISTANCE is NP-complete

INSTANCE: two unsigned genomes `A` and `B` over the same genes, and a nonnegative integer `K`.
QUESTION: is the translocation distance `d(A, B)` at most `K`, i.e. can `A` be transformed into
`B` by at most `K` translocations?

The model is that of Zhu and Wang (2006), Section 2. A genome is a set of chromosomes, a
chromosome `X = x₁, …, xₚ` is a sequence of genes, and for unsigned genomes each gene is a
positive integer. A translocation acts on two chromosomes `X = x₁, …, x_{b-1}, x_b, …, xₚ` and
`Y = y₁, …, y_{c-1}, y_c, …, y_q` of the genome: the prefix–prefix translocation `(X, Y, b, c)`
replaces them by `x₁, …, x_{b-1}, y_c, …, y_q` and `y₁, …, y_{c-1}, x_b, …, xₚ`, and the
prefix–suffix translocation `(X, Y, b, c)` by `x₁, …, x_{b-1}, y_{c-1}, …, y₁` and
`xₚ, …, x_b, y_c, …, y_q`. A chromosome `X` is identical to `Y` if `X = Y` or `X` is the
reversal of `Y`, and genome `A` is identical to genome `B` if they have the same set of
chromosomes. The translocation distance `d(A, B)` is the minimum number of translocations
required to transform `A` into `B`. Zhu and Wang prove that computing it is NP-hard
(Theorem 3, by a reduction whose question is "at most `3n - 3 - J` translocations"); this is
the decision form, at most `K` translocations.

A genome is a list of chromosomes and a chromosome a list of genes. The source writes both
segments `x₁, …, x_{b-1}` and `x_b, …, xₚ` of a chromosome cut by a translocation, so both are
nonempty (`2 ≤ b ≤ p`), and likewise for `Y`; `Translocation` states this with the four
nonempty segments `X₁ X₂ Y₁ Y₂`. As in the source's model and its reduction, each gene occurs
once in each genome, the two genomes have the same genes, and chromosomes are nonempty
(`WellFormed`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **UNSIGNED TRANSLOCATION DISTANCE is NP-complete.** Source: Zhu and Wang (2006),
Theorem 3. -/
public theorem_wanted unsignedTranslocationDistance_npComplete :
    unsignedTranslocationDistanceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unsignedTranslocationDistanceDec

end MetaMathlibExt.Complexity.NPComplete.UnsignedTranslocationDistance
