/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ALGEBRAIC EQUATIONS OVER GF[2] is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN9] ALGEBRAIC EQUATIONS OVER GF[2];
A. S. Fraenkel and Y. Yesha, "Complexity of problems in games, graphs and algebraic equations",
Discrete Applied Mathematics 1 (1979), 15-30, doi:10.1016/0166-218X(79)90012-X.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.AlgebraicEquationsOverGF2Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AlgebraicEquationsOverGF2

/-!
# ALGEBRAIC EQUATIONS OVER GF[2] is NP-complete

Given polynomials `P₁, …, Pₘ` over `GF[2]` in the variables `x₁, …, xₙ`, each a sum of terms
and each term either `1` or a product of distinct variables, is there
`(u₁, …, uₙ) ∈ {0, 1}ⁿ` with `Pᵢ(u₁, …, uₙ) = 0` for `1 ≤ i ≤ m`?

The variables are `x₀, …, x_{n-1}` (indices `Fin n`), `GF[2]` is `ZMod 2`, and each `Pᵢ` is
read as an element of `MvPolynomial (Fin n) (ZMod 2)` and evaluated with `MvPolynomial.eval`.
A term is the list of indices of its variables: `[]` is the term `1`, and `[j₁, …, jᵣ]` with
distinct `jₖ < n` is `x_{j₁} ⋯ x_{jᵣ}`. A polynomial is the list of its terms; a repeated term
is allowed and contributes `t + t = 0`, as in `GF[2]`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ALGEBRAIC EQUATIONS OVER GF[2] is NP-complete.** Source: Garey and Johnson (1979), [AN9];
Fraenkel and Yesha (1979). -/
public theorem_wanted algebraicEquationsOverGF2_npComplete :
    algebraicEquationsOverGF2Dec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L algebraicEquationsOverGF2Dec

end MetaMathlibExt.Complexity.NPComplete.AlgebraicEquationsOverGF2
