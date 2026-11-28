/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SATISFIABILITY OF QUADRATIC EQUATIONS OVER GF[q] is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MAXIMUM SATISFIABILITY OF QUADRATIC EQUATIONS OVER GF[Q] (decision version);
J. Håstad, S. Phillips and S. Safra, "A well-characterized approximation problem",
Information Processing Letters 47 (1993), 301-305, doi:10.1016/0020-0190(93)90076-L,
Theorem 4.2 (for every fixed prime `p`, deciding whether all equations of an instance can be
satisfied simultaneously is NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SatisfiabilityOfQuadraticEquationsOverGFqDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SatisfiabilityOfQuadraticEquationsOverGFq

/-!
# SATISFIABILITY OF QUADRATIC EQUATIONS OVER GF[q] is NP-complete

INSTANCE: a prime number `q`, a set `P = {p₁(x), …, pₘ(x)}` of polynomials of degree at most `2`
over `GF[q]` in `n` variables, none of which contains a monomial `xᵢ²`, and a positive integer
`K`.
QUESTION: is there a subset `P' ⊆ P` whose polynomials have a common root, with `|P'| ≥ K`?

`GF[q]` is `ZMod q`, the variables are `x₀, …, x_{n-1}` (indices `Fin n`), and each polynomial
is read as an element of `MvPolynomial (Fin n) (ZMod q)` and evaluated with
`MvPolynomial.eval`. A polynomial is given as a list of terms `(a, t)`, where the coefficient
`a < q` is an element of `GF[q]` and `t` is a duplicate-free list of at most two variable
indices: `[]` is the term `a`, `[j]` is `a·x_j`, and `[j, k]` with `j ≠ k` is `a·x_j·x_k`. These
are exactly the polynomials of degree at most `2` without a monomial `xᵢ²`. The polynomials of
`P` must be pairwise distinct, since `P` is a set; `P'` is a set of indices into the list, so its
cardinality is `|P'|`.

Håstad, Phillips and Safra fix the prime and also assume that no polynomial is constant ("just
a matter of definition"); the compendium entry, followed here, takes `q` as part of the input
and does not exclude constants.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SATISFIABILITY OF QUADRATIC EQUATIONS OVER GF[q] is NP-complete.** Source: Crescenzi and
Kann, MAXIMUM SATISFIABILITY OF QUADRATIC EQUATIONS OVER GF[Q]; Håstad, Phillips and Safra (1993),
Theorem 4.2. -/
public theorem_wanted quadraticEquations_npComplete :
    quadraticEquationsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L quadraticEquationsDec

end MetaMathlibExt.Complexity.NPComplete.SatisfiabilityOfQuadraticEquationsOverGFq
