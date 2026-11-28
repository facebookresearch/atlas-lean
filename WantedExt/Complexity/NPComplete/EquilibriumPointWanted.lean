/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EQUILIBRIUM POINT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN15] EQUILIBRIUM
POINT;
S. Sahni, "Computationally related problems", SIAM Journal on Computing 3 (1974),
262-279, doi:10.1137/0203021, Section 2.4, Theorem 2.4.1 (existence of an
equilibrium point of an n-person game with polynomial payoffs is NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EquilibriumPointDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EquilibriumPoint

/-!
# EQUILIBRIUM POINT is NP-complete

INSTANCE: a set `X = {x₁, ..., xₙ}` of variables, a collection `{Fᵢ : 1 ≤ i ≤ n}` of product
polynomials over `X` and the integers, and a finite range-set `Mᵢ ⊆ ℤ` for `1 ≤ i ≤ n`.
QUESTION: is there a sequence `y₁, ..., yₙ` of integers, with `yᵢ ∈ Mᵢ`, such that for
`1 ≤ i ≤ n` and all `y ∈ Mᵢ`,
`Fᵢ(y₁, ..., yᵢ₋₁, yᵢ, yᵢ₊₁, ..., yₙ) ≥ Fᵢ(y₁, ..., yᵢ₋₁, y, yᵢ₊₁, ..., yₙ)`?

This is the existence of a pure Nash equilibrium of the `n`-player game `game` in which player
`i` chooses `xᵢ ∈ Mᵢ` and receives payoff `Fᵢ`. The question is stated with the repository's
`MathlibExt.GameTheory.StrategicGame.IsNash`, which by `isNash_iff_update_le` says exactly that
no unilateral deviation `Function.update σ i t` raises the deviator's payoff. Payoffs are the
integer values of the `Fᵢ`, cast to `ℝ` as `StrategicGame` requires (the cast preserves `≤`).

Players and variables are indexed `0, ..., n - 1`. A product polynomial is a polynomial given
as a product of polynomials (Garey and Johnson use the term the same way in [AN11] NUMBER OF
ROOTS FOR A PRODUCT POLYNOMIAL), here `productPoly`, a product of factors `factorPoly`, each a
sum of integer multiples of monomials. A monomial is given by the list of its variables, each
listed as often as its exponent, so exponents are written in unary and a payoff is evaluated in
polynomial time; Sahni's reduction uses range-sets `{0, 1}`, on which exponents are immaterial.
Polynomials and their evaluation are Mathlib's `MvPolynomial ℕ ℤ` and `MvPolynomial.eval`; a
strategy profile `σ` assigns to player `i : Fin n` an element of `Mᵢ` and is evaluated at
`xᵢ = σ i` (`assignment`; no variable has an index `≥ n`). Integers are given as pairs of
naturals `(positive part, negative part)` and each range-set as a finite list of integers. A
profile exists only when every `Mᵢ` is nonempty; an empty `Mᵢ` leaves no sequence `y` with
`yᵢ ∈ Mᵢ`, so such instances are no-instances, as in the source.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open MvPolynomial

/-- **EQUILIBRIUM POINT is NP-complete.** Source: Garey and Johnson (1979), [AN15];
Sahni (1974), Theorem 2.4.1. -/
public theorem_wanted equilibriumPoint_npComplete :
    equilibriumPointDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L equilibriumPointDec

end MetaMathlibExt.Complexity.NPComplete.EquilibriumPoint
