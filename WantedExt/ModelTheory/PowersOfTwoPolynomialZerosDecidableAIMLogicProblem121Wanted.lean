/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Zeros of integer polynomials at powers of two are decidable (AIM Hilbert's tenth, Question 8)

AIM workshop Extensions of Hilbert's tenth problem, problem list, Question 8 (Pheidas): is the
following problem decidable: given `P(x⃗) ∈ ℤ[x⃗]`, do there exist `n₁, …, n_m ∈ ℕ` with `P(2^{n₁},
…, 2^{n_m}) = 0`? The list answers: yes, this is related to the Mordell-Lang conjecture for tori.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Computability.RE

@[expose] public section

namespace MathlibExt.ModelTheory.PowersOfTwoPolynomialZerosDecidableAIMLogicProblem121Wanted

/-!
Source: AIM workshop Extensions of Hilbert's tenth problem, problem list moderated by B. Poonen and
T. Scanlon, notes by J. Demeyer, Question 8 (T. Pheidas),
https://aimath.org/WWN/hilberts10th/hilberts10th.pdf. UnsolvedMath record UM-20002345
(`AIM-LOGIC-0121`), dataset ulamai/UnsolvedMath v1.8.0.

Inputs are polynomials with integer coefficients in finitely many variables, encoded as lists of
monomials (an integer coefficient and the exponents of `x₀, x₁, …`), the encoding of
`OpenConjectures.Computability.AnalyticSolutionsDecidability`. The unknowns `n₀, n₁, …` are natural
numbers; variables not occurring in `P` are irrelevant. Decidable is Mathlib's `ComputablePred` on
the encodings.
-/

/-- A polynomial `P ∈ ℤ[x₀, x₁, …]` encoded as a list of monomials, each given by its integer
coefficient and the list of exponents of `x₀, x₁, …` (missing exponents are `0`). -/
abbrev IntPolynomial := List (ℤ × List ℕ)

/-- The value `P(2^{n₀}, 2^{n₁}, …)` of the encoded polynomial `P`. -/
def evalAtPowersOfTwo (P : IntPolynomial) (n : ℕ → ℕ) : ℤ :=
  (P.map fun m => m.1 * ((m.2.zipIdx).map fun ej => ((2 : ℤ) ^ n ej.2) ^ ej.1).prod).sum

/-- `P(2^{n₀}, 2^{n₁}, …) = 0` for some natural numbers `n₀, n₁, …`. -/
def HasZeroAtPowersOfTwo (P : IntPolynomial) : Prop :=
  ∃ n : ℕ → ℕ, evalAtPowersOfTwo P n = 0

/-- AIM Extensions of Hilbert's tenth problem, Question 8 (Pheidas), as a claim: it is decidable,
given `P ∈ ℤ[x₁, …, x_m]`, whether `P(2^{n₁}, …, 2^{n_m}) = 0` for some `n₁, …, n_m ∈ ℕ`. -/
def powersOfTwoZerosDecidable : Prop :=
  ComputablePred HasZeroAtPowersOfTwo

/--
Resolved true: the workshop's problem list answers Pheidas's question: it is decidable whether an
integer polynomial vanishes at some point `(2^{n₁}, …, 2^{n_m})`, a fact related to the Mordell-Lang
conjecture for tori. Source: AIM workshop Extensions of Hilbert's tenth problem, problem list
moderated by B. Poonen and T. Scanlon, notes by J. Demeyer, Question 8 (T. Pheidas),
https://aimath.org/WWN/hilberts10th/hilberts10th.pdf; resolution: AIM workshop Extensions of
Hilbert's tenth problem, problem list (B. Poonen, T. Scanlon, J. Demeyer), answer recorded under
Question 8, Question 8: 'The answer is YES: this is related to the Mordell-Lang conjecture for
tori.', https://aimath.org/WWN/hilberts10th/hilberts10th.pdf.
-/
public theorem_wanted powersOfTwoZerosDecidable_holds : powersOfTwoZerosDecidable

end MathlibExt.ModelTheory.PowersOfTwoPolynomialZerosDecidableAIMLogicProblem121Wanted
