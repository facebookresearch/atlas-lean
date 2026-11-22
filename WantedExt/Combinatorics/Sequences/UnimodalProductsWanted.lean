/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Sequences.Unimodal
public import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# Products of unimodal and of log-concave polynomials

Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed. (author's draft of 15 July 2011,
https://math.mit.edu/~rstan/ec/ec1.pdf), Chapter 1, Exercise 50(c) and (d): the coefficient
sequences of products of polynomials with nonnegative coefficients inherit "symmetric and
unimodal", and "log-concave with no internal zeros". A polynomial is called unimodal, log-concave,
and so on when its coefficient sequence is.
-/

@[expose] public section

open Polynomial MathlibExt.Combinatorics.Sequences.Unimodal

namespace MathlibExt.Combinatorics.Sequences.UnimodalProductsWanted

/-- **Products of symmetric unimodal polynomials.** Let `P(x) = ∑_{i=0}^{m} aᵢ xⁱ` and
`Q(x) = ∑_{i=0}^{n} bᵢ xⁱ` have nonnegative coefficients, and let `(a₀, …, aₘ)` and
`(b₀, …, bₙ)` be symmetric (`aᵢ = a_{m-i}`, `bᵢ = b_{n-i}`) and unimodal. Then the coefficient
sequence `(c₀, …, c_{m+n})` of `P(x) Q(x)` is symmetric, unimodal and nonnegative (Stanley,
*Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, Chapter 1,
Exercise 50(c)). -/
theorem_wanted symmetric_unimodal_mul {P Q : ℝ[X]} {m n : ℕ} (hPm : P.natDegree ≤ m)
    (hQn : Q.natDegree ≤ n) (hPnn : ∀ i, 0 ≤ P.coeff i) (hQnn : ∀ i, 0 ≤ Q.coeff i)
    (hPsymm : ∀ i ≤ m, P.coeff i = P.coeff (m - i))
    (hQsymm : ∀ i ≤ n, Q.coeff i = Q.coeff (n - i))
    (hPuni : IsUnimodal P.coeff m) (hQuni : IsUnimodal Q.coeff n) :
    (∀ i, 0 ≤ (P * Q).coeff i) ∧
      (∀ i ≤ m + n, (P * Q).coeff i = (P * Q).coeff (m + n - i)) ∧
      IsUnimodal (P * Q).coeff (m + n)

/-- **Products of log-concave polynomials.** Let `P(x)` and `Q(x)` have nonnegative coefficients
and log-concave coefficient sequences with no internal zeros (indexed up to their degrees). Then
the same holds for `P(x) Q(x)` (Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's
draft of 15 July 2011, Chapter 1, Exercise 50(d)). -/
theorem_wanted logConcave_mul {P Q : ℝ[X]} (hPnn : ∀ i, 0 ≤ P.coeff i)
    (hQnn : ∀ i, 0 ≤ Q.coeff i)
    (hPlc : IsLogConcave P.coeff P.natDegree) (hQlc : IsLogConcave Q.coeff Q.natDegree)
    (hPnz : NoInternalZeros P.coeff P.natDegree) (hQnz : NoInternalZeros Q.coeff Q.natDegree) :
    (∀ i, 0 ≤ (P * Q).coeff i) ∧ IsLogConcave (P * Q).coeff (P * Q).natDegree ∧
      NoInternalZeros (P * Q).coeff (P * Q).natDegree

end MathlibExt.Combinatorics.Sequences.UnimodalProductsWanted
