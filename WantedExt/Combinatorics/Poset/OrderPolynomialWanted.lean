/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Poset.OrderPolynomial
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# The reciprocity theorem for order polynomials

Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed. (author's draft of 15 July 2011,
https://math.mit.edu/~rstan/ec/ec1.pdf), Sections 3.12 and 3.15.3, for a finite poset `P` with
`p` elements and its natural labellings. The expansion of `Ω_P` and its degree and leading
coefficient are proved in `MathlibExt.Combinatorics.Poset.OrderPolynomial`.
-/

@[expose] public section

open Polynomial MathlibExt.Combinatorics.Poset.OrderPolynomial

namespace MathlibExt.Combinatorics.Poset.OrderPolynomialWanted

variable (P : Type*) [PartialOrder P] [Fintype P]

/-- **Reciprocity theorem for order polynomials.** The polynomial `Ω_P` that counts
order-preserving maps `P → [m]` satisfies `Ω̄_P(m) = (-1)^p Ω_P(-m)`, where `Ω̄_P(m)` counts the
strictly order-preserving maps `P → [m]` (Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed.,
author's draft of 15 July 2011, Corollary 3.15.12, for a natural labelling `ω`, whose
complementary labelling `ω̄` is dual natural). -/
theorem_wanted orderPolynomial_reciprocity :
    ∃ Q : ℚ[X], (∀ m : ℕ, Q.eval (m : ℚ) = orderPolynomialValue P m) ∧
      ∀ m : ℕ, (-1 : ℚ) ^ Fintype.card P * Q.eval (-(m : ℚ)) = strictOrderPolynomialValue P m

end MathlibExt.Combinatorics.Poset.OrderPolynomialWanted
