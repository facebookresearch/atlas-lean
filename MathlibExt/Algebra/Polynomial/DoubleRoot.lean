/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Div

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-!
# Double roots of univariate polynomials

Over an arbitrary commutative ring, a point `a` is (at least) a double root
of `f` exactly when `f` and its formal derivative both vanish at `a`. This
is ATLAS `NumberTheoryI` Corollary 9.13 (Section 9.2,
`v1/Atlas/NumberTheoryI/targets.yaml`), proved here from the first-order
Taylor expansion with quadratic remainder in
`MathlibExt/Algebra/Polynomial/Taylor.lean`
(`existsUnique_taylor_remainder`, Lemma 9.11 of the book).

Mathlib's `one_lt_rootMultiplicity_iff_isRoot` characterizes the same
phenomenon via `rootMultiplicity`, but it requires `f ≠ 0`; the statements
here are in direct divisibility form and cover `f = 0` as well, with no
domain hypothesis.
-/

/-- **Double root criterion.** Let $R$ be a commutative ring, let $f \in R[x]$ and $a \in R$, and
let $f'$ be the formal derivative of $f$. Then $f(a) = 0$ and $f'(a) = 0$ if and only if
$f = (x - a)^2 g$ for some $g \in R[x]$.

Source: ATLAS NumberTheoryI, Corollary 9.13. -/
public theorem eval_and_derivative_eval_eq_zero_iff (f : R[X]) (a : R) :
    f.eval a = 0 ∧ f.derivative.eval a = 0 ↔
      ∃ g : R[X], f = (X - C a) ^ 2 * g := by
  constructor
  · rintro ⟨hf, hf'⟩
    obtain ⟨g, hg, -⟩ := existsUnique_taylor_remainder f a
    refine ⟨g, ?_⟩
    rw [hg, hf, hf']
    simp
    exact mul_comm _ _
  · rintro ⟨g, rfl⟩
    refine ⟨?_, ?_⟩
    · simp
    · rw [derivative_mul, derivative_pow]
      simp

/-- **Double root criterion in divisibility form.** Let $R$ be a commutative ring, let
$f \in R[x]$ and $a \in R$, and let $f'$ be the formal derivative of $f$. Then $(x - a)^2$
divides $f$ in $R[x]$ if and only if $f(a) = 0$ and $f'(a) = 0$.

Source: ATLAS NumberTheoryI, Corollary 9.13. -/
public theorem sq_dvd_iff_eval_and_derivative_eval_eq_zero (f : R[X])
    (a : R) :
    (X - C a) ^ 2 ∣ f ↔ f.eval a = 0 ∧ f.derivative.eval a = 0 := by
  rw [eval_and_derivative_eval_eq_zero_iff, dvd_iff_exists_eq_mul_right]

/-- **A nonvanishing derivative excludes a double root.** Let $R$ be a commutative ring, let
$f \in R[x]$ and $a \in R$, and let $f'$ be the formal derivative of $f$. If $f'(a) \neq 0$,
then $(x - a)^2$ does not divide $f$ in $R[x]$.

No assumption on $f(a)$ is needed.

Source: ATLAS NumberTheoryI, consequence of Corollary 9.13. -/
public theorem not_sq_dvd_of_derivative_eval_ne_zero
    (f : R[X]) (a : R) (hf' : f.derivative.eval a ≠ 0) :
    ¬ (X - C a) ^ 2 ∣ f := by
  rw [sq_dvd_iff_eval_and_derivative_eval_eq_zero]
  rintro ⟨-, h⟩
  exact hf' h

end Polynomial
