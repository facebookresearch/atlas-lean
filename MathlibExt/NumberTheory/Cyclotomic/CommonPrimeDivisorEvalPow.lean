/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# A common prime divisor of `y - 1` and `Φ_p(y ^ p ^ (a - 1))`

`MetaMathlibExt.prime_eq_of_dvd_sub_one_of_dvd_cyclotomic_eval_pow` states that if `ρ` and `p`
are primes, `a ≥ 1` is a natural number and `y` is a positive integer with `ρ ∣ y - 1` and
`ρ ∣ Φ_p(y ^ p ^ (a - 1))`, where `Φ_p` is the `p`-th cyclotomic polynomial with integer
coefficients, then `ρ = p`.

## Proof

Since `ρ ∣ y - 1` and `y - 1 ∣ y ^ p ^ (a - 1) - 1`, the prime `ρ` divides
`y ^ p ^ (a - 1) - 1`, hence also `Φ_p(y ^ p ^ (a - 1)) - Φ_p(1)` (`Polynomial.sub_dvd_eval_sub`).
As `Φ_p(1) = p` (`Polynomial.eval_one_cyclotomic_prime`) and `ρ ∣ Φ_p(y ^ p ^ (a - 1))`, the
prime `ρ` divides `p`, so `ρ = p`. The argument works for every integer `y` and every exponent:
the hypotheses `0 < a` and `0 < y` follow the source and are not used, so the unused-variables
linter is disabled for this one declaration.

## References

* Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026), Article A95,
  the source of the statement. In the arXiv preprint arXiv:2412.00010v1 (*Hybrid bounds for prime
  divisors*), the statement is Lemma 4.2, proved there by the same congruence argument.
-/

namespace MetaMathlibExt

open Polynomial

set_option linter.unusedVariables false in
/-- **A common prime divisor of $y - 1$ and $\Phi_p(y^{p^{a-1}})$ is $p$.** Let $\rho$ and $p$ be
primes, let $a \ge 1$ be a natural number, let $y$ be a positive integer, and let $\Phi_p$ be the
$p$-th cyclotomic polynomial with integer coefficients. If $\rho \mid y - 1$ and
$\rho \mid \Phi_p(y^{p^{a-1}})$, then $\rho = p$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Lemma 3 (`integers-2026-A95-lem-3`). -/
public theorem prime_eq_of_dvd_sub_one_of_dvd_cyclotomic_eval_pow {ρ p a : ℕ}
    (hρ : ρ.Prime) (hp : p.Prime) (ha : 0 < a) {y : ℤ} (hy : 0 < y) (h₁ : (ρ : ℤ) ∣ y - 1)
    (h₂ : (ρ : ℤ) ∣ (cyclotomic p ℤ).eval (y ^ p ^ (a - 1))) : ρ = p := by
  have : Fact p.Prime := ⟨hp⟩
  have h₃ : (ρ : ℤ) ∣ (cyclotomic p ℤ).eval (y ^ p ^ (a - 1)) - (cyclotomic p ℤ).eval 1 := by
    refine dvd_trans ?_ (sub_dvd_eval_sub _ _ _)
    simpa only [one_pow] using h₁.trans (sub_dvd_pow_sub_pow y 1 (p ^ (a - 1)))
  rw [eval_one_cyclotomic_prime] at h₃
  have h₄ : (ρ : ℤ) ∣ (p : ℤ) := by simpa using dvd_sub h₂ h₃
  exact (Nat.prime_dvd_prime_iff_eq hρ hp).mp (Int.natCast_dvd_natCast.mp h₄)

end MetaMathlibExt
