/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# Common prime divisors of cyclotomic values

If primes `ρ` and `p` satisfy `ρ ∣ x - 1` and `ρ ∣ Φ_p(x)`, then `ρ = p`.
Indeed, `Polynomial.sub_dvd_eval_sub` gives `ρ ∣ Φ_p(x) - Φ_p(1)`, so `ρ` divides
`Φ_p(1) = p`. Applying this result at `x = y ^ p ^ (a - 1)` gives the powered statement,
since `y - 1` divides `y ^ p ^ (a - 1) - 1`.

## References

* Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026), Article A95,
  the source of both statements. In the arXiv preprint arXiv:2412.00010v1 (*Hybrid bounds for prime
  divisors*), Lemma 4.2 gives the powered statement.
-/

namespace MetaMathlibExt

open Polynomial

set_option linter.unusedVariables false in
/-- **A common prime divisor of $x - 1$ and $\Phi_p(x)$ is $p$.** Let $\rho$ and $p$ be primes,
let $x$ be a positive integer, and let $\Phi_p$ be the $p$-th cyclotomic polynomial with integer
coefficients. If $\rho \mid x - 1$ and $\rho \mid \Phi_p(x)$, then $\rho = p$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Lemma 1 (`integers-2026-A95-lem-1`). -/
public theorem prime_eq_of_dvd_sub_one_of_dvd_cyclotomic_eval {ρ p : ℕ}
    (hρ : ρ.Prime) (hp : p.Prime) {x : ℤ} (hx : 0 < x) (h₁ : (ρ : ℤ) ∣ x - 1)
    (h₂ : (ρ : ℤ) ∣ (cyclotomic p ℤ).eval x) : ρ = p := by
  have : Fact p.Prime := ⟨hp⟩
  have hdiff := h₁.trans (sub_dvd_eval_sub x 1 (cyclotomic p ℤ))
  have hdvd : (ρ : ℤ) ∣ (p : ℤ) := by simpa using dvd_sub h₂ hdiff
  exact (Nat.prime_dvd_prime_iff_eq hρ hp).mp (Int.natCast_dvd_natCast.mp hdvd)

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
  exact prime_eq_of_dvd_sub_one_of_dvd_cyclotomic_eval hρ hp (pow_pos hy _)
    (h₁.trans (sub_one_dvd_pow_sub_one y _)) h₂

end MetaMathlibExt
