/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Finite.Basic

/-!
# Congruences for prime divisors of cyclotomic values

If distinct primes `ρ` and `p` satisfy `ρ ∣ Φ_p(x)`, then `x` reduces to a primitive `p`-th
root of unity in `ZMod ρ`. Its multiplicative order `p` therefore divides `ρ - 1`.
-/

namespace MetaMathlibExt

open Polynomial

set_option linter.unusedVariables false in
/-- **Prime divisors of $\Phi_p(x)$ other than $p$ are $1$ modulo $p$.** Let $\rho$ and $p$ be
distinct primes, let $x$ be a positive integer, and let $\Phi_p$ be the $p$-th cyclotomic
polynomial with integer coefficients. If $\rho \mid \Phi_p(x)$, then $\rho \equiv 1 \pmod p$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Proposition 1 (`integers-2026-A95-prop-1`). -/
public theorem prime_modEq_one_of_dvd_cyclotomic_eval {ρ p : ℕ} (hρ : ρ.Prime)
    (hp : p.Prime) (hne : ρ ≠ p) {x : ℤ} (hx : 0 < x)
    (h : (ρ : ℤ) ∣ (cyclotomic p ℤ).eval x) : Nat.ModEq p ρ 1 := by
  have : Fact ρ.Prime := ⟨hρ⟩
  have : NeZero (p : ZMod ρ) :=
    NeZero.of_not_dvd (ZMod ρ) (mt (Nat.prime_dvd_prime_iff_eq hρ hp).mp hne)
  have hroot : IsRoot (cyclotomic p (ZMod ρ)) (x : ZMod ρ) :=
    (cyclotomic.eval_apply x p (Int.castRingHom (ZMod ρ))).trans
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h)
  have hprim := isRoot_cyclotomic_iff.mp hroot
  refine ((Nat.modEq_iff_dvd' hρ.one_le).mpr ?_).symm
  rw [hprim.eq_orderOf]
  exact ZMod.orderOf_dvd_card_sub_one (hprim.ne_zero hp.ne_zero)

end MetaMathlibExt
