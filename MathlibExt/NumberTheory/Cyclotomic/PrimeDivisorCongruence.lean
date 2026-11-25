/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

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

set_option linter.unusedVariables false in
/-- **Divisibility of $x^p - 1$ by $p$.** Let $p$ be a prime, let $x$ be a positive integer, and
let $\Phi_p$ be the $p$-th cyclotomic polynomial with integer coefficients. Then
$p \mid x^p - 1$ if and only if $p \mid x - 1$ and $p \mid \Phi_p(x)$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Lemma 2 (`integers-2026-A95-lem-2`). -/
public theorem prime_dvd_pow_self_sub_one_iff {p : ℕ} (hp : p.Prime) {x : ℤ}
    (hx : 0 < x) :
    (p : ℤ) ∣ x ^ p - 1 ↔ (p : ℤ) ∣ x - 1 ∧ (p : ℤ) ∣ (cyclotomic p ℤ).eval x := by
  have : Fact p.Prime := ⟨hp⟩
  have hpow : (p : ℤ) ∣ x ^ p - 1 ↔ (p : ℤ) ∣ x - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd (x ^ p - 1) p,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd (x - 1) p]
    simp only [Int.cast_sub, Int.cast_pow, Int.cast_one, ZMod.pow_card]
  rw [hpow]
  refine ⟨fun h => ⟨h, ?_⟩, And.left⟩
  have hx' : (x : ZMod p) = 1 := by
    simpa only [Int.cast_sub, Int.cast_one, sub_eq_zero] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd (x - 1) p).mpr h
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  calc
    (↑((cyclotomic p ℤ).eval x) : ZMod p) = (cyclotomic p (ZMod p)).eval (x : ZMod p) :=
      (cyclotomic.eval_apply x p (Int.castRingHom (ZMod p))).symm
    _ = 0 := by
      simpa only [hx', eval_one_cyclotomic_prime] using ZMod.natCast_self p

end MetaMathlibExt
