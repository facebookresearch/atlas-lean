/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Basic

/-!
# Prime-power congruence for truncated Euler products

Raising a finite Euler product to a prime power gives a coefficientwise congruence
with the product in which the prime scales each exponent of the variable.
-/

namespace MetaMathlibExt

open Polynomial

set_option linter.unusedVariables false in
/--
**Prime-power congruence for truncated Euler products.** Let $s$ and $t$ be positive integers,
let $p$ be a prime and let $N$ be a natural number. Then every coefficient of the polynomial
$$\Big(\prod_{m=1}^{N} (1 - X^{sm})\Big)^{p^t} - \Big(\prod_{m=1}^{N} (1 - X^{spm})\Big)^{p^{t-1}}$$
in $\mathbb{Z}[X]$ is divisible by $p^t$.

Since the truncated products agree with the infinite products in all degrees up to $N$, letting
$N$ grow gives the congruence of formal power series
$\prod_{m \ge 1} (1 - q^{sm})^{p^t} \equiv \prod_{m \ge 1} (1 - q^{spm})^{p^{t-1}} \pmod{p^t}$.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Lemma 1.
-/
public theorem finiteEulerProduct_primePower_congruence
    (s t p N : ℕ) (hs : 0 < s) (ht : 0 < t) (hp : p.Prime) :
    ∀ r : ℕ, (p : ℤ) ^ t ∣
      ((∏ m ∈ Finset.Icc 1 N,
          ((1 : Polynomial ℤ) - Polynomial.X ^ (s * m))) ^ (p ^ t) -
        (∏ m ∈ Finset.Icc 1 N,
          ((1 : Polynomial ℤ) - Polynomial.X ^ (s * p * m))) ^
            (p ^ (t - 1))).coeff r := by
  let F (a : ℕ) : Polynomial ℤ := ∏ m ∈ Finset.Icc 1 N, (1 - X ^ (a * m))
  have : Fact p.Prime := ⟨hp⟩
  have hmod : ((F s) ^ p).map (Int.castRingHom (ZMod p)) =
      (F (s * p)).map (Int.castRingHom (ZMod p)) := by
    simp only [F, Polynomial.map_pow, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_one,
      Polynomial.map_X, ← Finset.prod_pow, sub_pow_char, one_pow, ← pow_mul,
      Nat.mul_right_comm s _ p]
  have hdvd : (p : Polynomial ℤ) ∣ (F s) ^ p - F (s * p) := by
    rw [← C_eq_natCast, C_dvd_iff_dvd_coeff]
    intro r
    rw [coeff_sub, ← ZMod.intCast_eq_intCast_iff_dvd_sub]
    simpa only [coeff_map, Int.coe_castRingHom] using congrArg (·.coeff r) hmod.symm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  apply (C_dvd_iff_dvd_coeff _ _).mp
  simpa only [map_pow, C_eq_natCast, Nat.succ_sub_one, ← pow_mul, ← pow_succ'] using
    dvd_sub_pow_of_dvd_sub hdvd k

end MetaMathlibExt
