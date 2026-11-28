/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.PadicNorm

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic.LinearCombination

/-!
# Wilson's theorem modulo the cube of an odd prime

For an odd prime $p$ and $1 \le i \le p-1$, let $\delta_0(i)$ and $\delta_1(i)$ be the
coefficients of $p$ and $p^2$ in the base-$p$ expansion of $i^{p-1}$. Then, with all sums
running over $1 \le i \le p-1$,

$$
(p-1)! \equiv -1 + p\sum_i\delta_0(i) + p^2\sum_i(\delta_0(i)+\delta_1(i))
- \frac{p^2}{2}\left(\left(\sum_i\delta_0(i)\right)^2+\sum_i\delta_0(i)^2\right)
\pmod{p^3}.
$$

The proof compares two quadratic expansions of $((p-1)!)^{p-1}$ in `ZMod (p ^ 3)`:
one from the digits of each factor and one from ordinary Wilson's theorem. It keeps a factor
of two until passing to the $p$-adic norm on $\mathbb{Q}$, where two has norm one.

## References

* Claire Levaillant, *Wilson's Theorem Modulo $p^2$ Derived from Faulhaber Polynomials*,
  INTEGERS **24** (2024), Article A87, pp. 1–17, Theorem 3, equations (4)–(5).
  <https://math.colgate.edu/~integers/y87/y87.pdf>
* `MathlibExt.NumberTheory.WilsonFermatQuotient`, `wilson_mod_prime_sq`: the comparison
  with the expansion of the Wilson lift is the quadratic version of the linear argument there.
  This avoids the Hensel lifting in the source paper.
-/

set_option autoImplicit false

open Finset

namespace MathlibExt.NumberTheory.WilsonFaulhaberWanted

private def digit0 (p i : ℕ) : ℕ := (i ^ (p - 1) - 1) / p % p

private def digit1 (p i : ℕ) : ℕ := (i ^ (p - 1) - 1) / p ^ 2 % p

-- Doubling the expansion turns the quadratic cross-terms into a square minus its diagonal.
private theorem twice_prod_of_cube_zero {R ι : Type*} [CommRing R]
    (x : R) (hx : x ^ 3 = 0) (s : Finset ι) (a b : ι → R) :
    2 * (∏ i ∈ s, (1 + x * a i + x ^ 2 * b i)) =
      2 + 2 * x * (∑ i ∈ s, a i) + x ^ 2 *
        (2 * (∑ i ∈ s, b i) + (∑ i ∈ s, a i) ^ 2 - ∑ i ∈ s, a i ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    let A := ∑ j ∈ s, a j
    let D := 2 * (∑ j ∈ s, b j) + A ^ 2 - ∑ j ∈ s, a j ^ 2
    rw [prod_insert hi, mul_left_comm (2 : R), ih, sum_insert hi, sum_insert hi, sum_insert hi]
    linear_combination (a i * D + 2 * b i * A + x * b i * D) * hx

private theorem pow_eq_digits {p i : ℕ} (hp : p.Prime) (hi : i ∈ Icc 1 (p - 1)) :
    (i : ZMod (p ^ 3)) ^ (p - 1) =
      1 + (p : ZMod (p ^ 3)) * (digit0 p i : ZMod (p ^ 3)) +
        (p : ZMod (p ^ 3)) ^ 2 * (digit1 p i : ZMod (p ^ 3)) := by
  obtain ⟨hi₁, hi₂⟩ := mem_Icc.mp hi
  have hi_lt := hi₂.trans_lt (Nat.sub_lt hp.pos Nat.one_pos)
  have hcop := (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hi₁ hi_lt)).symm
  let n := i ^ (p - 1) - 1
  let q := n / p
  have hrem : n % p = 0 := Nat.pow_card_sub_one_sub_one_mod_card hp hcop
  have hquot : p * q = n := by simpa only [hrem, zero_add] using Nat.mod_add_div n p
  have hpow : 1 + n = i ^ (p - 1) := by
    have : 0 < i ^ (p - 1) := pow_pos hi₁ _
    dsimp [n]
    omega
  have he : digit1 p i = (q / p) % p := by
    dsimp [digit1, q, n]
    rw [Nat.div_div_eq_div_mul, pow_two]
  have hq : digit0 p i + p * (digit1 p i + p * (q / p / p)) = q := by
    rw [he]
    change q % p + p * ((q / p) % p + p * (q / p / p)) = q
    rw [Nat.mod_add_div, Nat.mod_add_div]
  have hdecomp : i ^ (p - 1) = 1 + p * (digit0 p i + p * (digit1 p i + p * (q / p / p))) := by
    rw [hq, hquot, hpow]
  have hcast := congrArg (fun m : ℕ ↦ (m : ZMod (p ^ 3))) hdecomp
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_mul] at hcast
  have hx : (p : ZMod (p ^ 3)) ^ 3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [hcast]
  linear_combination (↑(q / p / p) : ZMod (p ^ 3)) * hx

private theorem factorial_twice_eq_in_zmod (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    let R := ZMod (p ^ 3)
    let x : R := p
    let s := Icc 1 (p - 1)
    let a (i : ℕ) : R := digit0 p i
    let b (i : ℕ) : R := digit1 p i
    let A := ∑ i ∈ s, a i
    let B := ∑ i ∈ s, b i
    let Q := ∑ i ∈ s, a i ^ 2
    let F : R := Nat.factorial (p - 1)
    2 * F = -2 + 2 * x * A + x ^ 2 * (2 * (A + B) - A ^ 2 - Q) := by
  intro R x s a b A B Q F
  have hx : x ^ 3 = 0 := by
    dsimp [x, R]
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hfac : ∏ i ∈ s, (i : R) = F := by
    rw [← Finset.prod_natCast]
    exact congrArg (fun m : ℕ ↦ (m : R)) <| by
      dsimp [s]
      rw [← Ico_add_one_right_eq_Icc, Finset.prod_Ico_id_eq_factorial]
  have hdigits : 2 * F ^ (p - 1) = 2 + 2 * x * A + x ^ 2 * (2 * B + A ^ 2 - Q) := by
    rw [← hfac, ← Finset.prod_pow]
    have h := Finset.prod_congr rfl (fun i hi ↦ pow_eq_digits hp hi :
      ∀ i ∈ s, (i : R) ^ (p - 1) = 1 + x * a i + x ^ 2 * b i)
    rw [h]
    exact twice_prod_of_cube_zero x hx s a b
  -- Lift ordinary Wilson's congruence from modulus p to an exact integer identity.
  obtain ⟨w, hw⟩ : (p : ℤ) ∣ (Nat.factorial (p - 1) : ℤ) + 1 := by
    let : Fact p.Prime := ⟨hp⟩
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp [ZMod.wilsons_lemma p]
  let W : R := w
  have hF : F + 1 = x * W := by
    simpa only [F, x, W, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one]
      using congrArg (fun m : ℤ ↦ (m : R)) hw
  have hneg : F = -(1 + x * -W) := by linear_combination hF
  have hWilson : 2 * F ^ (p - 1) = 2 + 2 * x * W + x ^ 2 * (2 * W ^ 2 - 2 * W) := by
    have h := twice_prod_of_cube_zero x hx (range (p - 1)) (fun _ ↦ -W) (fun _ ↦ 0)
    simp only [mul_zero, add_zero, prod_const, card_range, sum_const, nsmul_eq_mul] at h
    rw [Nat.cast_sub hp.one_le, Nat.cast_one] at h
    rw [hneg, (hp.even_sub_one hp2).neg_pow]
    linear_combination h + (x - 3) * W ^ 2 * hx
  -- The comparison makes 2x(W - A) a multiple of x², so the quadratic correction
  -- is unchanged on replacing W by A.
  have hfirst : 2 * x * (W - A) = x ^ 2 * (2 * B + A ^ 2 - Q - 2 * W ^ 2 + 2 * W) := by
    linear_combination hdigits - hWilson
  have hsecond : x ^ 2 * (2 * W - 2 * W ^ 2) = x ^ 2 * (2 * A - 2 * A ^ 2) := by
    linear_combination x * (1 - W - A) * hfirst +
      (1 - W - A) * (2 * B + A ^ 2 - Q - 2 * W ^ 2 + 2 * W) * hx
  linear_combination 2 * hF + hfirst + hsecond

/-- **Theorem 3**: for an odd prime `p` let `δ₀(k)`, `δ₁(k)` be the second and
third `p`-adic digits of `k^(p-1) ≡ 1 + p δ₀(k) + p^2 δ₁(k) (mod p^3)` (here
`((k^(p-1) - 1)/p) % p` and `((k^(p-1) - 1)/p^2) % p`). Then
`(p - 1)! ≡ -1 + p ∑ δ₀(i) + p^2 ∑ (δ₀(i) + δ₁(i)) - (p^2/2)((∑ δ₀(i))^2 + ∑ δ₀(i)^2)
(mod p^3)`, sums over `1 ≤ i ≤ p - 1`, read in `ℚ` through the `p`-adic norm.
`p ≠ 2` is added (the formula divides by `2`; at `p = 2` the difference is `2`).

Source: Claire Levaillant, *Wilson's Theorem Modulo p^2 Derived from Faulhaber
Polynomials*, INTEGERS 24 (2024), Article A87, Theorem 3. -/
public theorem wilson_mod_prime_cube_digits (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    padicNorm p ((Nat.factorial (p - 1) : ℚ) -
      (-1 + p * ∑ i ∈ Finset.Icc 1 (p - 1), (((i ^ (p - 1) - 1) / p % p : ℕ) : ℚ) +
        p ^ 2 * ∑ i ∈ Finset.Icc 1 (p - 1),
          ((((i ^ (p - 1) - 1) / p % p : ℕ) : ℚ) + (((i ^ (p - 1) - 1) / p ^ 2 % p : ℕ) : ℚ)) -
        p ^ 2 / 2 * ((∑ i ∈ Finset.Icc 1 (p - 1), (((i ^ (p - 1) - 1) / p % p : ℕ) : ℚ)) ^ 2 +
          ∑ i ∈ Finset.Icc 1 (p - 1), (((i ^ (p - 1) - 1) / p % p : ℕ) : ℚ) ^ 2))) ≤
      (p : ℚ) ^ (-3 : ℤ) := by
  let : Fact p.Prime := ⟨hp⟩
  let s := Icc 1 (p - 1)
  let z : ℤ := 2 * (Nat.factorial (p - 1) : ℤ) -
    (-2 + 2 * p * (∑ i ∈ s, (digit0 p i : ℤ)) + (p : ℤ) ^ 2 *
      (2 * ((∑ i ∈ s, (digit0 p i : ℤ)) + ∑ i ∈ s, (digit1 p i : ℤ)) -
        (∑ i ∈ s, (digit0 p i : ℤ)) ^ 2 - ∑ i ∈ s, (digit0 p i : ℤ) ^ 2))
  have hz : (↑(p ^ 3 : ℕ) : ℤ) ∣ z := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    dsimp [z]
    push_cast
    exact sub_eq_zero.mpr (factorial_twice_eq_in_zmod p hp hp2)
  have hnorm := (padicNorm.dvd_iff_norm_le (p := p)).mp hz
  have htwo : padicNorm p (2 : ℚ) = 1 := by
    apply (padicNorm.nat_eq_one_iff (p := p) 2).mpr
    exact fun hd ↦ hp2 ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hp.ne_one)
  let E : ℚ := (Nat.factorial (p - 1) : ℚ) -
    (-1 + p * (∑ i ∈ s, (digit0 p i : ℚ)) + (p : ℚ) ^ 2 *
      (∑ i ∈ s, ((digit0 p i : ℚ) + (digit1 p i : ℚ))) -
      (p : ℚ) ^ 2 / 2 * ((∑ i ∈ s, (digit0 p i : ℚ)) ^ 2 + ∑ i ∈ s, (digit0 p i : ℚ) ^ 2))
  change padicNorm p E ≤ _
  have hE : (z : ℚ) = 2 * E := by
    dsimp [z, E]
    push_cast
    rw [Finset.sum_add_distrib]
    ring
  rwa [hE, padicNorm.mul, htwo, one_mul] at hnorm

end MathlibExt.NumberTheory.WilsonFaulhaberWanted
