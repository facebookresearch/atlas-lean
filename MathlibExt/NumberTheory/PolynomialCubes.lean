/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Integers as sums of cubes of polynomials

For every integer `N` there are five nonconstant polynomials with integer coefficients whose cubes
add up to the constant polynomial `N` (`int_eq_sum_five_polynomial_cubes`). This is Theorem 2 of
Ajai Choudhry's paper on expressing an integer as a sum of cubes of polynomials.

Integers of the form `p ^ 3 + q ^ 3` or `2 * (p ^ 6 - q ^ 6)` are sums of just four cubes of
nonconstant polynomials (`int_sum_four_polynomial_cubes_of_cube_form`, Theorem 1).

## Proof outline for five cubes

Choudhry starts from the identity `6 * r = (r + 1) ^ 3 + (r - 1) ^ 3 - 2 * r ^ 3` and adds
`(-6 * t + j) ^ 3` to both sides. Since `j ^ 3 ≡ j [ZMOD 6]`, the equation
`6 * r + (-6 * t + j) ^ 3 = 6 * m + j` has a solution `r` that is a polynomial in `m` and `t`
with integer coefficients; the paper takes `j` among `0, 1, 2, 3, -2, -1` and writes out one
identity for each residue of an integer modulo `6`. Here `j = N` and `m = 0`, which covers every
integer `N` with a single identity: if `N ^ 3 - N = 6 * c`, then
`r = 36 * t ^ 3 - 18 * N * t ^ 2 + 3 * N ^ 2 * t - c` satisfies `6 * r + (N - 6 * t) ^ 3 = N`, so
`N = (r + 1) ^ 3 + (r - 1) ^ 3 + (-r) ^ 3 + (-r) ^ 3 + (N - 6 * t) ^ 3`.
The first four polynomials have degree `3` and the last one has degree `1`. For `N = 0, 1, 2, 3`
they are the polynomials of the paper's identities (3.1)–(3.4) with `m = 0`.

## Implementation notes

Both theorems keep their original full names in the `PolynomialCubesWanted` namespace.

## References

* Ajai Choudhry, *Expressing an integer as a sum of cubes of polynomials*, arXiv:2311.07325v1,
  Theorems 1 and 2 (<https://arxiv.org/abs/2311.07325>).
-/

@[expose] public section

namespace MathlibExt.NumberTheory.PolynomialCubesWanted

open Polynomial

/-- Choudhry's identity (2.1) gives four quadratics when `p + q ≠ 0`. -/
private theorem four_cubes_of_sum_of_cubes (p q : ℤ) :
    ∃ f g h k : ℤ[X],
      1 ≤ f.natDegree ∧ 1 ≤ g.natDegree ∧ 1 ≤ h.natDegree ∧ 1 ≤ k.natDegree ∧
        f ^ 3 + g ^ 3 + h ^ 3 + k ^ 3 = C (p ^ 3 + q ^ 3) := by
  by_cases hpq : p + q = 0
  · have hq : q = -p := by omega
    refine ⟨X, -X, X, -X, by simp, by simp, by simp, by simp, ?_⟩
    simp only [hq, map_add, map_neg, map_pow]
    ring
  let quad (a b c : ℤ) : ℤ[X] := C a * X ^ 2 + C b * X + C c
  let a := 2 * (p + q)
  have ha : a ≠ 0 := mul_ne_zero (by decide) hpq
  refine ⟨quad a (4 * q) q, quad a (4 * q) (-p + 2 * q),
    quad (-a) (p - 3 * q) p, quad (-a) (-(p + 5 * q)) (p - 2 * q), ?_⟩
  simp only [quad, natDegree_quadratic ha, natDegree_quadratic (neg_ne_zero.mpr ha),
    Nat.one_le_ofNat, true_and]
  simp only [a, map_add, map_sub, map_mul, map_neg, map_pow, C_ofNat]
  ring

/-- **Integers of the form $p^3 + q^3$ or $2(p^6 - q^6)$ as sums of four polynomial cubes.**
Let $p$ and $q$ be integers and let $N = p^3 + q^3$ or $N = 2(p^6 - q^6)$. Then there are
polynomials $f, g, h, k \in \mathbb{Z}[x]$, each of degree at least $1$, such that
$f^3 + g^3 + h^3 + k^3 = N$ as an identity in $\mathbb{Z}[x]$.

Source: Ajai Choudhry, "Expressing an Integer as a Sum of Cubes of
Polynomials", Theorem 1. -/
theorem int_sum_four_polynomial_cubes_of_cube_form
    (N p q : ℤ)
    (hN : N = p ^ 3 + q ^ 3 ∨ N = 2 * (p ^ 6 - q ^ 6)) :
    ∃ f g h k : Polynomial ℤ,
      1 ≤ f.natDegree ∧ 1 ≤ g.natDegree ∧ 1 ≤ h.natDegree ∧
        1 ≤ k.natDegree ∧
        f ^ 3 + g ^ 3 + h ^ 3 + k ^ 3 = Polynomial.C N := by
  rcases hN with rfl | rfl
  · exact four_cubes_of_sum_of_cubes p q
  -- With a zero slope in (2.2), the target is the sum of two equal integer cubes.
  by_cases hp : p = 0
  · subst p
    rw [show 2 * ((0 : ℤ) ^ 6 - q ^ 6) = (-q ^ 2) ^ 3 + (-q ^ 2) ^ 3 by ring]
    exact four_cubes_of_sum_of_cubes _ _
  by_cases hq : q = 0
  · subst q
    rw [show 2 * (p ^ 6 - (0 : ℤ) ^ 6) = (p ^ 2) ^ 3 + (p ^ 2) ^ 3 by ring]
    exact four_cubes_of_sum_of_cubes _ _
  -- The four polynomials in (2.2) now have nonzero slopes.
  refine ⟨C p * X + C (-q ^ 2), C (-p) * X + C (-q ^ 2),
    C q * X + C (p ^ 2), C (-q) * X + C (p ^ 2), ?_⟩
  simp only [natDegree_linear hp, natDegree_linear (neg_ne_zero.mpr hp), natDegree_linear hq,
    natDegree_linear (neg_ne_zero.mpr hq), le_refl, true_and]
  simp only [map_neg, map_pow, map_mul, map_sub, C_ofNat]
  ring

/-- Every integer is congruent to its cube modulo `6`. -/
private theorem six_dvd_cube_sub_self (N : ℤ) : (6 : ℤ) ∣ N ^ 3 - N := by
  have key : ∀ x : ZMod 6, x ^ 3 - x = 0 := by decide
  have h := key N
  rw [← Int.cast_pow, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  exact_mod_cast h

/-- **Every integer is a sum of five cubes of polynomials.** For every integer $N$ there are
polynomials $f, g, h, k, l \in \mathbb{Z}[x]$, each of degree at least $1$, such that
$f^3 + g^3 + h^3 + k^3 + l^3 = N$ as an identity in $\mathbb{Z}[x]$.

Source: Ajai Choudhry, "Expressing an Integer as a Sum of Cubes of
Polynomials", Theorem 2. -/
theorem int_eq_sum_five_polynomial_cubes (N : ℤ) :
    ∃ f g h k l : Polynomial ℤ,
      1 ≤ f.natDegree ∧ 1 ≤ g.natDegree ∧ 1 ≤ h.natDegree ∧
        1 ≤ k.natDegree ∧ 1 ≤ l.natDegree ∧
        f ^ 3 + g ^ 3 + h ^ 3 + k ^ 3 + l ^ 3 = Polynomial.C N := by
  obtain ⟨c, hc⟩ := six_dvd_cube_sub_self N
  -- Since `N ^ 3 - N = 6 * c`, `r` solves `6 * r + (N - 6 * X) ^ 3 = N`.
  set r : ℤ[X] := C 36 * X ^ 3 + C (-18 * N) * X ^ 2 + C (3 * N ^ 2) * X + C (-c) with hr
  have hr3 : r.natDegree = 3 := natDegree_cubic (by norm_num)
  refine ⟨r + 1, r - 1, -r, -r, C (-6) * X + C N, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← C_1, natDegree_add_C, hr3]; norm_num
  · rw [← C_1, natDegree_sub_C, hr3]; norm_num
  · rw [natDegree_neg, hr3]; norm_num
  · rw [natDegree_neg, hr3]; norm_num
  · rw [natDegree_linear (by norm_num)]
  · -- `(r + 1) ^ 3 + (r - 1) ^ 3 + (-r) ^ 3 + (-r) ^ 3 = 6 * r`.
    have hcC : C N ^ 3 - C N = 6 * C c := by
      rw [← C_pow, ← C_sub, hc, C_mul, C_ofNat]
    simp only [hr, map_neg, map_mul, map_pow, C_ofNat]
    linear_combination hcC

end MathlibExt.NumberTheory.PolynomialCubesWanted
