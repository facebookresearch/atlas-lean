/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Cyclotomic.RealCyclotomicPolynomial
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-- Divisibility between trace minpolys from root minpoly equality.

Given primitive `n`-th roots `u`, `v` in `ℂ` with the same minpoly over `ℤ`,
the minpoly of the trace `t' = v + v⁻¹` divides the minpoly of `t = u + u⁻¹`.

The argument: with `P = minpoly ℤ t` of degree `m`, form
`Q(X) = ∑ᵢ P.coeff i * X^(m-i) * (X^2+1)^i`, so that
`aeval w Q = w^m * aeval (w + w⁻¹) P` for `w ≠ 0`.
Since `aeval t P = 0`, we get `aeval u Q = 0`, hence `minpoly ℤ u ∣ Q`;
by hypothesis the same holds for `v`, giving `aeval v Q = 0` and therefore
`aeval t' P = 0` (as `v^m ≠ 0`), i.e. `minpoly ℤ t' ∣ P`. -/
private theorem minpoly_add_inv_dvd_of_minpoly_eq (n : ℕ) (u v t t' : ℂ) (hn : 0 < n)
    (hu : IsPrimitiveRoot u n) (hv : IsPrimitiveRoot v n)
    (hμ : minpoly ℤ u = minpoly ℤ v)
    (ht : t = u + u⁻¹) (ht' : t' = v + v⁻¹)
    (_hint : IsIntegral ℤ t) (hint' : IsIntegral ℤ t') :
    minpoly ℤ t' ∣ minpoly ℤ t := by
  have huv : u ≠ 0 := hu.ne_zero (by omega)
  have hvv : v ≠ 0 := hv.ne_zero (by omega)
  have huint : IsIntegral ℤ u := hu.isIntegral hn
  have hvint : IsIntegral ℤ v := hv.isIntegral hn
  set Q := ∑ i ∈ Finset.range ((minpoly ℤ t).natDegree + 1),
    Polynomial.C ((minpoly ℤ t).coeff i) *
      (Polynomial.X ^ ((minpoly ℤ t).natDegree - i) * (Polynomial.X ^ 2 + 1) ^ i) with hQdef
  have key : ∀ w : ℂ, w ≠ 0 → Polynomial.aeval w Q =
      w ^ (minpoly ℤ t).natDegree * Polynomial.aeval (w + w⁻¹) (minpoly ℤ t) := by
    intro w hw
    have hsum : w ^ (minpoly ℤ t).natDegree * Polynomial.aeval (w + w⁻¹) (minpoly ℤ t)
        = ∑ i ∈ Finset.range ((minpoly ℤ t).natDegree + 1),
          w ^ (minpoly ℤ t).natDegree * ((minpoly ℤ t).coeff i • (w + w⁻¹) ^ i) := by
      rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum]
    rw [hQdef, map_sum, hsum]
    apply Finset.sum_congr rfl
    intro i hi
    have him : i ≤ (minpoly ℤ t).natDegree := by
      have hmem := Finset.mem_range.mp hi
      omega
    have hwsq : w ^ 2 + 1 = w * (w + w⁻¹) := by
      rw [mul_add, mul_inv_cancel₀ hw, pow_two]
    have hinner : Polynomial.aeval w ((Polynomial.X ^ 2 + 1 : Polynomial ℤ)) = w * (w + w⁻¹) := by
      rw [map_add, map_pow, map_one, Polynomial.aeval_X]
      exact hwsq
    have e2 : Polynomial.aeval w ((Polynomial.X ^ ((minpoly ℤ t).natDegree - i) *
        (Polynomial.X ^ 2 + 1) ^ i : Polynomial ℤ))
        = w ^ (minpoly ℤ t).natDegree * (w + w⁻¹) ^ i := by
      rw [map_mul, map_pow, map_pow, Polynomial.aeval_X, hinner, mul_pow,
        ← mul_assoc, ← pow_add, Nat.sub_add_cancel him]
    rw [map_mul, Polynomial.aeval_C, e2, Algebra.smul_def (R := ℤ) (A := ℂ)]
    ring
  have hQu : Polynomial.aeval u Q = 0 := by
    rw [key u huv, ← ht, minpoly.aeval, mul_zero]
  have hdvdQ : minpoly ℤ u ∣ Q := minpoly.isIntegrallyClosed_dvd huint hQu
  rw [hμ] at hdvdQ
  have hQv : Polynomial.aeval v Q = 0 :=
    (minpoly.isIntegrallyClosed_dvd_iff hvint Q).mpr hdvdQ
  rw [key v hvv, ← ht'] at hQv
  have hvm : v ^ (minpoly ℤ t).natDegree ≠ 0 := pow_ne_zero _ hvv
  have ht'P : Polynomial.aeval t' (minpoly ℤ t) = 0 :=
    (mul_eq_zero.mp hQv).resolve_left hvm
  exact minpoly.isIntegrallyClosed_dvd hint' ht'P

/-- **Minimal polynomial of $2\cos(2\pi k/n)$ for $k$ coprime to $n$.** Let $n$ and $k$ be natural
numbers with $n > 2$ and $\gcd(k, n) = 1$. Then the real cyclotomic polynomial $\psi_n$ equals
the minimal polynomial over $\mathbb{Z}$ of the complex number $2\cos(2\pi k/n)$.

No bound on $k$ is needed, since the cosine depends only on $k$ modulo $n$. -/
theorem realCyclotomicPolynomial_eq_minpoly_two_cos
    {n k : ℕ} (hn : 2 < n) (hcop : Nat.Coprime k n) :
    realCyclotomicPolynomial n =
      minpoly ℤ (((2 * Real.cos (2 * (k : ℝ) * Real.pi / (n : ℝ)) : ℝ) : ℂ)) := by
  have hn0 : 0 < n := by omega
  have hn_ne : n ≠ 0 := by omega
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn_ne
  have hunfold : realCyclotomicPolynomial n
      = minpoly ℤ (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) +
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)))⁻¹) := rfl
  rw [hunfold]
  set ζ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) with hζdef
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn_ne
  have hζk : IsPrimitiveRoot (ζ ^ k) n := hζ.pow_of_coprime k hcop
  have hμ : minpoly ℤ ζ = minpoly ℤ (ζ ^ k) := hζ.minpoly_eq_pow_coprime hcop
  have hcos : (((2 * Real.cos (2 * (k : ℝ) * Real.pi / (n : ℝ)) : ℝ)) : ℂ)
      = (ζ ^ k) + (ζ ^ k)⁻¹ := by
    have hexp1 : Complex.exp (((2 * (k : ℝ) * Real.pi / (n : ℝ) : ℝ) : ℂ) *
        Complex.I) = ζ ^ k := by
      rw [hζdef, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hexp2 : Complex.exp (-(((2 * (k : ℝ) * Real.pi / (n : ℝ) : ℝ) : ℂ) *
        Complex.I)) = (ζ ^ k)⁻¹ := by
      rw [Complex.exp_neg, hexp1]
    have h2cos : ((((2 * Real.cos (2 * (k : ℝ) * Real.pi / (n : ℝ)) : ℝ))) : ℂ)
        = 2 * Complex.cos ((((2 * (k : ℝ) * Real.pi / (n : ℝ) : ℝ))) : ℂ) := by
      simp
    rw [h2cos, Complex.two_cos, neg_mul, hexp1, hexp2]
  have hζinv : IsIntegral ℤ ζ⁻¹ := hζ.inv.isIntegral hn0
  have ht1 : IsIntegral ℤ (ζ + ζ⁻¹) := (hζ.isIntegral hn0).add hζinv
  have ht2 : IsIntegral ℤ
      (((2 * Real.cos (2 * (k : ℝ) * Real.pi / (n : ℝ)) : ℝ)) : ℂ) := by
    rw [hcos]
    exact (hζk.isIntegral hn0).add (hζk.inv.isIntegral hn0)
  have h1 : minpoly ℤ (((2 * Real.cos (2 * (k : ℝ) * Real.pi / (n : ℝ)) : ℝ)) : ℂ)
      ∣ minpoly ℤ (ζ + ζ⁻¹) :=
    minpoly_add_inv_dvd_of_minpoly_eq n ζ (ζ ^ k) (ζ + ζ⁻¹)
      (((2 * Real.cos (2 * (k : ℝ) * Real.pi / (n : ℝ)) : ℝ)) : ℂ)
      hn0 hζ hζk hμ rfl hcos ht1 ht2
  have h2 : minpoly ℤ (ζ + ζ⁻¹)
      ∣ minpoly ℤ (((2 * Real.cos (2 * (k : ℝ) * Real.pi / (n : ℝ)) : ℝ)) : ℂ) :=
    minpoly_add_inv_dvd_of_minpoly_eq n (ζ ^ k) ζ
      (((2 * Real.cos (2 * (k : ℝ) * Real.pi / (n : ℝ)) : ℝ)) : ℂ) (ζ + ζ⁻¹)
      hn0 hζk hζ hμ.symm hcos rfl ht2 ht1
  have hmonic1 : (minpoly ℤ (ζ + ζ⁻¹)).Monic := minpoly.monic ht1
  have hmonic2 : (minpoly ℤ
      (((2 * Real.cos (2 * (k : ℝ) * Real.pi / (n : ℝ)) : ℝ)) : ℂ)).Monic :=
    minpoly.monic ht2
  have hle : (minpoly ℤ (ζ + ζ⁻¹)).natDegree
      ≤ (minpoly ℤ (((2 * Real.cos (2 * (k : ℝ) * Real.pi / (n : ℝ)) : ℝ)) : ℂ)).natDegree :=
    Polynomial.natDegree_le_of_dvd h2 hmonic2.ne_zero
  have heq : minpoly ℤ (ζ + ζ⁻¹)
      = minpoly ℤ (((2 * Real.cos (2 * (k : ℝ) * Real.pi / (n : ℝ)) : ℝ)) : ℂ) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmonic2 hmonic1 h1 hle
  exact heq

set_option linter.unusedVariables false in
/-- **Minimal polynomial of $2\cos(2\pi k/n)$ for $1 \le k \le n$ coprime to $n$.** Let $n$ and
$k$ be natural numbers with $n > 2$, $1 \le k \le n$ and $\gcd(k, n) = 1$. Then the real
cyclotomic polynomial $\psi_n$ equals the minimal polynomial over $\mathbb{Z}$ of the complex
number $2\cos(2\pi k/n)$.

The bounds $1 \le k \le n$ are not needed: the same holds for every $k$ coprime to $n$.

Proves `Wanted` entry `realCyclotomicPolynomial_eq_minpoly_two_cos_of_coprime`.

Source: Pinthira Tangsupphathawat and Vichian Laohakosol, "Minimal Polynomials of
Algebraic Cosine Values at Rational Multiples of π", Journal of Integer Sequences 19
(2016), source lines 83-90:
https://cs.uwaterloo.ca/journals/JIS/VOL19/Laohakosol/lao2.tex
source SHA-256 15e6923301658b132cd14eb587f480152fbf9dd9554ecbc6ce321216d9314455
normalized no-final-newline span SHA-256
e91ccd0347f84043d402747f2c4aaf5e6d5f22cba3840369c7fb8a8732dbe039
-/
theorem realCyclotomicPolynomial_eq_minpoly_two_cos_of_coprime
    {n k : ℕ} (hn : 2 < n) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (hcop : Nat.Coprime k n) :
    realCyclotomicPolynomial n =
      minpoly ℤ (((2 * Real.cos (2 * (k : ℝ) * Real.pi / (n : ℝ)) : ℝ) : ℂ)) :=
  realCyclotomicPolynomial_eq_minpoly_two_cos hn hcop

end MetaMathlibExt
