/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Series-divisors of products

For a sequence `s`, the series with coefficients `s (i + 1)` turns the positive-degree
recurrence for `F` into the identity `derivative F = mk (fun i ↦ s (i + 1)) * F`.
The product rule then adds the sequences.
-/

open PowerSeries

namespace MetaMathlibExt

/-- **Series-divisors add under multiplication.** Let $R$ be a commutative ring and let $A$, $B$
be formal power series over $R$ with coefficients $a(n)$, $b(n)$. Suppose $s_A, s_B$ are maps
$\mathbb{N} \to R$ with $n\,a(n) = \sum_{i=1}^{n} s_A(i)\,a(n-i)$ and
$n\,b(n) = \sum_{i=1}^{n} s_B(i)\,b(n-i)$ for every $n \ge 0$ (that is, $s_A$ and $s_B$ are
series-divisors of $A$ and $B$). Then, writing $c(n)$ for the coefficients of $AB$,
$n\,c(n) = \sum_{i=1}^{n} \bigl(s_A(i) + s_B(i)\bigr)\,c(n-i)$ for every $n \ge 0$, so $s_A + s_B$
is a series-divisor of $AB$.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Lemma 2
(`jis-2024-24.1.6-lem-2`). -/
public theorem series_divisor_add_of_mul {R : Type*} [CommRing R]
    (A B : PowerSeries R) (sA sB : ℕ → R)
    (hA : ∀ n : ℕ, (n : R) * coeff n A = ∑ i ∈ Finset.Icc 1 n, sA i * coeff (n - i) A)
    (hB : ∀ n : ℕ, (n : R) * coeff n B = ∑ i ∈ Finset.Icc 1 n, sB i * coeff (n - i) B) :
    ∀ n : ℕ, (n : R) * coeff n (A * B) =
      ∑ i ∈ Finset.Icc 1 n, (sA i + sB i) * coeff (n - i) (A * B) := by
  let S (s : ℕ → R) := PowerSeries.mk (fun i ↦ s (i + 1))
  have convolution (F : PowerSeries R) (s : ℕ → R) (n : ℕ) :
      coeff n (S s * F) = ∑ i ∈ Finset.Icc 1 (n + 1), s i * coeff (n + 1 - i) F := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp [S, Nat.add_comm 1]
  have recurrence (F : PowerSeries R) (s : ℕ → R) : derivative F = S s * F ↔
      ∀ n : ℕ, (n : R) * coeff n F = ∑ i ∈ Finset.Icc 1 n, s i * coeff (n - i) F := by
    rw [PowerSeries.ext_iff]
    simp_rw [coeff_derivative, convolution, mul_comm (coeff _ F), ← Nat.cast_succ]
    refine ⟨?_, fun h n ↦ h (n + 1)⟩
    rintro h (_ | n)
    · simp
    · exact h n
  have hadd : S (fun i ↦ sA i + sB i) = S sA + S sB := by
    ext i
    simp [S]
  apply (recurrence (A * B) (fun i ↦ sA i + sB i)).mp
  simp only [derivative.leibniz, smul_eq_mul, (recurrence A sA).mpr hA,
    (recurrence B sB).mpr hB, hadd]
  ring

end MetaMathlibExt
