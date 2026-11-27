/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.BinomialHarmonicConvolution

/-!
# Shifted binomial–harmonic convolution

We prove the shifted binomial–harmonic convolution for `1 ≤ k ≤ n - 1`.

Source: Horst Alzer and Man Kam Kwong,
"Ramanujan and a Combinatorial Identity Involving Harmonic Numbers",
*Journal of Integer Sequences* 29 (2026), Article 26.4.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Alzer/alzer22.html>).
The publisher TeX is <https://cs.uwaterloo.ca/journals/JIS/VOL29/Alzer/alzer22.tex>.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.RamanujanHarmonicIdentityWanted

private lemma choose_correction (k n : ℕ) (hn : 0 < n) :
    (1 / ((k : ℚ) + 1)) * (Nat.choose (n + k + 1) (k + 1) : ℚ) =
      (Nat.choose (n + k) (k + 1) : ℚ) * (((k : ℚ) + 1)⁻¹ + (n : ℚ)⁻¹) := by
  have h := Nat.choose_mul_succ_eq (n + k) (k + 1)
  rw [show n + k + 1 - (k + 1) = n by omega] at h
  have hQ : (Nat.choose (n + k) (k + 1) : ℚ) * ((n : ℚ) + k + 1) =
      (Nat.choose (n + k + 1) (k + 1) : ℚ) * n := by exact_mod_cast h
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hkQ : (k : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  linear_combination -hQ

/-- **Shifted binomial–harmonic convolution (Alzer–Kwong, Corollary 3, Eq. (1.4)).** For natural
numbers $k$ and $n$ with $1 \le k \le n - 1$,
$$
\sum_{\nu=1}^{n} \Bigl(\binom{n+k-\nu-1}{n-2} - \binom{n+k-\nu-1}{k}\Bigr) H_\nu =
\binom{n+k}{k+1} (H_k - H_n) + \frac{1}{k+1} \binom{n+k+1}{k+1},
$$
where $H_m = \sum_{j=1}^{m} 1/j$ is the $m$-th harmonic number.

Source: Horst Alzer and Man Kam Kwong, "Ramanujan and a
Combinatorial Identity Involving Harmonic Numbers",
Corollary 3, Eq. (1.4). -/
public theorem sum_choose_sub_choose_mul_harmonic_eq_add
    (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n - 1) :
    ∑ ν ∈ Finset.Icc 1 n,
        ((Nat.choose (n + k - ν - 1) (n - 2) : ℚ) -
          (Nat.choose (n + k - ν - 1) k : ℚ)) * harmonic ν =
      (Nat.choose (n + k) (k + 1) : ℚ) * (harmonic k - harmonic n) +
        (1 / ((k : ℚ) + 1)) * (Nat.choose (n + k + 1) (k + 1) : ℚ)
    := by
  have hn : 2 ≤ n := by omega
  rw [choose_correction k n (by omega)]
  by_cases heq : k = n - 1
  · have h := MetaMathlibExt.binomial_harmonic_convolution k n (by omega) (by omega)
    have hsucc : k + 1 = n := by omega
    have hsymm : (n + k).choose k = (n + k).choose (k + 1) :=
      Nat.choose_symm_of_eq_add (by omega)
    have hsum :
        (∑ ν ∈ Finset.Icc 1 n,
          ((Nat.choose (n + k - ν - 1) (n - 2) : ℚ) -
            (Nat.choose (n + k - ν - 1) k : ℚ)) * harmonic ν) =
        -(∑ ν ∈ Finset.Icc 1 n,
          ((Nat.choose (n + k - ν - 1) (n - 1) : ℚ) -
            (Nat.choose (n + k - ν - 1) (k - 1) : ℚ)) * harmonic ν) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro ν _
      rw [heq, show n - 1 - 1 = n - 2 by omega]
      ring
    have hH : harmonic n = harmonic k + (n : ℚ)⁻¹ := by
      simpa only [hsucc] using harmonic_succ k
    have hcast : (k : ℚ) + 1 = (n : ℚ) := by exact_mod_cast hsucc
    rw [hsum, h, hsymm, hcast, hH]
    ring
  · have h := MetaMathlibExt.binomial_harmonic_convolution (k + 1) (n - 1)
      (by omega) (by omega)
    have htop : (n - 1) + (k + 1) = n + k := by omega
    simp only [htop, Nat.add_sub_cancel, show n - 1 - 1 = n - 2 by omega] at h
    have hsum :
        (∑ ν ∈ Finset.Icc 1 n,
          ((Nat.choose (n + k - ν - 1) (n - 2) : ℚ) -
            (Nat.choose (n + k - ν - 1) k : ℚ)) * harmonic ν) =
        ∑ ν ∈ Finset.Icc 1 (n - 1),
          ((Nat.choose (n + k - ν - 1) (n - 2) : ℚ) -
            (Nat.choose (n + k - ν - 1) k : ℚ)) * harmonic ν := by
      rw [show Finset.Icc 1 n = Finset.Icc 1 ((n - 1) + 1) by congr 1; omega,
        Finset.sum_Icc_succ_top (by omega), show n - 1 + 1 = n by omega]
      simp [Nat.choose_eq_zero_of_lt (show k - 1 < n - 2 by omega),
        Nat.choose_eq_zero_of_lt (show k - 1 < k by omega)]
    have hH : harmonic n = harmonic (n - 1) + (n : ℚ)⁻¹ := by
      simpa only [show n - 1 + 1 = n by omega] using harmonic_succ (n - 1)
    rw [hsum, h, harmonic_succ, hH]
    push_cast
    ring

end MathlibExt.NumberTheory.RamanujanHarmonicIdentityWanted
