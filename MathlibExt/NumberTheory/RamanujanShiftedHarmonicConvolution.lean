/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Order.Interval.Finset.Nat
import MathlibExt.NumberTheory.BinomialHarmonicConvolution
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring

/-!
# A shifted binomial–harmonic convolution

## References

* Horst Alzer and Man Kam Kwong, *Ramanujan and a Combinatorial Identity Involving Harmonic
  Numbers*, Journal of Integer Sequences 29 (2026), Article 26.4.8, pp. 1–10,
  [Theorem 1 and Corollary 2](https://cs.uwaterloo.ca/journals/JIS/VOL29/Alzer/alzer22.pdf).
-/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.RamanujanHarmonicIdentityWanted

/-- **Shifted binomial–harmonic convolution (Alzer–Kwong, Corollary 2).** For natural numbers $k$
and $n$ with $2 \le k \le n$,
$$
\sum_{\nu=1}^{n+1} \Bigl(\binom{n+k-\nu-1}{n} - \binom{n+k-\nu-1}{k-2}\Bigr) H_\nu =
\binom{n+k}{k-1} (H_k - H_{n+1}) - \frac{1}{n+1} \binom{n+k}{k},
$$
where $H_m = \sum_{j=1}^{m} 1/j$ is the $m$-th harmonic number.

Source: Horst Alzer and Man Kam Kwong, "Ramanujan and a
Combinatorial Identity Involving Harmonic Numbers",
Corollary 2. -/
public theorem sum_choose_sub_choose_mul_harmonic_succ_eq
    (k n : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    ∑ ν ∈ Finset.Icc 1 (n + 1),
        ((Nat.choose (n + k - ν - 1) n : ℚ) -
          (Nat.choose (n + k - ν - 1) (k - 2) : ℚ)) * harmonic ν =
      (Nat.choose (n + k) (k - 1) : ℚ) *
          (harmonic k - harmonic (n + 1)) -
        (1 / ((n : ℚ) + 1)) * (Nat.choose (n + k) k : ℚ) := by
  have htop : (n + 1) + (k - 1) = n + k := by omega
  have hkpred : k - 1 + 1 = k := by omega
  have hconv := MetaMathlibExt.binomial_harmonic_convolution (k - 1) (n + 1)
    (by omega) (by omega)
  simp only [htop, Nat.add_sub_cancel, show k - 1 - 1 = k - 2 by omega] at hconv
  have hH : harmonic k = harmonic (k - 1) + 1 / (k : ℚ) := by
    simpa only [hkpred, one_div] using harmonic_succ (k - 1)
  have hchoose : Nat.choose (n + k) k * k = Nat.choose (n + k) (k - 1) * (n + 1) := by
    simpa only [hkpred, show n + k - (k - 1) = n + 1 by omega] using
      (Nat.choose_succ_right_eq (n + k) (k - 1))
  have hkQ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnQ : (n : ℚ) + 1 ≠ 0 := by positivity
  have hcorrection : (Nat.choose (n + k) (k - 1) : ℚ) / k =
      (Nat.choose (n + k) k : ℚ) / ((n : ℚ) + 1) := by
    apply (div_eq_div_iff hkQ hnQ).2
    exact_mod_cast hchoose.symm
  rw [hconv, hH]
  calc
    _ = (Nat.choose (n + k) (k - 1) : ℚ) * (harmonic (k - 1) - harmonic (n + 1)) +
          ((Nat.choose (n + k) (k - 1) : ℚ) / k -
            (Nat.choose (n + k) k : ℚ) / ((n : ℚ) + 1)) := by rw [hcorrection, sub_self, add_zero]
    _ = _ := by ring

end MathlibExt.NumberTheory.RamanujanHarmonicIdentityWanted
