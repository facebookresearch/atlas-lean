/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import MathlibExt.Combinatorics.Enumerative.AlternatingBinomialPowerSumRecurrences
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.StirlingSecondExplicit

/-!
# Alternating binomial power sums via Stirling numbers of the second kind

The main result, `alternatingBinomialPowerSum_eq_sum_stirlingSecond`, is Boyadzhiev's expansion
of the alternating binomial power sum
$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (kx + y)^\ell$ in Stirling numbers of the
second kind, together with Katsuura's formulas: $p_{\ell,m}(x, y) = 0$ for $\ell < m$, and
$p_{m,m}(x, y) = (-1)^m x^m m!$ on the diagonal.

The binomial theorem expands each power $(kx + y)^\ell$, and the explicit formula
$\sum_{k=0}^{m} (-1)^{m-k} \binom{m}{k} k^j = m!\, S(j, m)$ evaluates the resulting inner sums.

For the special values, the order recurrence reduces $p_{\ell,m}(x, x)$ to values at $y = 0$.
Reflecting the index in $p_{\ell,m}(-1, m)$ gives the explicit Stirling sum without a global sign.

## References

* Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
  INTEGERS 24 (2024), Article A70, pp. 1–31, Propositions 2 (i)–(iv) and 4 (i).
* Ronald L. Graham, Donald E. Knuth, and Oren Patashnik, *Concrete Mathematics: A Foundation
  for Computer Science*, Addison-Wesley (1989), p. 163 and Identity (6.19).
* Khristo N. Boyadzhiev, *Close Encounters with the Stirling Numbers of the Second Kind*,
  Mathematics Magazine 85 (2012), no. 4, pp. 252–266, p. 253.
* Jocelyn Quaintance and Henry W. Gould, *Combinatorial Identities for Stirling Numbers*,
  World Scientific (2015), Identity (9.21).
-/

namespace MetaMathlibExt

open Finset

namespace alternatingBinomialPowerSum_eq_sum_stirlingSecond

-- The explicit formula `∑_{k=0}^{m} (-1)^k C(m, k) k^j = (-1)^m m! S(j, m)` over `ℂ`,
-- transferred from `stirlingSecond_mul_factorial_eq_sum` over `ℝ`.
private theorem sum_neg_one_pow_choose_mul_pow (j m : ℕ) :
    ∑ k ∈ range (m + 1), (-1 : ℂ) ^ k * (m.choose k : ℂ) * (k : ℂ) ^ j =
      (-1) ^ m * (m.factorial : ℂ) * (Nat.stirlingSecond j m : ℂ) := by
  have h := congrArg Complex.ofReal (stirlingSecond_mul_factorial_eq_sum j m)
  push_cast at h
  rw [mul_assoc, mul_comm (m.factorial : ℂ), h, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hkm : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hsign : (-1 : ℂ) ^ k = (-1) ^ m * (-1) ^ (m - k) := by
    rw [← pow_add]
    apply neg_one_pow_congr
    simp only [Nat.even_iff]
    omega
  rw [hsign]
  ring

end alternatingBinomialPowerSum_eq_sum_stirlingSecond

open alternatingBinomialPowerSum_eq_sum_stirlingSecond in
/-- **Boyadzhiev's and Katsuura's formulas for alternating binomial power sums.** Let
$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (kx + y)^\ell$ and let $S(j, m)$ denote the
Stirling numbers of the second kind. For all complex numbers $x, y$ and natural numbers
$\ell, m$:
(i) (Boyadzhiev) $p_{\ell,m}(x, y) = \sum_{j=m}^{\ell} \binom{\ell}{j} (-1)^m m!\, S(j, m)\,
x^j y^{\ell-j}$, where the sum is empty (hence $0$) when $\ell < m$;
(ii) (Katsuura) if $\ell < m$ then $p_{\ell,m}(x, y) = 0$, and $p_{m,m}(x, y) = (-1)^m x^m m!$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Proposition 1 (`integers-2024-A70-prop-1`). -/
public theorem alternatingBinomialPowerSum_eq_sum_stirlingSecond (x y : ℂ) (ℓ m : ℕ) :
    alternatingBinomialPowerSum ℓ m x y =
        ∑ j ∈ Icc m ℓ, (ℓ.choose j : ℂ) * (-1) ^ m * (m.factorial : ℂ) *
          (Nat.stirlingSecond j m : ℂ) * x ^ j * y ^ (ℓ - j) ∧
      (ℓ < m → alternatingBinomialPowerSum ℓ m x y = 0) ∧
      alternatingBinomialPowerSum m m x y = (-1) ^ m * x ^ m * (m.factorial : ℂ) := by
  -- Expand each power binomially and evaluate the inner alternating sums; the terms with
  -- `j < m` vanish because `S(j, m) = 0` there.
  have hmain (d : ℕ) : alternatingBinomialPowerSum d m x y =
      ∑ j ∈ Icc m d, (d.choose j : ℂ) * (-1) ^ m * (m.factorial : ℂ) *
        (Nat.stirlingSecond j m : ℂ) * x ^ j * y ^ (d - j) := by
    calc
      _ = ∑ j ∈ range (d + 1), (d.choose j : ℂ) * (-1) ^ m * (m.factorial : ℂ) *
            (Nat.stirlingSecond j m : ℂ) * x ^ j * y ^ (d - j) := by
        unfold alternatingBinomialPowerSum
        simp_rw [add_pow, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun j _ => ?_
        rw [mul_assoc (d.choose j : ℂ), mul_assoc (d.choose j : ℂ),
          ← sum_neg_one_pow_choose_mul_pow j m]
        simp only [mul_sum, sum_mul]
        refine sum_congr rfl fun k _ => ?_
        ring
      _ = _ := by
        symm
        apply sum_subset
        · intro j hj
          exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hj).2)
        · intro j hj hnot
          have hjm : j < m := by
            simp only [mem_Icc, mem_range, not_and, not_le] at hj hnot
            omega
          simp [Nat.stirlingSecond_eq_zero_of_lt hjm]
  refine ⟨hmain ℓ, fun h => ?_, ?_⟩
  · rw [hmain ℓ, Icc_eq_empty_of_lt h, sum_empty]
  · rw [hmain m, Icc_self, sum_singleton, Nat.choose_self, Nat.stirlingSecond_self,
      Nat.sub_self]
    push_cast
    ring

open alternatingBinomialPowerSum_eq_sum_stirlingSecond in
/-- **Special values of alternating binomial power sums.** Let
$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (kx + y)^\ell$, with $0^0 = 1$, and let
$S(j, m)$ denote the Stirling numbers of the second kind. For all complex numbers $x, y$ and
natural numbers $\ell, m$:
(i) $p_{\ell,m}(x, x) = (-1)^m m!\, S(\ell + 1, m + 1)\, x^\ell$, and in particular
$p_{\ell,m}(1, 1) = (-1)^m m!\, S(\ell + 1, m + 1)$;
(ii) $p_{\ell,m}(0, y) = 0^m y^\ell$;
(iii) $p_{\ell,m}(x, 0) = (-1)^m m!\, S(\ell, m)\, x^\ell$, and in particular
$p_{m+1,m}(1, 0) = (-1)^m m! \binom{m+1}{2}$;
(iv) $p_{\ell,m}(-1, m) = m!\, S(\ell, m)$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Proposition 2 (i)–(iv) (`integers-2024-A70-prop-2`). -/
public theorem alternatingBinomialPowerSum_special_values (x y : ℂ) (ℓ m : ℕ) :
    alternatingBinomialPowerSum ℓ m x x =
        (-1) ^ m * (m.factorial : ℂ) * (Nat.stirlingSecond (ℓ + 1) (m + 1) : ℂ) * x ^ ℓ ∧
      alternatingBinomialPowerSum ℓ m 1 1 =
        (-1) ^ m * (m.factorial : ℂ) * (Nat.stirlingSecond (ℓ + 1) (m + 1) : ℂ) ∧
      alternatingBinomialPowerSum ℓ m 0 y = 0 ^ m * y ^ ℓ ∧
      alternatingBinomialPowerSum ℓ m x 0 =
        (-1) ^ m * (m.factorial : ℂ) * (Nat.stirlingSecond ℓ m : ℂ) * x ^ ℓ ∧
      alternatingBinomialPowerSum (m + 1) m 1 0 =
        (-1) ^ m * (m.factorial : ℂ) * ((m + 1).choose 2 : ℂ) ∧
      alternatingBinomialPowerSum ℓ m (-1) m =
        (m.factorial : ℂ) * (Nat.stirlingSecond ℓ m : ℂ) := by
  -- Factoring with `mul_pow` also works when the degree or the base is zero.
  have haxis (z : ℂ) (d n : ℕ) : alternatingBinomialPowerSum d n z 0 =
      (-1) ^ n * (n.factorial : ℂ) * (Nat.stirlingSecond d n : ℂ) * z ^ d := by
    rw [← sum_neg_one_pow_choose_mul_pow d n, sum_mul]
    simp only [alternatingBinomialPowerSum, add_zero, mul_pow, mul_assoc]
  -- Subtract the next order at `y = 0` and apply the Stirling recurrence.
  have hdiag (z : ℂ) : alternatingBinomialPowerSum ℓ m z z =
      (-1) ^ m * (m.factorial : ℂ) * (Nat.stirlingSecond (ℓ + 1) (m + 1) : ℂ) * z ^ ℓ := by
    have h := (alternatingBinomialPowerSum_recurrences z 0 ℓ m).1
    rw [add_zero] at h
    calc
      _ = alternatingBinomialPowerSum ℓ m z 0 - alternatingBinomialPowerSum ℓ (m + 1) z 0 := by
        rw [h, sub_sub_cancel]
      _ = _ := by
        rw [haxis, haxis, Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_succ, pow_succ (-1 : ℂ) m]
        ring
  refine ⟨hdiag x, by simpa only [one_pow, mul_one] using hdiag 1, ?_, haxis x ℓ m, ?_, ?_⟩
  · -- The binomial theorem gives `0 ^ m`, including the value `1` at `m = 0`.
    have hchoose : ∑ k ∈ range (m + 1), (-1 : ℂ) ^ k * (m.choose k : ℂ) = 0 ^ m := by
      simpa using (add_pow (-1 : ℂ) 1 m).symm
    simp only [alternatingBinomialPowerSum, mul_zero, zero_add, ← sum_mul, hchoose]
  · simpa only [Nat.stirlingSecond_succ_self_left, one_pow, mul_one] using haxis 1 (m + 1) m
  · have h := congrArg Complex.ofReal (stirlingSecond_mul_factorial_eq_sum ℓ m)
    push_cast at h
    rw [mul_comm (m.factorial : ℂ), h, alternatingBinomialPowerSum, ← sum_range_reflect]
    refine sum_congr rfl fun k hk => ?_
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hbase : ((m - k : ℕ) : ℂ) * (-1) + m = k := by
      rw [Nat.cast_sub hkm]
      ring
    rw [Nat.add_sub_cancel, Nat.choose_symm hkm, hbase]

end MetaMathlibExt
