/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Real.GoldenRatio
import MathlibExt.NumberTheory.FibonacciDivGoldenRatio
import Mathlib.Tactic.LinearCombination

/-!
# Differences of fractional parts of multiples of the golden ratio

Let $F_n$ be the $n$-th Fibonacci number, $\varphi = (1 + \sqrt{5})/2$ the golden ratio and
$\{y\} = y - \lfloor y \rfloor$ the fractional part. This file proves Wesley's lemma
`fract_goldenRatio_differences`: for $i \ge 1$ and $g_i = F_{3i}/2$, if
$\lfloor m_1\varphi \rfloor$ and $\lfloor m_2\varphi \rfloor$ are about $g_i/2$ apart, in one of
three precise ways, then $\{m_2\varphi\} - \{m_1\varphi\}$ is at most
$(\varphi^{-3i+1} - \varphi)/4 < -0.38$, less than $(3\varphi - 6)/4 < -0.28$, or less than
$(-5\varphi + 6)/4 < -0.52$.

## Implementation notes

Put $n = 3i$, $d = m_2 - m_1$ and $D = \lfloor m_2\varphi \rfloor - \lfloor m_1\varphi \rfloor$,
so that $\{m_2\varphi\} - \{m_1\varphi\} = d\varphi - D$ lies in $(-1, 1)$. In the three cases
$4D = F_n + c$ with $c = 0$, $6$ and $-6$. Wesley's identity
$F_n/\varphi - F_{n-1} = (-1)^{n+1}\varphi^{-n}$ (`fib_div_goldenRatio_sub_fib`) gives
$$4(\{m_2\varphi\} - \{m_1\varphi\}) = k\varphi - (-1)^{n+1}\varphi^{-n+1} - c, \qquad
k = 4d - F_{n-1}.$$
Since $F_{3i-1} \equiv 1 \pmod 4$, the integer $k$ is $3$ modulo $4$, and the bound
$d\varphi - D < 1$ gives $k \le -1$, $k \le 3$ and $k \le -5$ in the three cases. The parity of
$g_i$ is that of $i$, because $F_{3i} \equiv 0 \pmod 4$ for even $i$ and $F_{3i} \equiv 2 \pmod 4$
for odd $i$.

In case (i) the bound $d\varphi - D > -1$ also gives $k \ge -1$, so the inequality is an equality
whenever its hypotheses hold; this is why it reads $\le$ where the source prints $<$. The
hypothesis $i > 1$ of case (iii) is the source's; the proof does not use it.

## References

* William J. Wesley, *Improved Ramsey-type theorems for Fibonacci numbers and other sequences*,
  INTEGERS 25 (2025), Article A29; preprint arXiv:2211.05167, Lemma 8 and its proof.
-/

namespace MetaMathlibExt

namespace fract_goldenRatio_differences

/-- The Fibonacci numbers are periodic modulo `4` with period `6`. -/
private lemma fib_mod_four (n : ℕ) : Nat.fib n % 4 = Nat.fib (n % 6) % 4 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 6 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      have h6 : Nat.fib (m + 6) = Nat.fib m * 5 + Nat.fib (m + 1) * 8 := by
        rw [show m + 6 = m + 5 + 1 from rfl, Nat.fib_add]; rfl
      rw [h6, Nat.add_mod_right, ← ih m (by omega)]
      omega

/-- `F (3 i - 1) ≡ 1 (mod 4)` for every `i ≥ 1`. -/
private lemma fib_three_mul_sub_one_mod_four {i : ℕ} (hi : 1 ≤ i) :
    Nat.fib (3 * i - 1) % 4 = 1 := by
  rw [fib_mod_four]
  rcases (by omega : (3 * i - 1) % 6 = 2 ∨ (3 * i - 1) % 6 = 5) with h | h <;> rw [h] <;> rfl

/-- `F (3 i) ≡ 0 (mod 4)` for even `i` and `F (3 i) ≡ 2 (mod 4)` for odd `i`. -/
private lemma fib_three_mul_mod_four (i : ℕ) :
    (i % 2 = 0 ∧ Nat.fib (3 * i) % 4 = 0) ∨ (i % 2 = 1 ∧ Nat.fib (3 * i) % 4 = 2) := by
  rw [fib_mod_four]
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · exact Or.inl ⟨h, by rw [show 3 * i % 6 = 0 by omega]; rfl⟩
  · exact Or.inr ⟨h, by rw [show 3 * i % 6 = 3 by omega]; rfl⟩

/-- `1.618 < φ < 1.6181`. -/
private lemma goldenRatio_bounds : 1.618 < Real.goldenRatio ∧ Real.goldenRatio < 1.6181 := by
  have hsq : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5 : (0 : ℝ) ≤ √5 := Real.sqrt_nonneg 5
  constructor <;> simp only [Real.goldenRatio] <;> nlinarith

/-- `φ ^ (-2) = 2 - φ`. -/
private lemma goldenRatio_zpow_neg_two : Real.goldenRatio ^ (-2 : ℤ) = 2 - Real.goldenRatio := by
  rw [zpow_neg, zpow_ofNat]
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  linear_combination (1 - Real.goldenRatio) * Real.goldenRatio_sq

/-- `φ ^ (-5) = 5 φ - 8`. -/
private lemma goldenRatio_zpow_neg_five :
    Real.goldenRatio ^ (-5 : ℤ) = 5 * Real.goldenRatio - 8 := by
  rw [zpow_neg, zpow_ofNat]
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  linear_combination (5 * Real.goldenRatio ^ 4 - 3 * Real.goldenRatio ^ 3 +
    2 * Real.goldenRatio ^ 2 - Real.goldenRatio + 1) * Real.goldenRatio_sq

/-- The core computation. If `4 (⌊m₂ φ⌋ - ⌊m₁ φ⌋) = F (3 i) + c`, then
`4 ({m₂ φ} - {m₁ φ}) = k φ - (-1) ^ (3 i + 1) φ ^ (-3 i + 1) - c` for an integer `k ≡ 3 (mod 4)`,
namely `k = 4 (m₂ - m₁) - F (3 i - 1)`. -/
private lemma four_mul_fract_sub {i : ℕ} (hi : 1 ≤ i) (m₁ m₂ c : ℤ)
    (h : 4 * (⌊m₂ * Real.goldenRatio⌋ - ⌊m₁ * Real.goldenRatio⌋) = Nat.fib (3 * i) + c) :
    ∃ k : ℤ, k % 4 = 3 ∧
      4 * (Int.fract (m₂ * Real.goldenRatio) - Int.fract (m₁ * Real.goldenRatio)) =
        k * Real.goldenRatio -
          (-1) ^ (3 * i + 1) * Real.goldenRatio ^ (-(3 * i : ℤ) + 1) - c := by
  refine ⟨4 * (m₂ - m₁) - Nat.fib (3 * i - 1), ?_, ?_⟩
  · have := fib_three_mul_sub_one_mod_four hi
    omega
  · have hfib := fib_div_goldenRatio_sub_fib (3 * i) (by omega)
    push_cast at hfib
    have hφ := Real.goldenRatio_ne_zero
    have hz : Real.goldenRatio ^ (-(3 * i : ℤ) + 1) =
        Real.goldenRatio ^ (-(3 * i : ℤ)) * Real.goldenRatio :=
      zpow_add_one₀ hφ _
    have hR : (4 : ℝ) * (⌊m₂ * Real.goldenRatio⌋ - ⌊m₁ * Real.goldenRatio⌋) =
        Nat.fib (3 * i) + c := by
      exact_mod_cast h
    rw [Int.fract, Int.fract, hz]
    push_cast
    linear_combination (-1 : ℝ) * hR - Real.goldenRatio * hfib +
      (Nat.fib (3 * i) : ℝ) * mul_inv_cancel₀ hφ

end fract_goldenRatio_differences

open fract_goldenRatio_differences in
/-- **Differences of fractional parts of multiples of the golden ratio.** Let $F_m$ be the $m$-th
Fibonacci number, with $F_0 = 0$ and $F_1 = 1$, let $\varphi = (1 + \sqrt{5})/2$ be the golden
ratio, and write $\{y\} = y - \lfloor y \rfloor$ for the fractional part. Let $i \ge 1$ be a
natural number, put $g_i = F_{3i}/2$ (an integer, since $F_{3i}$ is even), and let
$x_1, x_2, m_1, m_2$ be integers. Then:
(i) if $g_i$ is even, $2(x_2 - x_1) = g_i$, $x_1 = \lfloor m_1\varphi \rfloor$ and
$x_2 = \lfloor m_2\varphi \rfloor$, then
$\{m_2\varphi\} - \{m_1\varphi\} \le (\varphi^{-3i+1} - \varphi)/4 < -0.38$;
(ii) if $g_i$ is odd, $2(x_2 - x_1) = g_i + 1$, $x_1 = \lfloor m_1\varphi \rfloor$ and
$x_2 + 1 = \lfloor m_2\varphi \rfloor$, then
$\{m_2\varphi\} - \{m_1\varphi\} < (3\varphi - 6)/4 < -0.28$;
(iii) if $g_i$ is odd, $i > 1$, $2(x_2 - x_1) = g_i - 1$, $x_1 + 1 = \lfloor m_1\varphi \rfloor$
and $x_2 = \lfloor m_2\varphi \rfloor$, then
$\{m_2\varphi\} - \{m_1\varphi\} < (-5\varphi + 6)/4 < -0.52$.

The paper states (i) with a strict inequality, but equality occurs: $i = 2$, $m_1 = 1$, $m_2 = 2$,
$x_1 = 1$, $x_2 = 3$ give $\{2\varphi\} - \{\varphi\} = (\varphi^{-5} - \varphi)/4$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Lemma 4 (`integers-2025-A29-lem-4`). -/
public theorem fract_goldenRatio_differences (i : ℕ) (hi : 1 ≤ i) (x₁ x₂ m₁ m₂ : ℤ) :
    (Even (Nat.fib (3 * i) / 2) → 2 * (x₂ - x₁) = (Nat.fib (3 * i) / 2 : ℕ) →
      x₁ = ⌊m₁ * Real.goldenRatio⌋ → x₂ = ⌊m₂ * Real.goldenRatio⌋ →
      Int.fract (m₂ * Real.goldenRatio) - Int.fract (m₁ * Real.goldenRatio) ≤
        (Real.goldenRatio ^ (-(3 * i : ℤ) + 1) - Real.goldenRatio) / 4 ∧
      (Real.goldenRatio ^ (-(3 * i : ℤ) + 1) - Real.goldenRatio) / 4 < -0.38) ∧
    (Odd (Nat.fib (3 * i) / 2) → 2 * (x₂ - x₁) = (Nat.fib (3 * i) / 2 : ℕ) + 1 →
      x₁ = ⌊m₁ * Real.goldenRatio⌋ → x₂ + 1 = ⌊m₂ * Real.goldenRatio⌋ →
      Int.fract (m₂ * Real.goldenRatio) - Int.fract (m₁ * Real.goldenRatio) <
        (3 * Real.goldenRatio - 6) / 4 ∧ (3 * Real.goldenRatio - 6) / 4 < -0.28) ∧
    (Odd (Nat.fib (3 * i) / 2) → 1 < i → 2 * (x₂ - x₁) = (Nat.fib (3 * i) / 2 : ℕ) - 1 →
      x₁ + 1 = ⌊m₁ * Real.goldenRatio⌋ → x₂ = ⌊m₂ * Real.goldenRatio⌋ →
      Int.fract (m₂ * Real.goldenRatio) - Int.fract (m₁ * Real.goldenRatio) <
        (-5 * Real.goldenRatio + 6) / 4 ∧ (-5 * Real.goldenRatio + 6) / 4 < -0.52) := by
  obtain ⟨hφ₁, hφ₂⟩ := goldenRatio_bounds
  have hφ := Real.goldenRatio_pos
  -- `e = φ ^ (-3 i + 1)` satisfies `0 < e ≤ φ ^ (-2) = 2 - φ`.
  have he₀ : 0 < Real.goldenRatio ^ (-(3 * i : ℤ) + 1) := zpow_pos hφ _
  have he₂ : Real.goldenRatio ^ (-(3 * i : ℤ) + 1) ≤ 2 - Real.goldenRatio := by
    rw [← goldenRatio_zpow_neg_two]
    exact zpow_le_zpow_right₀ Real.one_lt_goldenRatio.le (by omega)
  -- The difference of two fractional parts is less than `1`.
  have hfr : Int.fract (m₂ * Real.goldenRatio) - Int.fract (m₁ * Real.goldenRatio) < 1 := by
    linarith [Int.fract_lt_one (m₂ * Real.goldenRatio), Int.fract_nonneg (m₁ * Real.goldenRatio)]
  have hmod := fib_three_mul_mod_four i
  refine ⟨fun hev h2 h3 h4 => ?_, fun hodd h2 h3 h4 => ?_, fun hodd _ h2 h3 h4 => ?_⟩
  · -- (i): `i` is even and `k ≤ -1`.
    rw [Nat.even_iff] at hev
    have hi' : i % 2 = 0 ∧ Nat.fib (3 * i) % 4 = 0 := by omega
    obtain ⟨k, hk, hfd⟩ := four_mul_fract_sub hi m₁ m₂ 0 (by rw [← h3, ← h4]; omega)
    rw [Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))] at hfd
    push_cast at hfd
    have hk₂ : k ≤ 2 := by
      by_contra hk'
      have := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (by omega : 3 ≤ k) : (3 : ℝ) ≤ k) hφ.le
      linarith
    have hk₁ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (by omega : k ≤ -1) : (k : ℝ) ≤ -1) hφ.le
    have he₅ : Real.goldenRatio ^ (-(3 * i : ℤ) + 1) ≤ 5 * Real.goldenRatio - 8 := by
      rw [← goldenRatio_zpow_neg_five]
      exact zpow_le_zpow_right₀ Real.one_lt_goldenRatio.le (by omega)
    constructor
    · linarith
    · norm_num
      linarith
  · -- (ii): `i` is odd, `k ≤ 3`.
    rw [Nat.odd_iff] at hodd
    have hi' : i % 2 = 1 ∧ Nat.fib (3 * i) % 4 = 2 := by omega
    obtain ⟨k, hk, hfd⟩ := four_mul_fract_sub hi m₁ m₂ 6 (by rw [← h3, ← h4]; omega)
    rw [Even.neg_one_pow (Nat.even_iff.mpr (by omega))] at hfd
    push_cast at hfd
    have hk₆ : k ≤ 6 := by
      by_contra hk'
      have := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (by omega : 7 ≤ k) : (7 : ℝ) ≤ k) hφ.le
      linarith
    have hk₃ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (by omega : k ≤ 3) : (k : ℝ) ≤ 3) hφ.le
    constructor
    · linarith
    · norm_num
      linarith
  · -- (iii): `i` is odd, `k ≤ -5`.
    rw [Nat.odd_iff] at hodd
    have hi' : i % 2 = 1 ∧ Nat.fib (3 * i) % 4 = 2 := by omega
    obtain ⟨k, hk, hfd⟩ := four_mul_fract_sub hi m₁ m₂ (-6) (by rw [← h3, ← h4]; omega)
    rw [Even.neg_one_pow (Nat.even_iff.mpr (by omega))] at hfd
    push_cast at hfd
    have hk₂ : k ≤ -2 := by
      by_contra hk'
      have := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (by omega : -1 ≤ k) : (-1 : ℝ) ≤ k) hφ.le
      linarith
    have hk₅ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (by omega : k ≤ -5) : (k : ℝ) ≤ -5) hφ.le
    constructor
    · linarith
    · norm_num
      linarith

end MetaMathlibExt
