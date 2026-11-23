/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.AlternatingBinomialPowerSum

/-!
# Recurrences for alternating binomial power sums

Pascal's identity expresses an increase in binomial order as a difference in the shift
parameter. The binomial theorem then expands the shifted sum in lower powers.
-/

namespace MetaMathlibExt

open Finset

@[expose] public section

/-- **Alternating binomial power sum.** For natural numbers $\ell, m$ and complex numbers $x, y$,
$$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (kx + y)^\ell,$$
with the convention $0^0 = 1$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Section 3, Equation (3.9). -/
public def alternatingBinomialPowerSum (ℓ m : ℕ) (x y : ℂ) : ℂ :=
  ∑ k ∈ range (m + 1), (-1) ^ k * (m.choose k : ℂ) * (k * x + y) ^ ℓ

/-- **A value of the alternating binomial power sum.** The alternating binomial power sum
$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (kx + y)^\ell$ satisfies
$p_{1,1}(1, 1) = 1 - 2 = -1$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Section 3, Equation (3.9). -/
public theorem alternatingBinomialPowerSum_one_one_one_one :
    alternatingBinomialPowerSum 1 1 1 1 = -1 := by
  simp [alternatingBinomialPowerSum, sum_range_succ]

end

namespace alternatingBinomialPowerSum_recurrences

private theorem order_succ (ℓ m : ℕ) (x y : ℂ) :
    alternatingBinomialPowerSum ℓ (m + 1) x y =
      alternatingBinomialPowerSum ℓ m x y - alternatingBinomialPowerSum ℓ m x (x + y) := by
  simpa only [alternatingBinomialPowerSum, Nat.cast_succ, pow_succ (-1 : ℂ), mul_neg_one,
    add_mul, one_mul, add_assoc, mul_neg, neg_mul, sum_neg_distrib, sub_eq_add_neg,
    mul_left_comm, mul_assoc] using
    sum_choose_succ_mul (fun k _ => (-1 : ℂ) ^ k * (k * x + y) ^ ℓ) m

-- Apply the shift difference to the product of the last linear factor and the lower power.
private theorem degree_succ (ℓ m : ℕ) (x y : ℂ) :
    alternatingBinomialPowerSum (ℓ + 1) (m + 1) x y =
      y * alternatingBinomialPowerSum ℓ (m + 1) x y -
        (m + 1) * x * alternatingBinomialPowerSum ℓ m x (x + y) := by
  induction m generalizing y with
  | zero =>
    rw [order_succ, order_succ]
    simp [alternatingBinomialPowerSum, pow_succ]
    ring
  | succ m ih =>
    rw [order_succ (ℓ + 1), ih, ih, order_succ ℓ (m + 1), order_succ ℓ m x (x + y)]
    push_cast
    ring

private theorem zero_of_lt {ℓ m : ℕ} (h : ℓ < m) (x y : ℂ) :
    alternatingBinomialPowerSum ℓ m x y = 0 := by
  cases ℓ with
  | zero =>
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
    rw [order_succ]
    simp [alternatingBinomialPowerSum]
  | succ ℓ =>
    simpa [alternatingBinomialPowerSum, add_comm y] using
      (sum_neg_one_pow_choose_mul_pow y x 1 (by omega) (Nat.succ_pos ℓ)).2 h

private theorem shift (ℓ m : ℕ) (x y : ℂ) :
    alternatingBinomialPowerSum ℓ m x (x + y) =
      ∑ j ∈ Icc m ℓ, (ℓ.choose j : ℂ) * alternatingBinomialPowerSum j m x y * x ^ (ℓ - j) := by
  calc
    _ = ∑ j ∈ range (ℓ + 1),
        (ℓ.choose j : ℂ) * alternatingBinomialPowerSum j m x y * x ^ (ℓ - j) := by
      unfold alternatingBinomialPowerSum
      have expand (k : ℕ) := add_pow ((k : ℂ) * x + y) x ℓ
      simp_rw [add_comm x y, ← add_assoc, expand, mul_sum, sum_mul]
      rw [sum_comm]
      refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
      ring
    _ = _ := by
      symm
      apply sum_subset
      · intro j hj
        exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hj).2)
      · intro j hj hnot
        have hjm : j < m := by
          simp only [mem_Icc, mem_range] at *
          omega
        simp [zero_of_lt hjm]

private theorem derivative (ℓ m : ℕ) (x y : ℂ) :
    deriv (fun z => alternatingBinomialPowerSum ℓ m x z) y =
      ℓ * alternatingBinomialPowerSum (ℓ - 1) m x y := by
  unfold alternatingBinomialPowerSum
  rw [mul_sum]
  apply HasDerivAt.deriv
  apply HasDerivAt.fun_sum
  intro k _
  simpa only [id_eq, mul_one, mul_left_comm] using
    ((((hasDerivAt_id y).const_add ((k : ℂ) * x)).fun_pow ℓ).const_mul
      ((-1 : ℂ) ^ k * (m.choose k : ℂ)))

end alternatingBinomialPowerSum_recurrences

open alternatingBinomialPowerSum_recurrences in
/-- **Recurrences for alternating binomial power sums.** Let
$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (kx + y)^\ell$. For all complex numbers
$x, y$ and natural numbers $\ell, m$ (sums over an empty range are $0$, and $m - 1$ means $0$ when
$m = 0$):
(i) $p_{\ell,m+1}(x, y) = p_{\ell,m}(x, y) - p_{\ell,m}(x, x + y)$;
(ii) $p_{\ell,m}(x, x + y) = \sum_{j=m}^{\ell} \binom{\ell}{j} p_{j,m}(x, y)\, x^{\ell-j}$;
(iii) $p_{\ell,m+1}(x, y) = -\sum_{j=m}^{\ell-1} \binom{\ell}{j} p_{j,m}(x, y)\, x^{\ell-j}$;
(iv) $p_{\ell+1,m}(x, y) = y\, p_{\ell,m}(x, y) - m x\, p_{\ell,m-1}(x, x + y)$;
(v) $p_{\ell+1,m+1}(x, y) = ((m + 1) x + y)\, p_{\ell,m+1}(x, y) -
(m + 1) x\, p_{\ell,m}(x, y)$;
(vi) if $\ell \ge 1$, the complex derivative of $z \mapsto p_{\ell,m}(x, z)$ at $z = y$ is
$\ell\, p_{\ell-1,m}(x, y)$;
(vii) if $\ell \ge 1$, then
$p_{\ell,m}(x, y) = (m x + y)\, p_{\ell-1,m}(x, y) - m x\, p_{\ell-1,m-1}(x, y)$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Proposition 4 (`integers-2024-A70-prop-4`). -/
public theorem alternatingBinomialPowerSum_recurrences (x y : ℂ) (ℓ m : ℕ) :
    alternatingBinomialPowerSum ℓ (m + 1) x y =
        alternatingBinomialPowerSum ℓ m x y - alternatingBinomialPowerSum ℓ m x (x + y) ∧
      alternatingBinomialPowerSum ℓ m x (x + y) =
        ∑ j ∈ Icc m ℓ, (ℓ.choose j : ℂ) * alternatingBinomialPowerSum j m x y * x ^ (ℓ - j) ∧
      alternatingBinomialPowerSum ℓ (m + 1) x y =
        -∑ j ∈ Ico m ℓ, (ℓ.choose j : ℂ) * alternatingBinomialPowerSum j m x y * x ^ (ℓ - j) ∧
      alternatingBinomialPowerSum (ℓ + 1) m x y =
        y * alternatingBinomialPowerSum ℓ m x y -
          m * x * alternatingBinomialPowerSum ℓ (m - 1) x (x + y) ∧
      alternatingBinomialPowerSum (ℓ + 1) (m + 1) x y =
        ((m + 1) * x + y) * alternatingBinomialPowerSum ℓ (m + 1) x y -
          (m + 1) * x * alternatingBinomialPowerSum ℓ m x y ∧
      (1 ≤ ℓ → deriv (fun z => alternatingBinomialPowerSum ℓ m x z) y =
        ℓ * alternatingBinomialPowerSum (ℓ - 1) m x y) ∧
      (1 ≤ ℓ → alternatingBinomialPowerSum ℓ m x y =
        (m * x + y) * alternatingBinomialPowerSum (ℓ - 1) m x y -
          m * x * alternatingBinomialPowerSum (ℓ - 1) (m - 1) x y) := by
  have horder := order_succ ℓ m x y
  have hshift := shift ℓ m x y
  have hdegree (d n : ℕ) :
      alternatingBinomialPowerSum (d + 1) (n + 1) x y =
        ((n + 1) * x + y) * alternatingBinomialPowerSum d (n + 1) x y -
          (n + 1) * x * alternatingBinomialPowerSum d n x y := by
    rw [degree_succ, order_succ d n]
    ring
  refine ⟨horder, hshift, ?_, ?_, hdegree ℓ m, fun _ => derivative ℓ m x y, ?_⟩
  · by_cases h : m ≤ ℓ
    · rw [horder, hshift, ← sum_Ico_add_eq_sum_Icc h]
      simp
    · simp [Ico_eq_empty_of_le (by omega : ℓ ≤ m), zero_of_lt (by omega : ℓ < m + 1)]
  · cases m with
    | zero => simp [alternatingBinomialPowerSum, pow_succ, mul_comm]
    | succ m => simpa using degree_succ ℓ m x y
  · intro h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ℓ ≠ 0)
    cases m with
    | zero => simp [alternatingBinomialPowerSum, pow_succ, mul_comm]
    | succ m => simpa using hdegree k m

end MetaMathlibExt
