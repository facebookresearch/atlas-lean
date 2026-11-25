/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Set.Function
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Approximation by Lüroth convergents

The theorem `MetaMathlibExt.lurothConvergent_lt_le` bounds the positive error of each
Lüroth convergent in terms of its last digit and denominator.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **First Lüroth digit.** For a real number $x$, the first Lüroth digit of $x$ is the natural
number $d_1(x) = \lfloor 1/x \rfloor + 1$, where $\lfloor \cdot \rfloor$ is the floor truncated
at $0$ and $1/0 = 0$. For $x \in (0, 1]$ this is the usual digit and is at least $2$; for
$x \le 0$ and for $x > 1$ it equals $1$.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Section 2. -/
noncomputable def lurothDigit (x : ℝ) : ℕ :=
  ⌊1 / x⌋₊ + 1

/-- **Lüroth map.** For a real number $x$ with first Lüroth digit $d = d_1(x)$, the Lüroth
map is $L(x) = d(d - 1)x - (d - 1)$.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Section 2. -/
noncomputable def lurothMap (x : ℝ) : ℝ :=
  (lurothDigit x : ℝ) * ((lurothDigit x : ℝ) - 1) * x - ((lurothDigit x : ℝ) - 1)

/-- **Lüroth digits.** For a real number $x$ and $n \ge 1$, the $n$-th Lüroth digit of $x$ is
$d_n(x) = d_1(L^{n-1}(x))$, where $d_1$ is the first Lüroth digit, $L$ is the Lüroth map and
$L^{n-1}$ is its $(n-1)$-fold iterate ($L^0$ is the identity).

The digit sequence is indexed from $0$: its term of index $k$ is $d_1(L^k(x)) = d_{k+1}(x)$.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Section 2. -/
noncomputable def lurothDigitSeq (x : ℝ) (k : ℕ) : ℕ :=
  lurothDigit (lurothMap^[k] x)

/-- **Lüroth denominators.** For a sequence of natural numbers $d_0, d_1, d_2, \dots$ (numbered from
$0$), the $n$-th Lüroth denominator is
$$Q_n = d_n \prod_{j=0}^{n-1} d_j (d_j - 1), \qquad n \ge 0.$$
With digits numbered from $1$, as in the paper, this is the paper's $Q_{n+1}$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (8). -/
public def lurothDenominator (d : ℕ → ℕ) (n : ℕ) : ℕ :=
  d n * ∏ j ∈ Finset.range n, d j * (d j - 1)

/-- **Lüroth convergents.** For a sequence of natural numbers $d_0, d_1, d_2, \dots$ (numbered from
$0$) with Lüroth denominators $Q_0, Q_1, Q_2, \dots$, the $n$-th Lüroth convergent is the rational
number
$$x_n = \sum_{k=0}^{n} \frac{1}{Q_k}, \qquad n \ge 0,$$
where a term with $Q_k = 0$ is read as $0$. With digits numbered from $1$, as in the paper, this is
the paper's $x_{n+1} = P_{n+1}/Q_{n+1}$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Section 2. -/
public def lurothConvergent (d : ℕ → ℕ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), 1 / (lurothDenominator d k : ℚ)

namespace lurothConvergent_lt_le

private theorem digit_gt_one {y : ℝ} (hy : y ∈ Set.Ioc 0 1) : 1 < lurothDigit y :=
  Nat.lt_add_one_iff.mpr <| (Nat.one_le_floor_iff _).2 <|
    (le_div_iff₀ hy.1).2 (by simpa using hy.2)

private theorem mapsTo : Set.MapsTo lurothMap (Set.Ioc 0 1) (Set.Ioc 0 1) := by
  intro y hy
  let a : ℝ := ⌊1 / y⌋₊
  have ha : 0 < a := by
    exact Nat.cast_pos.mpr (Nat.succ_lt_succ_iff.mp (digit_gt_one hy))
  have hlo : a * y ≤ 1 := (le_div_iff₀ hy.1).1 (Nat.floor_le (one_div_nonneg.mpr hy.1.le))
  have hhi : 1 < (a + 1) * y := (div_lt_iff₀ hy.1).1 (Nat.lt_floor_add_one _)
  have hmap : lurothMap y = a * ((a + 1) * y - 1) := by
    simp [lurothMap, lurothDigit, a]
    ring
  rw [Set.mem_Ioc, hmap]
  refine ⟨mul_pos ha (sub_pos.mpr hhi), ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hlo (show 0 ≤ a + 1 by positivity)]

end lurothConvergent_lt_le

/-- **Lüroth convergents approximate from below.** Let $x \in (0, 1]$ have Lüroth digits
$d_0, d_1, d_2, \dots$ (numbered from $0$), Lüroth denominators $Q_0, Q_1, Q_2, \dots$ and Lüroth
convergents $x_0, x_1, x_2, \dots$. Then for every $n \ge 0$,
$$0 < x - x_n \le \frac{1}{(d_n - 1) Q_n}.$$
In the paper's numbering from $1$ these are $d_{n+1}$, $Q_{n+1}$ and $x_{n+1} = P_{n+1}/Q_{n+1}$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Proposition 1. -/
public theorem lurothConvergent_lt_le (x : ℝ) (hx : x ∈ Set.Ioc 0 1) (n : ℕ) :
    0 < x - lurothConvergent (lurothDigitSeq x) n ∧
      x - lurothConvergent (lurothDigitSeq x) n ≤
        1 / (((lurothDigitSeq x n : ℝ) - 1) * lurothDenominator (lurothDigitSeq x) n) := by
  let d := lurothDigitSeq x
  let u (k : ℕ) := lurothMap^[k] x
  have hu (k : ℕ) : u k ∈ Set.Ioc 0 1 := lurothConvergent_lt_le.mapsTo.iterate k hx
  have hd (k : ℕ) : 1 < d k := lurothConvergent_lt_le.digit_gt_one (hu k)
  have hd' (k : ℕ) : (1 : ℝ) < d k := by exact_mod_cast hd k
  let p (k : ℕ) : ℝ := ∏ j ∈ Finset.range k, (d j : ℝ) * (d j - 1 : ℝ)
  have hp (k : ℕ) : 0 < p k :=
    Finset.prod_pos fun j _ => mul_pos (zero_lt_one.trans (hd' j)) (sub_pos.mpr (hd' j))
  have hq (k : ℕ) : (lurothDenominator d k : ℝ) = d k * p k := by
    have hcast (j : ℕ) : ((d j - 1 : ℕ) : ℝ) = d j - 1 := by
      rw [Nat.cast_sub (hd j).le, Nat.cast_one]
    simp [lurothDenominator, p, Nat.cast_prod, hcast]
  have hp_succ (k : ℕ) : p (k + 1) = p k * (d k * (d k - 1 : ℝ)) :=
    Finset.prod_range_succ _ _
  -- Each summand is the difference between two successive scaled iterates.
  have hstep (k : ℕ) : 1 / (lurothDenominator d k : ℝ) = u k / p k - u (k + 1) / p (k + 1) := by
    have hu_succ : u (k + 1) = (d k : ℝ) * (d k - 1 : ℝ) * u k - (d k - 1 : ℝ) :=
      Function.iterate_succ_apply' lurothMap k x
    rw [hq, hu_succ, hp_succ]
    field_simp [(hp k).ne', (zero_lt_one.trans (hd' k)).ne', (sub_pos.mpr (hd' k)).ne']
    ring
  have hrem : x - lurothConvergent d n = u (n + 1) / p (n + 1) := by
    simp only [lurothConvergent, Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
      hstep, Finset.sum_range_sub' (fun k => u k / p k)]
    simp [u, p]
  have hscale : ((d n : ℝ) - 1) * lurothDenominator d n = p (n + 1) := by
    rw [hp_succ, hq]
    ring
  change 0 < x - lurothConvergent d n ∧ x - lurothConvergent d n ≤ _
  rw [hrem, hscale]
  exact ⟨div_pos (hu _).1 (hp _), div_le_div_of_nonneg_right (hu _).2 (hp _).le⟩

end

end MetaMathlibExt
