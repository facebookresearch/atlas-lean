/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The infinite Pascal matrix

Source: E. F. Cornelius Jr. and Phill Schultz, *Polynomial Points*:
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Schultz/schultz14.tex>.
-/

@[expose] public section

open scoped BigOperators Topology

namespace MetaMathlibExt

/-- **Entries of the infinite Pascal matrix.** For natural numbers $i$ and $j$, the entry of the
infinite Pascal matrix in row $i$ and column $j$ is the binomial coefficient $\binom{i}{j}$. -/
public def pascalEntry (i j : ℕ) : ℕ :=
  Nat.choose i j

/-- **Column generating functions of the Pascal matrix.** For a natural number $j$ and a real
number $x$, the column generating function of the infinite Pascal matrix is
$\alpha_j(x) = \sum_{i \ge 0} \binom{i}{j} x^i$, where $\binom{i}{j}$ is the entry in row $i$ and
column $j$; the sum is taken to be $0$ when the series is not summable.

Source: concept `jis_sem_0dfae529bb25056055d54002`, statement
`jis_0e7580a02d8343e6906a8ac6`. -/
public noncomputable def pascalAlpha (j : ℕ) (x : ℝ) : ℝ :=
  ∑' i, (pascalEntry i j : ℝ) * x ^ i

/-- Column `j` sums to `x^j / (1 - x)^(j+1)` for `‖x‖ < 1`. -/
private theorem colHas (j : ℕ) (x : ℝ) (hx : ‖x‖ < 1) :
    HasSum (fun i => (pascalEntry i j : ℝ) * x ^ i)
      (x ^ j / (1 - x) ^ (j + 1)) := by
  have hpre : ∑ i ∈ Finset.range j, (pascalEntry i j : ℝ) * x ^ i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      unfold pascalEntry
      rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hi), Nat.cast_zero, zero_mul]
  have hcongr : (fun m => (pascalEntry (m + j) j : ℝ) * x ^ (m + j))
      = fun m => x ^ j * ((((m + j).choose j : ℕ) : ℝ) * x ^ m) :=
    funext fun m => by unfold pascalEntry; rw [pow_add]; ring
  have hshift : HasSum (fun m => (pascalEntry (m + j) j : ℝ) * x ^ (m + j))
      (x ^ j * (1 / (1 - x) ^ (j + 1))) := by
    rw [hcongr]
    exact (hasSum_choose_mul_geometric_of_norm_lt_one j hx).mul_left _
  rw [div_eq_mul_one_div]
  simpa [hpre] using
    (hasSum_nat_add_iff (f := fun i => (pascalEntry i j : ℝ) * x ^ i) j).mp hshift

/-- **Closed form of the Pascal column generating functions.** For every natural number $j$ and
every real number $x$ with $|x| < 1$, the column generating function $\alpha_j$ of the infinite
Pascal matrix satisfies $\alpha_j(x) = x^j / (1 - x)^{j+1}$. -/
public theorem pascalAlpha_eq (j : ℕ) (x : ℝ) (hx : |x| < 1) :
    pascalAlpha j x = x ^ j / (1 - x) ^ (j + 1) := by
  unfold pascalAlpha
  exact (colHas j x (by rwa [Real.norm_eq_abs])).tsum_eq

/-- The Pascal-matrix terms are summable over `ℕ × ℕ` for `|x| < 1/2`. -/
private theorem masterSumm (x : ℝ) (hx : |x| < 1 / 2) :
    Summable (fun p : ℕ × ℕ => (pascalEntry p.1 p.2 : ℝ) * x ^ p.1) := by
  set c : ℝ := (1 + 2 * |x|) / 2 with hc
  have hxnonneg : 0 ≤ |x| := abs_nonneg x
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  have hc1 : c < 1 := by rw [hc]; linarith
  have h2xc : 2 * |x| ≤ c ^ 2 := by rw [hc]; nlinarith [hx, hxnonneg]
  have hsumc : Summable (fun i : ℕ => c ^ i) :=
    summable_geometric_of_norm_lt_one
      (by rw [Real.norm_eq_abs, abs_of_nonneg hc0]; exact hc1)
  have hnormsum : Summable (fun i : ℕ => ‖c ^ i‖) := by
    simpa [norm_pow, Real.norm_eq_abs, abs_of_nonneg hc0] using hsumc
  have hprod : Summable (fun p : ℕ × ℕ => c ^ p.1 * c ^ p.2) :=
    summable_mul_of_summable_norm hnormsum hnormsum
  have hle : ∀ p : ℕ × ℕ,
      ‖(pascalEntry p.1 p.2 : ℝ) * x ^ p.1‖ ≤ c ^ p.1 * c ^ p.2 := by
    intro ⟨i, j⟩
    change ‖(pascalEntry i j : ℝ) * x ^ i‖ ≤ c ^ i * c ^ j
    have hCnonneg : 0 ≤ ((Nat.choose i j : ℕ) : ℝ) := Nat.cast_nonneg _
    simp only [pascalEntry, norm_mul, norm_pow, Real.norm_eq_abs,
      abs_of_nonneg hCnonneg]
    by_cases hj : j ≤ i
    · have hC2 : ((Nat.choose i j : ℕ) : ℝ) ≤ (2 : ℝ) ^ i := by
        exact_mod_cast Nat.choose_le_two_pow _ _
      calc ((Nat.choose i j : ℕ) : ℝ) * |x| ^ i
          ≤ (2 * |x|) ^ i := by
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_right hC2 (pow_nonneg hxnonneg _)
        _ ≤ (c ^ 2) ^ i := pow_le_pow_left₀ (by positivity) h2xc _
        _ ≤ c ^ i * c ^ j := by
            rw [← pow_mul, show 2 * i = i + i by omega, pow_add]
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_of_le_one hc0 (le_of_lt hc1) hj) (pow_nonneg hc0 _)
    · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hj), Nat.cast_zero, zero_mul]
      exact mul_nonneg (pow_nonneg hc0 _) (pow_nonneg hc0 _)
  exact Summable.of_norm (Summable.of_nonneg_of_le (fun p => norm_nonneg _) hle hprod)

/-- **Summing the Pascal column generating functions.** For every real number $x$ with
$|x| < 1/2$, the sum $\sum_{j \ge 0} \alpha_j(x)$ of the column generating functions of the
infinite Pascal matrix equals $\sum_{j \ge 0} \sum_{i \ge 0} \binom{i}{j} x^i$, where
$\binom{i}{j}$ is the entry in row $i$ and column $j$, and it also equals
$\sum_{j \ge 0} x^j / (1 - x)^{j+1}$. -/
public theorem tsum_pascalAlpha_eq (x : ℝ) (hx : |x| < 1 / 2) :
    (∑' j, pascalAlpha j x) = (∑' j, ∑' i, (pascalEntry i j : ℝ) * x ^ i) ∧
      (∑' j, pascalAlpha j x) = ∑' j, x ^ j / (1 - x) ^ (j + 1) := by
  exact ⟨rfl, tsum_congr fun j => pascalAlpha_eq j x (by linarith)⟩

/-- Each row sums to `2 ^ i` over its finite support. -/
private theorem rowSum (i : ℕ) :
    (∑ j ∈ Finset.range (i + 1), (pascalEntry i j : ℝ)) = (2 : ℝ) ^ i := by
  unfold pascalEntry
  rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_two]

/-- Each row tsum over `j` equals `x ^ i * 2 ^ i`. -/
private theorem rowTsum (i : ℕ) (x : ℝ) :
    (∑' j, (pascalEntry i j : ℝ) * x ^ i) = x ^ i * 2 ^ i := by
  have hsupp : ∀ j ∉ Finset.range (i + 1), (pascalEntry i j : ℝ) * x ^ i = 0 :=
    fun j hj => by
      unfold pascalEntry
      rw [Nat.choose_eq_zero_of_lt (by rw [Finset.mem_range] at hj; omega),
        Nat.cast_zero, zero_mul]
  rw [(hasSum_sum_of_ne_finset_zero hsupp).tsum_eq, ← Finset.sum_mul, rowSum]; ring

/-- `|2 * x| < 1` for `|x| < 1 / 2`. -/
private theorem abs_two_mul_lt_one (x : ℝ) (hx : |x| < 1 / 2) :
    |2 * x| < 1 := by
  rw [abs_mul, abs_of_nonneg (by linarith)]; linarith

/-- `|x / (1 - x)| < 1` for `|x| < 1 / 2`. -/
private theorem abs_div_one_sub_lt_one (x : ℝ) (hx : |x| < 1 / 2) :
    |x / (1 - x)| < 1 := by
  have hb := abs_lt.mp hx
  have h1x : (0 : ℝ) < 1 - x := by linarith [hb.2]
  rw [abs_div, abs_of_pos h1x, div_lt_one h1x]; linarith [hx, hb.2]

/-- **Reversing the order of summation in the Pascal matrix.** For every real number $x$ with
$|x| < 1/2$, writing $\binom{i}{j}$ for the entry of the infinite Pascal matrix in row $i$ and
column $j$, we have
$\sum_{j \ge 0} \sum_{i \ge 0} \binom{i}{j} x^i = \sum_{i \ge 0} \sum_{j \ge 0} \binom{i}{j} x^i$,
and this sum equals $\frac{1}{1 - x} \sum_{j \ge 0} \left(\frac{x}{1 - x}\right)^j$. -/
public theorem tsum_pascalEntry_comm (x : ℝ) (hx : |x| < 1 / 2) :
    (∑' j, ∑' i, (pascalEntry i j : ℝ) * x ^ i) =
      (∑' i, ∑' j, (pascalEntry i j : ℝ) * x ^ i) ∧
    (∑' i, ∑' j, (pascalEntry i j : ℝ) * x ^ i) =
      (1 / (1 - x)) * (∑' j, (x / (1 - x)) ^ j) := by
  refine ⟨Summable.tsum_comm (masterSumm x hx), ?_⟩
  have hLHS : (∑' i, x ^ i * 2 ^ i) = (1 - 2 * x)⁻¹ := by
    rw [tsum_congr (fun i => (by ring : x ^ i * (2 : ℝ) ^ i = (2 * x) ^ i)),
      tsum_geometric_of_abs_lt_one (abs_two_mul_lt_one x hx)]
  have hRHS : (∑' j, (x / (1 - x)) ^ j) = (1 - x / (1 - x))⁻¹ :=
    tsum_geometric_of_abs_lt_one (abs_div_one_sub_lt_one x hx)
  have h1x_ne : (1 : ℝ) - x ≠ 0 := ne_of_gt (by have hb := abs_lt.mp hx; linarith)
  have hmul : ((1 : ℝ) - x) * (1 - x / (1 - x)) = 1 - 2 * x := by
    rw [mul_comm ((1 : ℝ) - x), sub_mul, one_mul, div_mul_cancel₀ _ h1x_ne]; ring
  rw [tsum_congr (fun i => rowTsum i x), hLHS, hRHS, one_div, ← mul_inv, hmul]

/-- **Summing the Pascal matrix row by row.** For every real number $x$ with $|x| < 1/2$,
writing $\binom{i}{j}$ for the entry of the infinite Pascal matrix in row $i$ and column $j$, we
have $\sum_{i \ge 0} x^i \sum_{j=0}^{i} \binom{i}{j} = \frac{1}{1 - 2x}$. -/
public theorem tsum_pascalEntry_row (x : ℝ) (hx : |x| < 1 / 2) :
    (∑' i, x ^ i * Finset.sum (Finset.range (i + 1))
      (fun j => (pascalEntry i j : ℝ))) = 1 / (1 - 2 * x) := by
  have hrow : ∀ i : ℕ, x ^ i * (Finset.sum (Finset.range (i + 1))
      fun j => (pascalEntry i j : ℝ)) = (2 * x) ^ i := by
    intro i; rw [rowSum]; ring
  rw [tsum_congr hrow,
    tsum_geometric_of_abs_lt_one (abs_two_mul_lt_one x hx), inv_eq_one_div]

/-- **Total generating function of the Pascal matrix.** For every real number $x$ with
$|x| < 1/2$, the sum $\sum_{j \ge 0} \alpha_j(x)$ of the column generating functions of the
infinite Pascal matrix equals $\sum_{i \ge 0} (2x)^i$, and
$\sum_{i \ge 0} (2x)^i = \frac{1}{1 - 2x}$. -/
public theorem tsum_pascalAlpha_eq_geometric (x : ℝ) (hx : |x| < 1 / 2) :
    (∑' j, pascalAlpha j x) = (∑' i, (2 * x) ^ i) ∧
      (∑' i, (2 * x) ^ i) = 1 / (1 - 2 * x) := by
  constructor
  · rw [(tsum_pascalAlpha_eq x hx).1, (tsum_pascalEntry_comm x hx).1]
    exact tsum_congr fun i => by rw [rowTsum]; ring
  · rw [tsum_geometric_of_abs_lt_one (abs_two_mul_lt_one x hx), inv_eq_one_div]

end MetaMathlibExt
