/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 6, Entry 5

The factorial series `C(x) = ∑_{j ≥ 0} (-1)ʲ / ((x + 1) ⋯ (x + j + 1))` converges for `0 < x` and
has the asymptotic expansion `C(x) ~ ∑_{j ≥ 0} (-1)ʲ B_{j+1} / x^{j+1}` as `x → ∞`, where `B_n` is
the `n`-th Bell number.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch6

namespace Entry5Digamma

open Asymptotics Filter Finset

noncomputable section

/-- **Terms of Ramanujan's factorial series.** For a real number $x$ and a natural number $j$,
the $j$-th term of Ramanujan's factorial series is $(-1)^j / ((x + 1)(x + 2) \cdots (x + j + 1))$,
read as $0$ when the denominator vanishes. -/
def chapter6Section13ExampleCTerm (x : ℝ) (j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j /
    ∏ r ∈ range (j + 1), (x + (r + 1 : ℕ))

/-- **Ramanujan's factorial series.** For a real number $x$, $C(x)$ is the sum
$\sum_{j \ge 0} (-1)^j / ((x + 1)(x + 2) \cdots (x + j + 1))$ of Ramanujan's factorial series,
where a term is read as $0$ when its denominator vanishes and the sum is taken to be $0$ when
the series is not summable.

The series is summable for every $x > 0$. -/
def chapter6Section13ExampleCSum (x : ℝ) : ℝ :=
  ∑' j : ℕ, chapter6Section13ExampleCTerm x j

private lemma factorial_as_prod_aux (j : ℕ) :
    ((j + 1).factorial : ℝ) = ∏ r ∈ Finset.range (j + 1), ((r + 1 : ℕ) : ℝ) := by
  have h : (j + 1).factorial = ∏ r ∈ Finset.range (j + 1), (r + 1) := by
    rw [Finset.prod_range_add_one_eq_factorial]
  rw [h]
  push_cast
  rfl

private lemma prod_le_factorial_bound_aux (x : ℝ) (hx : 0 < x) (j : ℕ) :
    ((j + 1).factorial : ℝ) ≤ ∏ r ∈ Finset.range (j + 1), (x + (r + 1 : ℕ)) := by
  rw [factorial_as_prod_aux]
  gcongr with r hr
  linarith [hx]

private lemma norm_CTerm_le_aux (x : ℝ) (hx : 0 < x) (j : ℕ) :
    ‖chapter6Section13ExampleCTerm x j‖ ≤ 1 / ((j + 1).factorial : ℝ) := by
  unfold chapter6Section13ExampleCTerm
  have hprod_pos : 0 < ∏ r ∈ Finset.range (j + 1), (x + (r + 1 : ℕ)) := by
    apply Finset.prod_pos
    intro r hr
    have hnn : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by positivity
    linarith [hx]
  have hfact_pos : (0 : ℝ) < ((j + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (j + 1)
  have hle := prod_le_factorial_bound_aux x hx j
  rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_eq_abs,
    abs_of_pos hprod_pos]
  exact one_div_le_one_div_of_le hfact_pos hle

/-- **Convergence of Ramanujan's factorial series.** For every real $x > 0$, the series
$\sum_{j \ge 0} (-1)^j / ((x + 1)(x + 2) \cdots (x + j + 1))$ is summable.

Its $j$-th term is bounded in absolute value by $1 / (j + 1)!$. -/
theorem summable_chapter6Section13ExampleCTerm (x : ℝ) (hx : 0 < x) :
    Summable (chapter6Section13ExampleCTerm x) := by
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / (n.factorial : ℝ)) := by
    have h := Real.summable_pow_div_factorial (1 : ℝ)
    simpa using h
  have hshift : Summable (fun j : ℕ => (1 : ℝ) / (((j + 1).factorial : ℕ) : ℝ)) := by
    exact (summable_nat_add_iff 1).mpr hsum
  refine Summable.of_norm_bounded hshift (fun j => ?_)
  exact norm_CTerm_le_aux x hx j

private lemma eventually_summable_aux :
    ∀ᶠ x : ℝ in atTop, 0 < x ∧ Summable (chapter6Section13ExampleCTerm x) := by
  filter_upwards [eventually_gt_atTop 0] with x hx
  exact ⟨hx, summable_chapter6Section13ExampleCTerm x hx⟩

private lemma prod_ge_pow_aux (x : ℝ) (hx : 0 < x) (j : ℕ) :
    x ^ (j + 1) ≤ ∏ r ∈ Finset.range (j + 1), (x + (r + 1 : ℕ)) := by
  have h1 : ∏ r ∈ Finset.range (j + 1), x ≤ ∏ r ∈ Finset.range (j + 1), (x + (r + 1 : ℕ)) := by
    gcongr with r hr
    have hnn : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by positivity
    linarith
  rwa [Finset.prod_const, Finset.card_range] at h1

private lemma norm_CTerm_le_pow_aux (x : ℝ) (hx : 0 < x) (j : ℕ) :
    ‖chapter6Section13ExampleCTerm x j‖ ≤ 1 / x ^ (j + 1) := by
  unfold chapter6Section13ExampleCTerm
  have hprod_pos : 0 < ∏ r ∈ Finset.range (j + 1), (x + (r + 1 : ℕ)) := by
    apply Finset.prod_pos
    intro r hr
    have hnn : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by positivity
    linarith [hx]
  have hxpow : (0 : ℝ) < x ^ (j + 1) := pow_pos hx _
  have hle := prod_ge_pow_aux x hx j
  rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_eq_abs,
    abs_of_pos hprod_pos]
  exact one_div_le_one_div_of_le hxpow hle

private lemma pow_succ_eq_aux (x : ℝ) (j : ℕ) :
    (1 : ℝ) / x ^ (j + 1) = (1 / x) * ((1 / x) ^ j) := by
  rw [← one_div_pow, ← pow_succ']

private lemma bigO_zero_aux : (fun x : ℝ => chapter6Section13ExampleCSum x) =O[atTop]
    (fun x : ℝ => 1 / x ^ (0 + 1)) := by
  apply Asymptotics.IsBigOWith.isBigO
  apply Asymptotics.IsBigOWith.of_bound (c := 2)
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hr : (1 / x : ℝ) < 1 := by
    rw [div_lt_one hxpos]
    exact hx1
  have hrnn : (0 : ℝ) ≤ 1 / x := by positivity
  have hgeo : Summable (fun j : ℕ => (1 / x : ℝ) ^ j) :=
    summable_geometric_of_lt_one hrnn hr
  have hbound : Summable (fun j : ℕ => (1 : ℝ) / x ^ (j + 1)) := by
    have h2 : (fun j : ℕ => (1 : ℝ) / x ^ (j + 1)) = (fun j : ℕ => (1 / x) * ((1 / x) ^ j)) := by
      funext j
      exact pow_succ_eq_aux x j
    rw [h2]
    exact hgeo.mul_left (1 / x)
  have hnorm_sum : Summable (fun j => ‖chapter6Section13ExampleCTerm x j‖) := by
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => norm_CTerm_le_pow_aux x hxpos j) hbound
  have htsum_bound : ‖∑' j, chapter6Section13ExampleCTerm x j‖ ≤ ∑' j, (1 : ℝ) / x ^ (j + 1) := by
    calc ‖∑' j, chapter6Section13ExampleCTerm x j‖
        ≤ ∑' j, ‖chapter6Section13ExampleCTerm x j‖ := norm_tsum_le_tsum_norm hnorm_sum
      _ ≤ ∑' j, (1 : ℝ) / x ^ (j + 1) :=
        Summable.tsum_le_tsum (fun j => norm_CTerm_le_pow_aux x hxpos j) hnorm_sum hbound
  have hgeo_val : ∑' j : ℕ, (1 : ℝ) / x ^ (j + 1) = 1 / (x - 1) := by
    have htsum : ∑' j : ℕ, (1 / x : ℝ) ^ j = (1 - 1 / x)⁻¹ := tsum_geometric_of_lt_one hrnn hr
    have hmul : ∑' j : ℕ, (1 / x : ℝ) * ((1 / x) ^ j) = (1 / x) * (1 - 1 / x)⁻¹ :=
      Summable.tsum_mul_left (1 / x) hgeo ▸ congrArg ((1 / x) * ·) htsum
    have heq : (fun j : ℕ => (1 : ℝ) / x ^ (j + 1)) = (fun j : ℕ => (1 / x) * ((1 / x) ^ j)) := by
      funext j
      exact pow_succ_eq_aux x j
    rw [heq, hmul]
    have hne1 : x - 1 ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < x - 1)
    have hne2 : x ≠ 0 := ne_of_gt hxpos
    field_simp
  have hnorm_eq : ‖(1 : ℝ) / x ^ (0 + 1)‖ = 1 / x := by
    simp [Real.norm_eq_abs, abs_of_pos hxpos]
  have hle : 1 / (x - 1) ≤ 2 / x := by
    have hxn : (0 : ℝ) < x - 1 := by linarith
    have hne1 : x - 1 ≠ 0 := ne_of_gt hxn
    have hne2 : x ≠ 0 := ne_of_gt hxpos
    field_simp
    nlinarith
  calc ‖(fun x : ℝ => chapter6Section13ExampleCSum x) x‖
      = ‖∑' j, chapter6Section13ExampleCTerm x j‖ := by
        unfold chapter6Section13ExampleCSum; rfl
    _ ≤ ∑' j, (1 : ℝ) / x ^ (j + 1) := htsum_bound
    _ = 1 / (x - 1) := hgeo_val
    _ ≤ 2 / x := hle
    _ = 2 * (1 / x) := by ring
    _ = 2 * ‖(1 : ℝ) / x ^ (0 + 1)‖ := by rw [hnorm_eq]
    _ = 2 * ‖(fun x : ℝ => 1 / x ^ (0 + 1)) x‖ := rfl

private lemma prod_succ_eq_aux (x : ℝ) (j : ℕ) :
    ∏ r ∈ Finset.range (j + 2), (x + (r + 1 : ℕ)) =
      (x + 1) * ∏ r ∈ Finset.range (j + 1), ((x + 1) + (r + 1 : ℕ)) := by
  rw [Finset.prod_range_succ']
  rw [mul_comm]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro r hr
    push_cast
    ring

@[simp]
theorem chapter6Section13ExampleCTerm_zero (x : ℝ) :
    chapter6Section13ExampleCTerm x 0 = 1 / (x + 1) := by
  unfold chapter6Section13ExampleCTerm
  simp

/-- **Recursion for the terms of Ramanujan's factorial series.** Write
$c_j(x) = (-1)^j / ((x + 1)(x + 2) \cdots (x + j + 1))$ for the $j$-th term of Ramanujan's
factorial series, with division by $0$ read as $0$. For every real $x$ and every natural number
$j$, $c_{j+1}(x) = -\frac{1}{x + 1} \, c_j(x + 1)$. -/
theorem chapter6Section13ExampleCTerm_succ (x : ℝ) (j : ℕ) :
    chapter6Section13ExampleCTerm x (j + 1) =
      (-1 / (x + 1)) * chapter6Section13ExampleCTerm (x + 1) j := by
  unfold chapter6Section13ExampleCTerm
  rw [prod_succ_eq_aux]
  rw [pow_succ]
  field_simp

/-- **Functional equation of Ramanujan's factorial series.** Let
$C(x) = \sum_{j \ge 0} (-1)^j / ((x + 1)(x + 2) \cdots (x + j + 1))$ be Ramanujan's factorial
series. For every real $x > 0$, $C(x) = \frac{1}{x + 1} - \frac{C(x + 1)}{x + 1}$. -/
theorem chapter6Section13ExampleCSum_eq (x : ℝ) (hx : 0 < x) :
    chapter6Section13ExampleCSum x =
      1 / (x + 1) - chapter6Section13ExampleCSum (x + 1) / (x + 1) := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hsx := summable_chapter6Section13ExampleCTerm x hx
  have hsx1 := summable_chapter6Section13ExampleCTerm (x + 1) hx1
  unfold chapter6Section13ExampleCSum
  rw [hsx.tsum_eq_zero_add, chapter6Section13ExampleCTerm_zero]
  have htail : (fun b : ℕ => chapter6Section13ExampleCTerm x (b + 1)) =
      (fun b : ℕ => (-1 / (x + 1)) * chapter6Section13ExampleCTerm (x + 1) b) := by
    funext b
    exact chapter6Section13ExampleCTerm_succ x b
  rw [htail, hsx1.tsum_mul_left]
  ring

private lemma triangle_regroup_aux (n : ℕ) (G : ℕ → ℕ → ℝ) :
    (∑ k ∈ range (n + 1), ∑ i ∈ range (n + 1 - k), G k i)
      = ∑ m ∈ range (n + 1), ∑ k ∈ range (m + 1), G k (m - k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hnm : n + 2 = n + 1 + 1 := by omega
    rw [hnm]
    have hpeel : (∑ k ∈ range (n + 1 + 1), ∑ i ∈ range (n + 1 + 1 - k), G k i)
        = (∑ k ∈ range (n + 1), ∑ i ∈ range (n + 1 + 1 - k), G k i)
          + (∑ i ∈ range (n + 1 + 1 - (n + 1)), G (n + 1) i) :=
      Finset.sum_range_succ _ _
    have hinner : ∀ k ∈ range (n + 1),
        (∑ i ∈ range (n + 1 + 1 - k), G k i)
        = (∑ i ∈ range (n + 1 - k), G k i) + G k (n + 1 - k) := by
      intro k hk
      have hbridge : n + 1 + 1 - k = (n + 1 - k) + 1 := by
        have hkk : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        omega
      rw [hbridge]
      exact Finset.sum_range_succ _ _
    have hlast : (∑ i ∈ range (n + 1 + 1 - (n + 1)), G (n + 1) i) = G (n + 1) 0 := by
      have h10 : n + 1 + 1 - (n + 1) = 1 := by omega
      rw [h10]
      exact Finset.sum_range_one _
    have hrhs : (∑ m ∈ range (n + 1 + 1), ∑ k ∈ range (m + 1), G k (m - k))
        = (∑ m ∈ range (n + 1), ∑ k ∈ range (m + 1), G k (m - k))
          + (∑ k ∈ range (n + 1 + 1), G k (n + 1 - k)) :=
      Finset.sum_range_succ _ _
    have hF : (fun k => G k (n + 1 - k)) (n + 1) = G (n + 1) 0 := by simp
    have hdiag : (∑ k ∈ range (n + 1), G k (n + 1 - k)) + G (n + 1) 0
        = ∑ k ∈ range (n + 1 + 1), G k (n + 1 - k) := by
      rw [← hF]
      exact (Finset.sum_range_succ _ _).symm
    calc (∑ k ∈ range (n + 1 + 1), ∑ i ∈ range (n + 1 + 1 - k), G k i)
        = (∑ k ∈ range (n + 1), ∑ i ∈ range (n + 1 - k), G k i)
          + ((∑ k ∈ range (n + 1), G k (n + 1 - k)) + G (n + 1) 0) := by
          rw [hpeel, Finset.sum_congr rfl hinner, Finset.sum_add_distrib, hlast,
            add_assoc]
      _ = (∑ m ∈ range (n + 1), ∑ k ∈ range (m + 1), G k (m - k))
          + (∑ k ∈ range (n + 1 + 1), G k (n + 1 - k)) := by
          rw [ih, hdiag]
      _ = _ := hrhs.symm

private lemma hockeystick_aux (k t : ℕ) :
    (∑ i ∈ range (t + 1), ((k + i).choose k : ℝ)) = ((k + t + 1).choose t : ℝ) := by
  induction t with
  | zero => simp
  | succ t iht =>
    rw [Finset.sum_range_succ, iht]
    have e1 : k + (t + 1) = (k + t + 1) := by omega
    rw [e1]
    have hle : k ≤ k + t + 1 := by omega
    have hsub : k + t + 1 - k = t + 1 := by omega
    have hsym : (k + t + 1).choose k = (k + t + 1).choose (t + 1) := by
      rw [← hsub]
      exact (Nat.choose_symm hle).symm
    have hnat : (k + t + 1).choose t + (k + t + 1).choose k
        = (k + t + 1 + 1).choose (t + 1) := by
      rw [hsym]
      exact (Nat.choose_succ_succ (k + t + 1) t).symm
    exact_mod_cast hnat

private lemma monomial_bigO_aux (c : ℝ) (a b : ℕ) (hab : a ≤ b) :
    (fun x : ℝ => c / x ^ b) =O[atTop] (fun x => 1 / x ^ a) := by
  apply Asymptotics.IsBigOWith.isBigO
  apply Asymptotics.IsBigOWith.of_bound (c := |c|)
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have e1 : ‖c / x ^ b‖ = |c| / x ^ b := by
    rw [norm_div, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0]
  have e2 : ‖(1 : ℝ) / x ^ a‖ = 1 / x ^ a := by
    rw [norm_div, norm_one, norm_pow, Real.norm_eq_abs, abs_of_pos hx0]
  have hle : x ^ a ≤ x ^ b := pow_le_pow_right₀ (by linarith) hab
  rw [e1, e2, mul_one_div]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  simpa [one_div] using one_div_le_one_div_of_le (pow_pos hx0 a) hle

private lemma expand_zero_aux (M : ℕ) (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    1 / (x + 1) - ∑ i ∈ range M, (-1 : ℝ) ^ i / x ^ (1 + i)
      = (-1 : ℝ) ^ M / (x ^ M * (x + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h2 : (1 : ℝ) / (x + 1) - (∑ i ∈ range M, (-1) ^ i / x ^ (1 + i) + (-1) ^ M / x ^ (1 + M))
        = (1 / (x + 1) - ∑ i ∈ range M, (-1) ^ i / x ^ (1 + i)) - (-1) ^ M / x ^ (1 + M) := by
      ring
    have hxM : x ^ M ≠ 0 := pow_ne_zero M hx
    have hxM1 : x ^ (M + 1) ≠ 0 := pow_ne_zero (M + 1) hx
    rw [Finset.sum_range_succ, h2, ih]
    field_simp
    ring

private lemma expand_zero_bigO_aux (M : ℕ) :
    (fun x : ℝ => 1 / (x + 1) - ∑ j ∈ range M, (-1 : ℝ) ^ j / x ^ (1 + j))
    =O[atTop] (fun x => 1 / x ^ (1 + M)) := by
  apply Asymptotics.IsBigOWith.isBigO
  apply Asymptotics.IsBigOWith.of_bound (c := 1)
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hxn : x ≠ 0 := ne_of_gt hx0
  have hx1n : x + 1 ≠ 0 := ne_of_gt (by linarith)
  rw [expand_zero_aux M x hxn hx1n]
  have hpos : (0 : ℝ) < x ^ M * (x + 1) := mul_pos (pow_pos hx0 M) (by linarith)
  have e1 : ‖(-1 : ℝ) ^ M / (x ^ M * (x + 1))‖ = 1 / (x ^ M * (x + 1)) := by
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_eq_abs,
      abs_of_pos hpos]
  have e2 : ‖(1 : ℝ) / x ^ (1 + M)‖ = 1 / x ^ (1 + M) := by
    rw [norm_div, norm_one, norm_pow, Real.norm_eq_abs, abs_of_pos hx0]
  rw [e1, e2, one_mul]
  apply one_div_le_one_div_of_le (pow_pos hx0 (1 + M))
  have hle : x ^ M * x ≤ x ^ M * (x + 1) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (le_of_lt hx0) M)
    linarith
  have hbridge : (1 : ℕ) + M = M + 1 := by omega
  calc x ^ (1 + M) = x ^ M * x := by rw [hbridge, pow_succ]
    _ ≤ x ^ M * (x + 1) := hle

private lemma expand_bigO_aux (k M : ℕ) :
    (fun x : ℝ => 1 / (x + 1) ^ (k + 1)
      - ∑ i ∈ range M, (-1 : ℝ) ^ i * ((k + i).choose k : ℝ) / x ^ (k + 1 + i))
    =O[atTop] (fun x => 1 / x ^ (k + 1 + M)) := by
  induction k generalizing M with
  | zero =>
    have hbase := expand_zero_bigO_aux M
    simpa using hbase
  | succ k ih =>
    show (fun x : ℝ => 1 / (x + 1) ^ (k + 1 + 1)
      - ∑ t ∈ range M, (-1 : ℝ) ^ t * (((k + 1 + t).choose (k + 1) : ℕ) : ℝ) / x ^ (k + 1 + 1 + t))
      =O[atTop] (fun x => 1 / x ^ (k + 1 + 1 + M))
    have hA := ih (M + 1)
    have hB := expand_zero_bigO_aux (M + 1)
    set Sk : ℝ → ℝ := fun x => ∑ i ∈ range (M + 1),
      (-1 : ℝ) ^ i * ((k + i).choose k : ℝ) / x ^ (k + 1 + i) with hSk
    set S0 : ℝ → ℝ := fun x => ∑ j ∈ range (M + 1), (-1 : ℝ) ^ j / x ^ (1 + j) with hS0
    set Tf : ℝ → ℝ := fun x => ∑ t ∈ range (M + 1),
      (-1 : ℝ) ^ t * (((k + 1 + t).choose (k + 1) : ℕ) : ℝ) / x ^ (k + 1 + 1 + t) with hTf
    set Tg : ℝ → ℝ := fun x => ∑ t ∈ range M,
      (-1 : ℝ) ^ t * (((k + 1 + t).choose (k + 1) : ℕ) : ℝ) / x ^ (k + 1 + 1 + t) with hTg
    set Hh : ℝ → ℝ := fun x => ∑ i ∈ range (M + 1), ∑ j ∈ Finset.Ico (M + 1 - i) (M + 1),
      (((-1 : ℝ) ^ i * ((k + i).choose k : ℝ)) * (-1 : ℝ) ^ j) / x ^ (k + 1 + 1 + i + j) with hHh
    have hSkx : ∀ x, Sk x = ∑ i ∈ range (M + 1),
      (-1 : ℝ) ^ i * ((k + i).choose k : ℝ) / x ^ (k + 1 + i) := fun x => rfl
    have hS0x : ∀ x, S0 x = ∑ j ∈ range (M + 1), (-1 : ℝ) ^ j / x ^ (1 + j) :=
      fun x => rfl
    have hTfx : ∀ x, Tf x = ∑ t ∈ range (M + 1),
      (-1 : ℝ) ^ t * (((k + 1 + t).choose (k + 1) : ℕ) : ℝ) / x ^ (k + 1 + 1 + t) :=
      fun x => rfl
    have hTgx : ∀ x, Tg x = ∑ t ∈ range M,
      (-1 : ℝ) ^ t * (((k + 1 + t).choose (k + 1) : ℕ) : ℝ) / x ^ (k + 1 + 1 + t) :=
      fun x => rfl
    have hHhx : ∀ x, Hh x = ∑ i ∈ range (M + 1), ∑ j ∈ Finset.Ico (M + 1 - i) (M + 1),
      (((-1 : ℝ) ^ i * ((k + i).choose k : ℝ)) * (-1 : ℝ) ^ j) / x ^ (k + 1 + 1 + i + j) :=
      fun x => rfl
    have hAf : (fun x : ℝ => 1 / (x + 1) ^ (k + 1) - Sk x) =O[atTop]
        (fun x => 1 / x ^ (k + 1 + (M + 1))) := hA
    have hBf : (fun x : ℝ => 1 / (x + 1) - S0 x) =O[atTop]
        (fun x => 1 / x ^ (1 + (M + 1))) := hB
    have hSkO : Sk =O[atTop] (fun x : ℝ => 1 / x ^ (k + 1)) := by
      have hSkEq : Sk = ∑ i ∈ range (M + 1),
          (fun x : ℝ => (-1 : ℝ) ^ i * ((k + i).choose k : ℝ) / x ^ (k + 1 + i)) := by
        funext x
        simp only [hSkx, Finset.sum_apply]
      rw [hSkEq]
      apply Asymptotics.IsBigO.sum
      intro i _
      exact monomial_bigO_aux _ _ _ (Nat.le_add_right _ _)
    have hS0O : S0 =O[atTop] (fun x : ℝ => 1 / x ^ 1) := by
      have hS0Eq : S0 = ∑ j ∈ range (M + 1),
          (fun x : ℝ => (-1 : ℝ) ^ j / x ^ (1 + j)) := by
        funext x
        simp only [hS0x, Finset.sum_apply]
      rw [hS0Eq]
      apply Asymptotics.IsBigO.sum
      intro j _
      exact monomial_bigO_aux _ _ _ (Nat.le_add_right _ _)
    have hpx : ∀ x : ℝ, (1 / (x + 1) ^ (k + 1)) * (1 / (x + 1))
        = 1 / (x + 1) ^ (k + 1 + 1) := by
      intro x
      rw [pow_succ (x + 1) (k + 1), div_mul_div_comm, one_mul]
    have hSSx : ∀ x : ℝ, Sk x * S0 x - Tf x = Hh x := by
      intro x
      rw [hSkx x, hS0x x, hTfx x, hHhx x]
      rw [Finset.sum_mul_sum]
      have hterm : ∀ i j : ℕ,
          (((-1 : ℝ) ^ i * ((k + i).choose k : ℝ) / x ^ (k + 1 + i))
            * ((-1 : ℝ) ^ j / x ^ (1 + j)))
          = (((-1 : ℝ) ^ i * ((k + i).choose k : ℝ)) * (-1 : ℝ) ^ j)
            / x ^ (k + 1 + 1 + i + j) := by
        intro i j
        have hexp2 : (k + 1 + i) + (1 + j) = k + 1 + 1 + i + j := by omega
        rw [div_mul_div_comm, ← pow_add, hexp2]
      rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hterm i j))]
      have hsplit : ∀ i ∈ range (M + 1),
          (∑ j ∈ range (M + 1),
            (((-1 : ℝ) ^ i * ((k + i).choose k : ℝ)) * (-1 : ℝ) ^ j)
            / x ^ (k + 1 + 1 + i + j))
          = (∑ j ∈ range (M + 1 - i),
            (((-1 : ℝ) ^ i * ((k + i).choose k : ℝ)) * (-1 : ℝ) ^ j)
            / x ^ (k + 1 + 1 + i + j))
            + (∑ j ∈ Finset.Ico (M + 1 - i) (M + 1),
            (((-1 : ℝ) ^ i * ((k + i).choose k : ℝ)) * (-1 : ℝ) ^ j)
            / x ^ (k + 1 + 1 + i + j)) := by
        intro i _
        exact (Finset.sum_range_add_sum_Ico _ (Nat.sub_le _ _)).symm
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      have hlow : (∑ i ∈ range (M + 1), ∑ j ∈ range (M + 1 - i),
          (((-1 : ℝ) ^ i * ((k + i).choose k : ℝ)) * (-1 : ℝ) ^ j)
          / x ^ (k + 1 + 1 + i + j))
          = ∑ t ∈ range (M + 1),
            (-1 : ℝ) ^ t * (((k + 1 + t).choose (k + 1) : ℕ) : ℝ) / x ^ (k + 1 + 1 + t) := by
        rw [triangle_regroup_aux]
        apply Finset.sum_congr rfl
        intro t _
        have hterm2 : ∀ i ∈ range (t + 1),
            (((-1 : ℝ) ^ i * ((k + i).choose k : ℝ)) * (-1 : ℝ) ^ (t - i))
            / x ^ (k + 1 + 1 + i + (t - i))
            = ((-1 : ℝ) ^ t * ((k + i).choose k : ℝ)) / x ^ (k + 1 + 1 + t) := by
          intro i hi
          have hit : i ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          have hexp : k + 1 + 1 + i + (t - i) = k + 1 + 1 + t := by omega
          have hsign : (-1 : ℝ) ^ i * (-1 : ℝ) ^ (t - i) = (-1 : ℝ) ^ t := by
            rw [← pow_add, Nat.add_sub_cancel' hit]
          have hnum : (((-1 : ℝ) ^ i * ((k + i).choose k : ℝ)) * (-1 : ℝ) ^ (t - i))
              = (-1 : ℝ) ^ t * ((k + i).choose k : ℝ) := by
            calc (((-1 : ℝ) ^ i * _) * (-1 : ℝ) ^ (t - i))
                = _ * ((-1 : ℝ) ^ i * (-1 : ℝ) ^ (t - i)) := by ring
              _ = _ * (-1 : ℝ) ^ t := by rw [hsign]
              _ = (-1 : ℝ) ^ t * _ := by ring
          rw [hexp, hnum]
        rw [Finset.sum_congr rfl hterm2, ← Finset.sum_div, ← Finset.mul_sum,
          hockeystick_aux]
        have hsym : (((k + 1 + t).choose (k + 1) : ℕ) : ℝ)
            = ((k + t + 1).choose t : ℝ) := by
          have h1 : k + 1 + t = (k + t + 1) := by omega
          have h2 : k + 1 = (k + t + 1) - t := by omega
          have hle : t ≤ k + t + 1 := by omega
          rw [h1, h2]
          exact_mod_cast Nat.choose_symm hle
        rw [← hsym]
      rw [hlow, add_sub_cancel_left]
    have key : (fun x : ℝ => 1 / (x + 1) ^ (k + 1 + 1) - Tg x)
        = (fun x => (Tf x - Tg x) + (Hh x + (Sk x * (1 / (x + 1) - S0 x)
          + ((1 / (x + 1) ^ (k + 1) - Sk x) * S0 x
            + (1 / (x + 1) ^ (k + 1) - Sk x) * (1 / (x + 1) - S0 x))))) := by
      funext x
      rw [← hSSx x, ← hpx x]
      ring
    have hTfTg : (fun x : ℝ => Tf x - Tg x) =O[atTop]
        (fun x => 1 / x ^ (k + 1 + 1 + M)) := by
      have hpeel : ∀ x, Tf x - Tg x
          = ((-1 : ℝ) ^ M * (((k + 1 + M).choose (k + 1) : ℕ) : ℝ))
            / x ^ (k + 1 + 1 + M) := by
        intro x
        rw [hTfx x, hTgx x, Finset.sum_range_succ]
        abel
      have hfun : (fun x : ℝ => Tf x - Tg x)
          = (fun x => (((-1 : ℝ) ^ M * (((k + 1 + M).choose (k + 1) : ℕ) : ℝ))
            / x ^ (k + 1 + 1 + M))) :=
        funext hpeel
      rw [hfun]
      exact monomial_bigO_aux _ _ _ le_rfl
    have hHO : Hh =O[atTop] (fun x => 1 / x ^ (k + 1 + 1 + M)) := by
      have hHhEq : Hh = ∑ i ∈ range (M + 1),
          (fun x : ℝ => ∑ j ∈ Finset.Ico (M + 1 - i) (M + 1),
            (((-1 : ℝ) ^ i * ((k + i).choose k : ℝ)) * (-1 : ℝ) ^ j)
            / x ^ (k + 1 + 1 + i + j)) := by
        funext x
        simp only [hHhx, Finset.sum_apply]
      rw [hHhEq]
      apply Asymptotics.IsBigO.sum
      intro i hi
      have hiM : i ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hinnerEq : (fun x : ℝ => ∑ j ∈ Finset.Ico (M + 1 - i) (M + 1),
            (((-1 : ℝ) ^ i * ((k + i).choose k : ℝ)) * (-1 : ℝ) ^ j)
            / x ^ (k + 1 + 1 + i + j))
          = ∑ j ∈ Finset.Ico (M + 1 - i) (M + 1),
            (fun x : ℝ => (((-1 : ℝ) ^ i * ((k + i).choose k : ℝ)) * (-1 : ℝ) ^ j)
              / x ^ (k + 1 + 1 + i + j)) := by
        funext x
        simp only [Finset.sum_apply]
      rw [hinnerEq]
      apply Asymptotics.IsBigO.sum
      intro j hj
      have hmem := Finset.mem_Ico.mp hj
      apply monomial_bigO_aux
      omega
    have hmul1 : (fun x : ℝ => (1 / x ^ (k + 1)) * (1 / x ^ (1 + (M + 1))))
        = (fun x => 1 / x ^ (k + 1 + (1 + (M + 1)))) := by
      funext x
      rw [div_mul_div_comm, one_mul, ← pow_add]
    have hc1 : (fun x : ℝ => Sk x * (1 / (x + 1) - S0 x)) =O[atTop]
        (fun x => 1 / x ^ (k + 1 + 1 + M)) := by
      apply Asymptotics.IsBigO.trans (hSkO.mul hBf)
      change (fun x : ℝ => (1 / x ^ (k + 1)) * (1 / x ^ (1 + (M + 1)))) =O[atTop]
        (fun x => 1 / x ^ (k + 1 + 1 + M))
      rw [hmul1]
      exact monomial_bigO_aux _ _ _ (by omega)
    have hmul2 : (fun x : ℝ => (1 / x ^ (k + 1 + (M + 1))) * (1 / x ^ 1))
        = (fun x => 1 / x ^ (k + 1 + (M + 1) + 1)) := by
      funext x
      rw [div_mul_div_comm, one_mul, ← pow_add]
    have hc2 : (fun x : ℝ => (1 / (x + 1) ^ (k + 1) - Sk x) * S0 x) =O[atTop]
        (fun x => 1 / x ^ (k + 1 + 1 + M)) := by
      apply Asymptotics.IsBigO.trans (hAf.mul hS0O)
      change (fun x : ℝ => (1 / x ^ (k + 1 + (M + 1))) * (1 / x ^ 1)) =O[atTop]
        (fun x => 1 / x ^ (k + 1 + 1 + M))
      rw [hmul2]
      exact monomial_bigO_aux _ _ _ (by omega)
    have hmul3 : (fun x : ℝ => (1 / x ^ (k + 1 + (M + 1))) * (1 / x ^ (1 + (M + 1))))
        = (fun x => 1 / x ^ (k + 1 + (M + 1) + (1 + (M + 1)))) := by
      funext x
      rw [div_mul_div_comm, one_mul, ← pow_add]
    have hc3 : (fun x : ℝ => (1 / (x + 1) ^ (k + 1) - Sk x) * (1 / (x + 1) - S0 x))
        =O[atTop] (fun x => 1 / x ^ (k + 1 + 1 + M)) := by
      apply Asymptotics.IsBigO.trans (hAf.mul hBf)
      change (fun x : ℝ => (1 / x ^ (k + 1 + (M + 1))) * (1 / x ^ (1 + (M + 1)))) =O[atTop]
        (fun x => 1 / x ^ (k + 1 + 1 + M))
      rw [hmul3]
      exact monomial_bigO_aux _ _ _ (by omega)
    have hTot := hTfTg.add (hHO.add (hc1.add (hc2.add hc3)))
    change (fun x : ℝ => 1 / (x + 1) ^ (k + 1 + 1) - Tg x) =O[atTop]
      (fun x => 1 / x ^ (k + 1 + 1 + M))
    rw [key]
    exact hTot

private lemma bell_recurrence_real_aux (m : ℕ) : (((m + 1).bell : ℕ) : ℝ)
    = ∑ j ∈ range (m + 1), ((m.choose j : ℕ) : ℝ) * ((j.bell : ℕ) : ℝ) := by
  have h : (m + 1).bell = ∑ j ∈ range (m + 1), m.choose j * j.bell := by
    rw [Nat.bell_succ', ← Finset.Nat.sum_antidiagonal_swap,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Prod.swap_prod_mk, Nat.choose_symm (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  exact_mod_cast h

private lemma const_bigO_one_aux (c : ℝ) : (fun _ : ℝ => c) =O[atTop] (fun _ => (1 : ℝ)) := by
  apply Asymptotics.IsBigOWith.isBigO
  apply Asymptotics.IsBigOWith.of_bound (c := |c|)
  filter_upwards with x
  rw [Real.norm_eq_abs, norm_one, mul_one]

/-- **Asymptotic expansion of Ramanujan's factorial series.** Let
$C(x) = \sum_{j \ge 0} (-1)^j / ((x + 1)(x + 2) \cdots (x + j + 1))$ be Ramanujan's factorial
series and let $B_n$ denote the $n$-th Bell number. For every natural number $N$,
$$C(x) - \sum_{j=0}^{N-1} \frac{(-1)^j B_{j+1}}{x^{j+1}} = O\left(\frac{1}{x^{N+1}}\right)
\quad \text{as } x \to \infty.$$ -/
theorem isBigO_chapter6Section13ExampleCSum_sub_sum_bell (N : ℕ) :
    (fun x : ℝ => chapter6Section13ExampleCSum x -
        ∑ j ∈ range N, (-1 : ℝ) ^ j * ((j + 1).bell : ℝ) / x ^ (j + 1))
      =O[atTop] (fun x : ℝ => 1 / x ^ (N + 1)) := by
  induction N with
  | zero =>
    simpa using bigO_zero_aux
  | succ n ih =>
    show (fun x : ℝ => chapter6Section13ExampleCSum x -
      ∑ j ∈ range (n + 1), (-1 : ℝ) ^ j * (((j + 1).bell : ℕ) : ℝ) / x ^ (j + 1))
      =O[atTop] (fun x => 1 / x ^ (n + 1 + 1))
    set d : ℕ → ℝ := fun k => ((k.bell : ℕ) : ℝ) with hd
    have hd0 : d 0 = 1 := by
      have h1 : d 0 = ((Nat.bell 0 : ℕ) : ℝ) := rfl
      rw [h1, Nat.bell_zero, Nat.cast_one]
    set Pn : ℝ → ℝ := fun x => ∑ j ∈ range n, (-1 : ℝ) ^ j * d (j + 1) / x ^ (j + 1) with hPn
    set Pnp1 : ℝ → ℝ := fun x => ∑ j ∈ range (n + 1), (-1 : ℝ) ^ j * d (j + 1) / x ^ (j + 1)
      with hPnp1
    set Qsum : ℝ → ℝ := fun x => ∑ k ∈ range (n + 1), (-1 : ℝ) ^ k * d k / (x + 1) ^ (k + 1)
      with hQsum
    have hQsumx : ∀ x, Qsum x = ∑ k ∈ range (n + 1), (-1 : ℝ) ^ k * d k / (x + 1) ^ (k + 1) :=
      fun x => rfl
    have hPnp1x : ∀ x, Pnp1 x = ∑ j ∈ range (n + 1), (-1 : ℝ) ^ j * d (j + 1) / x ^ (j + 1) :=
      fun x => rfl
    have hPnx : ∀ x, Pn x = ∑ j ∈ range n, (-1 : ℝ) ^ j * d (j + 1) / x ^ (j + 1) :=
      fun x => rfl
    have hRn : (fun x : ℝ => chapter6Section13ExampleCSum x - Pn x) =O[atTop]
        (fun x => 1 / x ^ (n + 1)) := ih
    have hQ : ∀ x : ℝ, Qsum x = 1 / (x + 1) - Pn (x + 1) / (x + 1) := by
      intro x
      rw [hQsumx x, hPnx (x + 1), Finset.sum_range_succ']
      have hF0 : (-1 : ℝ) ^ (0 : ℕ) * d 0 / (x + 1) ^ (0 + 1) = 1 / (x + 1) := by
        rw [hd0]
        simp
      rw [hF0]
      have htermQ : ∀ k ∈ range n,
          (-1 : ℝ) ^ (k + 1) * d (k + 1) / (x + 1) ^ (k + 1 + 1)
          = -(((-1 : ℝ) ^ k * d (k + 1) / (x + 1) ^ (k + 1)) / (x + 1)) := by
        intro k _
        rw [pow_succ (-1 : ℝ) k, div_div, ← pow_succ (x + 1) (k + 1)]
        ring
      rw [Finset.sum_congr rfl htermQ, Finset.sum_neg_distrib, ← Finset.sum_div]
      ring
    have hdBell : ∀ m ∈ range (n + 1),
        d (m + 1) = ∑ j ∈ range (m + 1), (m.choose j : ℝ) * d j := by
      intro m _
      have h1 : d (m + 1) = (((m + 1).bell : ℕ) : ℝ) := rfl
      have h2 : (∑ j ∈ range (m + 1), (m.choose j : ℝ) * d j)
          = ∑ j ∈ range (m + 1), ((m.choose j : ℕ) : ℝ) * ((j.bell : ℕ) : ℝ) := rfl
      rw [h1, h2]
      exact bell_recurrence_real_aux m
    have hG : ∀ (x : ℝ) (k : ℕ), k ∈ range (n + 1) → ∀ (i : ℕ), i ∈ range (n + 1 - k) →
        ((-1 : ℝ) ^ k * d k) * (((-1 : ℝ) ^ i * ((k + i).choose k : ℝ)) / x ^ (k + 1 + i))
        = (-1 : ℝ) ^ (k + i) * d k * ((k + i).choose k : ℝ) / x ^ (k + 1 + i) := by
      intro x k hk i hi
      have hsign2 : (-1 : ℝ) ^ k * (-1 : ℝ) ^ i = (-1 : ℝ) ^ (k + i) := (pow_add _ _ _).symm
      calc ((-1 : ℝ) ^ k * d k) * (((-1 : ℝ) ^ i * ((k + i).choose k : ℝ)) / x ^ (k + 1 + i))
          = (((-1 : ℝ) ^ k * (-1 : ℝ) ^ i) * d k * ((k + i).choose k : ℝ)) / x ^ (k + 1 + i) := by
            ring
        _ = (-1 : ℝ) ^ (k + i) * d k * ((k + i).choose k : ℝ) / x ^ (k + 1 + i) := by
            rw [hsign2]
    have htermP : ∀ (x : ℝ) (m : ℕ), m ∈ range (n + 1) → ∀ (k : ℕ), k ∈ range (m + 1) →
        (-1 : ℝ) ^ (k + (m - k)) * d k * (((k + (m - k)).choose k : ℕ) : ℝ) /
          x ^ (k + 1 + (m - k))
        = (-1 : ℝ) ^ m * d k * ((m.choose k : ℕ) : ℝ) / x ^ (m + 1) := by
      intro x m hm k hk
      have hkm : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have e1 : k + (m - k) = m := Nat.add_sub_cancel' hkm
      have e2 : k + 1 + (m - k) = m + 1 := by omega
      rw [e1, e2]
    have hinnerP : ∀ (x : ℝ) (m : ℕ), m ∈ range (n + 1) →
        (∑ k ∈ range (m + 1), (-1 : ℝ) ^ m * d k * ((m.choose k : ℕ) : ℝ) / x ^ (m + 1))
        = (-1 : ℝ) ^ m * d (m + 1) / x ^ (m + 1) := by
      intro x m hm
      rw [← Finset.sum_div]
      congr 1
      simp only [mul_assoc]
      rw [← Finset.mul_sum]
      congr 1
      rw [hdBell m hm]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hQS : ∀ x : ℝ,
        (∑ k ∈ range (n + 1), ∑ i ∈ range (n + 1 - k),
          ((-1 : ℝ) ^ k * d k) * (((-1 : ℝ) ^ i * ((k + i).choose k : ℝ)) / x ^ (k + 1 + i)))
        = Pnp1 x := by
      intro x
      rw [hPnp1x x,
        Finset.sum_congr rfl (fun k hk => Finset.sum_congr rfl (fun i hi => hG x k hk i hi)),
        triangle_regroup_aux,
        Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (fun k hk => htermP x m hm k hk)),
        Finset.sum_congr rfl (fun m hm => hinnerP x m hm)]
    have ha_fun : ∀ x : ℝ, Qsum x - Pnp1 x
        = ∑ k ∈ range (n + 1), ((-1 : ℝ) ^ k * d k)
          * ((1 / (x + 1) ^ (k + 1))
            - ∑ i ∈ range (n + 1 - k),
              (-1 : ℝ) ^ i * ((k + i).choose k : ℝ) / x ^ (k + 1 + i)) := by
      intro x
      rw [hQsumx x, ← hQS x, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      have hDk : (∑ i ∈ range (n + 1 - k), ((-1 : ℝ) ^ k * d k)
            * (((-1 : ℝ) ^ i * ((k + i).choose k : ℝ)) / x ^ (k + 1 + i)))
          = ((-1 : ℝ) ^ k * d k)
            * (∑ i ∈ range (n + 1 - k),
              (-1 : ℝ) ^ i * ((k + i).choose k : ℝ) / x ^ (k + 1 + i)) :=
        (Finset.mul_sum _ _ _).symm
      rw [hDk]
      ring
    have hAterm : ∀ k ∈ range (n + 1),
        (fun x : ℝ => ((-1 : ℝ) ^ k * d k)
          * ((1 / (x + 1) ^ (k + 1))
            - ∑ i ∈ range (n + 1 - k), (-1 : ℝ) ^ i * ((k + i).choose k : ℝ) / x ^ (k + 1 + i)))
        =O[atTop] (fun x => 1 / x ^ (n + 1 + 1)) := by
      intro k hk
      have hEk := expand_bigO_aux k (n + 1 - k)
      have hkM : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hbridge : n + 1 + 1 ≤ k + 1 + (n + 1 - k) := by omega
      have hEkT : (fun x : ℝ => (1 / (x + 1) ^ (k + 1))
            - ∑ i ∈ range (n + 1 - k), (-1 : ℝ) ^ i * ((k + i).choose k : ℝ) / x ^ (k + 1 + i))
          =O[atTop] (fun x => 1 / x ^ (n + 1 + 1)) :=
        hEk.trans (monomial_bigO_aux _ _ _ hbridge)
      have hC := (const_bigO_one_aux ((-1 : ℝ) ^ k * d k)).mul hEkT
      simpa using hC
    have hApart : (fun x : ℝ => Qsum x - Pnp1 x) =O[atTop] (fun x => 1 / x ^ (n + 1 + 1)) := by
      have hApartFun : (fun x : ℝ => Qsum x - Pnp1 x)
          = ∑ k ∈ range (n + 1), (fun x : ℝ => ((-1 : ℝ) ^ k * d k)
            * ((1 / (x + 1) ^ (k + 1))
              - ∑ i ∈ range (n + 1 - k),
                (-1 : ℝ) ^ i * ((k + i).choose k : ℝ) / x ^ (k + 1 + i))) := by
        funext x
        rw [ha_fun x, Finset.sum_apply]
      rw [hApartFun]
      exact Asymptotics.IsBigO.sum hAterm
    have hBpart : (fun x : ℝ => (chapter6Section13ExampleCSum (x + 1) - Pn (x + 1)) / (x + 1))
        =O[atTop] (fun x => 1 / x ^ (n + 1 + 1)) := by
      have hcomp : ((fun x : ℝ => chapter6Section13ExampleCSum x - Pn x) ∘ (fun x : ℝ => x + 1))
          =O[atTop] ((fun x : ℝ => 1 / x ^ (n + 1)) ∘ (fun x : ℝ => x + 1)) :=
        hRn.comp_tendsto (Filter.tendsto_atTop_add_const_right _ 1 Filter.tendsto_id)
      have hshift : (fun x : ℝ => 1 / (x + 1)) =O[atTop] (fun x => 1 / x) := by
        apply Asymptotics.IsBigOWith.isBigO
        apply Asymptotics.IsBigOWith.of_bound (c := 1)
        filter_upwards [eventually_ge_atTop 1] with x hx
        have hx0 : (0 : ℝ) < x := by linarith
        have e1 : ‖(1 : ℝ) / (x + 1)‖ = 1 / (x + 1) := by
          rw [norm_div, norm_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
        have e2 : ‖(1 : ℝ) / x‖ = 1 / x := by
          rw [norm_div, norm_one, Real.norm_eq_abs, abs_of_pos hx0]
        rw [e1, e2, one_mul]
        exact one_div_le_one_div_of_le hx0 (by linarith)
      have hmul := hcomp.mul hshift
      have hmid :
          (fun x : ℝ => (chapter6Section13ExampleCSum (x + 1) - Pn (x + 1)) * (1 / (x + 1)))
          =O[atTop] (fun x => (1 / (x + 1) ^ (n + 1)) * (1 / x)) :=
        hmul.congr (fun x => rfl) (fun x => rfl)
      have hfin : (fun x : ℝ => (1 / (x + 1) ^ (n + 1)) * (1 / x)) =O[atTop]
          (fun x => 1 / x ^ (n + 1 + 1)) := by
        apply Asymptotics.IsBigOWith.isBigO
        apply Asymptotics.IsBigOWith.of_bound (c := 1)
        filter_upwards [eventually_ge_atTop 1] with x hx
        have hx0 : (0 : ℝ) < x := by linarith
        have hpos : (0 : ℝ) < (1 / (x + 1) ^ (n + 1)) * (1 / x) :=
          mul_pos (div_pos one_pos (pow_pos (by linarith) _)) (div_pos one_pos hx0)
        have e1 : ‖(1 / (x + 1) ^ (n + 1)) * (1 / x)‖ = (1 / (x + 1) ^ (n + 1)) * (1 / x) := by
          rw [Real.norm_eq_abs, abs_of_pos hpos]
        have e2 : ‖(1 : ℝ) / x ^ (n + 1 + 1)‖ = 1 / x ^ (n + 1 + 1) := by
          rw [norm_div, norm_one, norm_pow, Real.norm_eq_abs, abs_of_pos hx0]
        rw [e1, e2, one_mul, div_mul_div_comm, one_mul]
        apply one_div_le_one_div_of_le (pow_pos hx0 _)
        have hle : x ^ (n + 1) ≤ (x + 1) ^ (n + 1) :=
          pow_le_pow_left₀ (le_of_lt hx0) (by linarith) _
        have hbridge : x ^ (n + 1 + 1) = x ^ (n + 1) * x := by
          have hnn : n + 1 + 1 = (n + 1) + 1 := rfl
          rw [hnn, pow_succ]
        rw [hbridge]
        exact mul_le_mul_of_nonneg_right hle (le_of_lt hx0)
      have hdiv : (fun x : ℝ => (chapter6Section13ExampleCSum (x + 1) - Pn (x + 1)) / (x + 1))
          = (fun x => (chapter6Section13ExampleCSum (x + 1) - Pn (x + 1)) * (1 / (x + 1))) := by
        funext x
        rw [div_eq_mul_one_div]
      rw [hdiv]
      exact hmid.trans hfin
    have hAsm := hApart.sub hBpart
    have hEv : (fun x : ℝ => chapter6Section13ExampleCSum x - Pnp1 x)
        =ᶠ[atTop] (fun x => (Qsum x - Pnp1 x)
          - ((chapter6Section13ExampleCSum (x + 1) - Pn (x + 1)) / (x + 1))) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      have hfunc := chapter6Section13ExampleCSum_eq x hx
      rw [hfunc, hQ x]
      ring
    exact hAsm.congr' hEv.symm Filter.EventuallyEq.rfl

/-- **Convergence and asymptotic expansion of Ramanujan's factorial series.** Let
$c_j(x) = (-1)^j / ((x + 1)(x + 2) \cdots (x + j + 1))$, let $C(x) = \sum_{j \ge 0} c_j(x)$,
and let $B_n$ denote the $n$-th Bell number. For all sufficiently large real $x$, $x > 0$ and the
series $\sum_{j \ge 0} c_j(x)$ is summable; and for every natural number $N$,
$$C(x) - \sum_{j=0}^{N-1} \frac{(-1)^j B_{j+1}}{x^{j+1}} = O\left(\frac{1}{x^{N+1}}\right)
\quad \text{as } x \to \infty.$$

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 6.
Proves `Wanted` entry `ramanujan_part1_ch6_entry5_digamma`.
-/
theorem ramanujan_part1_ch6_entry5_digamma :
    (∀ᶠ x : ℝ in atTop,
        0 < x ∧ Summable (chapter6Section13ExampleCTerm x)) ∧
      ∀ N : ℕ, Asymptotics.IsBigO atTop
        (fun x : ℝ => chapter6Section13ExampleCSum x -
          ∑ j ∈ range N,
            (-1 : ℝ) ^ j * ((j + 1).bell : ℝ) /
              x ^ (j + 1))
        (fun x : ℝ => 1 / x ^ (N + 1)) := by
  exact ⟨eventually_summable_aux, isBigO_chapter6Section13ExampleCSum_sub_sum_bell⟩

end

end Entry5Digamma

end MathlibExt.Analysis.Ramanujan.Part1Ch6
