/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Order.Monotone.Monovary
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Monovary
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Power sum inequalities for monotone sequences

Results from Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for
Monotone Sequences with Applications to Fibonacci Numbers*, INTEGERS 26
(2026), Article A101.

For a finite sequence `x` of positive reals, the paper's power sum is
`S_n^{[p]}(x) = ∑ x_k ^ p` (real exponent), and the weighted power sum is
`S_n^{[p]}(x; w) = ∑ w_k x_k ^ p` with total weight `W = ∑ w_k`. A sequence
`x_1 ≤ ⋯ ≤ x_n` with `n ≥ 1` terms is `x : Fin (n + 1) → ℝ`, so `x_n` is
`x (Fin.last n)` and the number of terms is `n + 1`. `F_k` is `Nat.fib k`.

The proofs go through statements about an arbitrary `Finset`, which serve the
unweighted results (weights `w ≡ 1`), the weighted ones and the Fibonacci
applications alike. These helpers are public and live in the namespaces
`MetaMathlibExt.Finset`, `MetaMathlibExt.Real` and `MetaMathlibExt.Nat`.

* `Real.sum_rpow_le_rpow_sum`: `∑ z_i ^ p ≤ (∑ z_i) ^ p` for `p ≥ 1` and
  `z_i ≥ 0` (induction from Mathlib's two-term `Real.add_rpow_le_rpow_add`).
  Applied to `z_i = x_i ^ β` it gives `Real.sum_rpow_le_rpow_sum_rpow`,
  `∑ x_i ^ α ≤ (∑ x_i ^ β) ^ (α / β)` for `0 < β ≤ α`, hence Proposition 1,
  Theorem 2(i) and Theorem 3(i).
* `Real.sum_mul_rpow_le_mul_rpow_div`, the weighted power mean inequality
  `∑ w_i x_i ^ α ≤ W (∑ w_i x_i ^ β / W) ^ (α / β)` for `0 < α ≤ β` (from
  Mathlib's `Real.rpow_arith_mean_le_arith_mean_rpow`), and
  `Real.mul_rpow_div_le_sum_mul_rpow`, the bound of the right side by
  `∑ w_i x_i ^ β` when every `x_i ≥ 1`. Together they give Theorem 2(ii),
  Theorem 3(ii), Theorem 4(ii) and Theorem 5(ii).
* `Real.sum_mul_rpow_mul_sum_mul_rpow_le`: for positive `x_i ≤ M`, weights
  `w_i ≥ 0` and `0 ≤ q ≤ p`,
  `(∑ w_i x_i ^ p) (∑ w_i x_i ^ q) ≤
    M ^ (p / 2) (∑ w_i x_i ^ (q / 2)) (∑ w_i x_i ^ ((p + q) / 2))`.
  It combines `x_i ^ p ≤ M ^ (p / 2) x_i ^ (p / 2)` with a weighted Chebyshev
  inequality (`MonovaryOn.sum_mul_mul_sum_mul_le_sum_mul_sum_mul_mul`).
  `Real.sum_mul_rpow_mul_sum_mul_rpow_div_max_le` applies it to the larger of
  the two exponents, which gives the lower bounds of Theorems 2 and 4. Of the
  monotonicity of `x`, these proofs use only that every `x_k` is positive and
  at most `x_n`.
* Lemma 1 parts (b)–(e) are proved over `ℕ` by induction on `n`, using
  `Nat.fib_add` and `Nat.fib_two_mul_add_one` for part (e). Part (g) is the
  case `m = 0` of `∑_{i=0}^n binom(n, i) F_{i+m} = F_{2n+m}`, proved by
  induction on `n` with Pascal's rule.
* Theorem 1 combines the Cauchy–Schwarz inequality
  `Finset.sum_mul_sq_le_sq_mul_sq` for `F_k ^ (r / 2)` and `F_k ^ (s / 2)`
  with `F_k ^ 2 ≤ F_k ^ ((r + s) / 2)` and `∑_{k=1}^n F_k ^ 2 = F_n F_{n+1}`
  (`Nat.sum_Icc_fib_sq`). For the equality case with `n ≥ 3`, Lagrange's
  identity (`Finset.sum_sum_mul_sub_mul_sq`) makes Cauchy–Schwarz strict
  unless `r = s` (compare `F_1 = 1` with `F_3 = 2`), and
  `F_3 ^ ((r + s) / 2) > F_3 ^ 2` unless `r + s = 4`.

Not formalized: Lemma 1 part (a), which is Mathlib's
`Nat.fib_succ_eq_succ_sum`, and Lemma 1 parts (f) and (h) and the lower
bounds of Theorems 3 and 5, whose extracted statements were judged garbled or
false and so were never stated.

## Main results

* `power_sum_rpow_one_div_le` (Proposition 1).
* `power_sum_mul_div_max_le` (Theorem 2, lower bound),
  `power_sum_le_rpow_of_le` (Theorem 2(i)),
  `power_sum_le_card_mul_rpow_of_lt` (Theorem 2(ii)).
* `sum_fib_rpow_le_of_two_le` (Theorem 3(i)),
  `sum_fib_rpow_le_card_mul_rpow` (Theorem 3(ii)).
* `weighted_power_sum_mul_div_max_le` (Theorem 4, lower bound),
  `weighted_power_sum_le_mul_rpow_of_lt` (Theorem 4(ii)).
* `weighted_sum_fib_rpow_le_mul_rpow` (Theorem 5(ii)).
* `fib_power_sum_identities` (Lemma 1 (b), (c), (d), (e), (g)).
* `sum_fib_rpow_mul_sum_fib_rpow_ge` (Theorem 1, with its equality case).

## References

* Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
  Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026),
  Article A101.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

variable {ι : Type*}

/-! ### Finite-sum inequalities -/

/-- **Lagrange's identity**: the defect in the Cauchy–Schwarz inequality is
half the sum of the squares `(f i * g j - f j * g i) ^ 2` over all ordered
pairs `(i, j)`. -/
theorem Finset.sum_sum_mul_sub_mul_sq {R : Type*} [CommRing R] (s : Finset ι)
    (f g : ι → R) :
    ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2 =
      2 * ((∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) -
        (∑ i ∈ s, f i * g i) ^ 2) := by
  have e : ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, f i ^ 2 * g j ^ 2 +
        ∑ i ∈ s, ∑ j ∈ s, f j ^ 2 * g i ^ 2 -
        2 * ∑ i ∈ s, ∑ j ∈ s, f i * g i * (f j * g j) := by
    simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  rw [e, sum_comm (s := s) (t := s) (f := fun i j => f j ^ 2 * g i ^ 2),
    ← sum_mul_sum, sq (∑ i ∈ s, f i * g i), ← sum_mul_sum]
  ring

/-- **Cauchy–Schwarz inequality, strict form**: if `f i * g j ≠ f j * g i`
for some `i, j ∈ s` (so that `f` and `g` are not proportional on `s`), then
`(∑ f g) ^ 2 < (∑ f ^ 2) (∑ g ^ 2)`. -/
theorem Finset.sum_mul_sq_lt_sq_mul_sq {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (s : Finset ι) (f g : ι → R) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (hne : f i * g j ≠ f j * g i) :
    (∑ k ∈ s, f k * g k) ^ 2 < (∑ k ∈ s, f k ^ 2) * ∑ k ∈ s, g k ^ 2 := by
  have hpos : 0 < ∑ a ∈ s, ∑ b ∈ s, (f a * g b - f b * g a) ^ 2 := by
    refine sum_pos' (fun a _ => sum_nonneg fun b _ => sq_nonneg _)
      ⟨i, hi, sum_pos' (fun b _ => sq_nonneg _) ⟨j, hj, ?_⟩⟩
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  rw [Finset.sum_sum_mul_sub_mul_sq] at hpos
  linarith

/-- **Chebyshev's sum inequality, weighted form**: if `f` and `g` monovary on
`s` and the weights `w` are nonnegative there, then
`(∑ w f) (∑ w g) ≤ (∑ w) (∑ w f g)`. -/
theorem MonovaryOn.sum_mul_mul_sum_mul_le_sum_mul_sum_mul_mul
    {f g w : ι → ℝ} {s : Finset ι} (hfg : MonovaryOn f g s)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * f i) * ∑ i ∈ s, w i * g i ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i * g i := by
  have e : ∑ i ∈ s, ∑ j ∈ s, w i * w j * ((f j - f i) * (g j - g i)) =
      2 * ((∑ i ∈ s, w i) * (∑ i ∈ s, w i * f i * g i) -
        (∑ i ∈ s, w i * f i) * ∑ i ∈ s, w i * g i) := by
    have e1 : ∑ i ∈ s, ∑ j ∈ s, w i * w j * ((f j - f i) * (g j - g i)) =
        ∑ i ∈ s, ∑ j ∈ s, w i * (w j * f j * g j) +
          ∑ i ∈ s, ∑ j ∈ s, w j * (w i * f i * g i) -
          ∑ i ∈ s, ∑ j ∈ s, w i * f i * (w j * g j) -
          ∑ i ∈ s, ∑ j ∈ s, w j * f j * (w i * g i) := by
      simp only [← sum_add_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
    rw [e1, sum_comm (s := s) (t := s)
        (f := fun i j => w j * (w i * f i * g i)),
      sum_comm (s := s) (t := s) (f := fun i j => w j * f j * (w i * g i)),
      ← sum_mul_sum, ← sum_mul_sum]
    ring
  have hnn : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, w i * w j * ((f j - f i) * (g j - g i)) :=
    sum_nonneg fun i hi => sum_nonneg fun j hj =>
      mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (hfg.sub_mul_sub_nonneg hi hj)
  linarith

/-- A finite sum of `p`-th powers, `p ≥ 1`, of nonnegative reals is at most
the `p`-th power of the sum: `∑ z_i ^ p ≤ (∑ z_i) ^ p`. -/
theorem Real.sum_rpow_le_rpow_sum (s : Finset ι) (z : ι → ℝ)
    (hz : ∀ i ∈ s, 0 ≤ z i) {p : ℝ} (hp : 1 ≤ p) :
    ∑ i ∈ s, z i ^ p ≤ (∑ i ∈ s, z i) ^ p := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [sum_empty, sum_empty, Real.zero_rpow (by linarith)]
  | cons a s ha ih =>
    rw [sum_cons, sum_cons]
    have hz' : ∀ i ∈ s, 0 ≤ z i := fun i hi => hz i (mem_cons_of_mem hi)
    calc z a ^ p + ∑ i ∈ s, z i ^ p ≤ z a ^ p + (∑ i ∈ s, z i) ^ p :=
          add_le_add le_rfl (ih hz')
      _ ≤ (z a + ∑ i ∈ s, z i) ^ p :=
          Real.add_rpow_le_rpow_add (hz a (mem_cons_self a s))
            (sum_nonneg hz') hp

/-- For nonnegative reals and `0 < β ≤ α`,
`∑ x_i ^ α ≤ (∑ x_i ^ β) ^ (α / β)`: the `ℓ^α` norm is at most the `ℓ^β`
norm. -/
theorem Real.sum_rpow_le_rpow_sum_rpow (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) {α β : ℝ} (hβ : 0 < β) (hβα : β ≤ α) :
    ∑ i ∈ s, x i ^ α ≤ (∑ i ∈ s, x i ^ β) ^ (α / β) := by
  have h := Real.sum_rpow_le_rpow_sum s (fun i => x i ^ β)
    (fun i hi => Real.rpow_nonneg (hx i hi) β)
    (p := α / β) ((one_le_div hβ).mpr hβα)
  refine le_of_eq_of_le (sum_congr rfl fun i hi => ?_) h
  rw [← Real.rpow_mul (hx i hi), mul_div_cancel₀ α hβ.ne']

/-- **Weighted power mean inequality** in the form used for power sums: for
nonnegative reals `x_i`, nonnegative weights `w_i` with `W = ∑ w_i > 0` and
`0 < α ≤ β`, `∑ w_i x_i ^ α ≤ W (∑ w_i x_i ^ β / W) ^ (α / β)`. -/
theorem Real.sum_mul_rpow_le_mul_rpow_div (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : 0 < ∑ i ∈ s, w i)
    (hx : ∀ i ∈ s, 0 ≤ x i) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∑ i ∈ s, w i * x i ^ α ≤
      (∑ i ∈ s, w i) * ((∑ i ∈ s, w i * x i ^ β) / ∑ i ∈ s, w i) ^ (α / β) := by
  set W := ∑ i ∈ s, w i
  have hβ : 0 < β := hα.trans_le hαβ
  have h := Real.rpow_arith_mean_le_arith_mean_rpow s (fun i => w i / W)
    (fun i => x i ^ α) (fun i hi => div_nonneg (hw i hi) hW.le)
    (by rw [← sum_div, div_self hW.ne'])
    (fun i hi => Real.rpow_nonneg (hx i hi) α) (p := β / α)
    ((one_le_div hα).mpr hαβ)
  have e1 : ∑ i ∈ s, w i / W * x i ^ α = (∑ i ∈ s, w i * x i ^ α) / W := by
    rw [sum_div]
    exact sum_congr rfl fun i _ => div_mul_eq_mul_div _ _ _
  have e2 : ∑ i ∈ s, w i / W * (x i ^ α) ^ (β / α) =
      (∑ i ∈ s, w i * x i ^ β) / W := by
    rw [sum_div]
    refine sum_congr rfl fun i hi => ?_
    rw [← Real.rpow_mul (hx i hi), mul_div_cancel₀ β hα.ne',
      div_mul_eq_mul_div]
  rw [e1, e2] at h
  have hA : 0 ≤ (∑ i ∈ s, w i * x i ^ α) / W :=
    div_nonneg (sum_nonneg fun i hi =>
      mul_nonneg (hw i hi) (Real.rpow_nonneg (hx i hi) α)) hW.le
  rw [← div_le_iff₀' hW]
  calc (∑ i ∈ s, w i * x i ^ α) / W =
        (((∑ i ∈ s, w i * x i ^ α) / W) ^ (β / α)) ^ (α / β) := by
        rw [← Real.rpow_mul hA, div_mul_div_cancel₀ hα.ne', div_self hβ.ne',
          Real.rpow_one]
    _ ≤ ((∑ i ∈ s, w i * x i ^ β) / W) ^ (α / β) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hA _) h (div_nonneg hα.le hβ.le)

/-- If every `x_i ≥ 1`, the weights `w_i` are nonnegative with `W = ∑ w_i > 0`
and `0 ≤ α ≤ β`, then `W (∑ w_i x_i ^ β / W) ^ (α / β) ≤ ∑ w_i x_i ^ β`. -/
theorem Real.mul_rpow_div_le_sum_mul_rpow (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : 0 < ∑ i ∈ s, w i)
    (hx : ∀ i ∈ s, 1 ≤ x i) {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) :
    (∑ i ∈ s, w i) * ((∑ i ∈ s, w i * x i ^ β) / ∑ i ∈ s, w i) ^ (α / β) ≤
      ∑ i ∈ s, w i * x i ^ β := by
  set W := ∑ i ∈ s, w i
  have hB : 1 ≤ (∑ i ∈ s, w i * x i ^ β) / W := by
    rw [one_le_div hW]
    exact sum_le_sum fun i hi => le_mul_of_one_le_right (hw i hi)
      (Real.one_le_rpow (hx i hi) (hα.trans hαβ))
  calc W * ((∑ i ∈ s, w i * x i ^ β) / W) ^ (α / β) ≤
        W * ((∑ i ∈ s, w i * x i ^ β) / W) ^ (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hB
          (div_le_one_of_le₀ hαβ (hα.trans hαβ))) hW.le
    _ = ∑ i ∈ s, w i * x i ^ β := by
        rw [Real.rpow_one, mul_div_cancel₀ _ hW.ne']

/-- The two-exponent inequality behind the lower bounds of Theorems 2 and 4
of Kovač and Pečarić: for positive reals `x_i ≤ M`, nonnegative weights `w_i`
and `0 ≤ q ≤ p`,
`(∑ w_i x_i ^ p) (∑ w_i x_i ^ q) ≤
  M ^ (p / 2) (∑ w_i x_i ^ (q / 2)) (∑ w_i x_i ^ ((p + q) / 2))`.
It combines `x_i ^ p ≤ M ^ (p / 2) x_i ^ (p / 2)` with the weighted Chebyshev
inequality for the similarly ordered `x_i ^ ((p - q) / 2)` and `x_i ^ (q / 2)`
under the weights `w_i x_i ^ (q / 2)`. -/
theorem Real.sum_mul_rpow_mul_sum_mul_rpow_le (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 < x i) {M : ℝ}
    (hM : ∀ i ∈ s, x i ≤ M) {p q : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p) :
    (∑ i ∈ s, w i * x i ^ p) * ∑ i ∈ s, w i * x i ^ q ≤
      M ^ (p / 2) * (∑ i ∈ s, w i * x i ^ (q / 2)) *
        ∑ i ∈ s, w i * x i ^ ((p + q) / 2) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp only [sum_empty, mul_zero, le_refl]
  have hM0 : 0 ≤ M := (hx i₀ hi₀).le.trans (hM i₀ hi₀)
  have hp : 0 ≤ p := hq.trans hqp
  -- Step 1: `x_i ^ p ≤ M ^ (p / 2) x_i ^ (p / 2)`.
  have h1 : ∑ i ∈ s, w i * x i ^ p ≤
      M ^ (p / 2) * ∑ i ∈ s, w i * x i ^ (p / 2) := by
    rw [mul_sum]
    refine sum_le_sum fun i hi => ?_
    have hxi := hx i hi
    calc w i * x i ^ p = w i * x i ^ (p / 2) * x i ^ (p / 2) := by
          rw [mul_assoc, ← Real.rpow_add hxi, add_halves]
      _ ≤ w i * x i ^ (p / 2) * M ^ (p / 2) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hxi.le (hM i hi) (by linarith))
            (mul_nonneg (hw i hi) (Real.rpow_nonneg hxi.le _))
      _ = M ^ (p / 2) * (w i * x i ^ (p / 2)) := mul_comm _ _
  -- Step 2: weighted Chebyshev.
  have hmono : MonovaryOn (fun i => x i ^ ((p - q) / 2))
      (fun i => x i ^ (q / 2)) s := by
    intro i hi j hj hlt
    have hxij : x i ≤ x j := by
      by_contra hcon
      exact absurd hlt (not_lt.mpr
        (Real.rpow_le_rpow (hx j hj).le (le_of_not_ge hcon) (by linarith)))
    exact Real.rpow_le_rpow (hx i hi).le hxij (by linarith)
  have h2 := MonovaryOn.sum_mul_mul_sum_mul_le_sum_mul_sum_mul_mul hmono
    (w := fun i => w i * x i ^ (q / 2))
    (fun i hi => mul_nonneg (hw i hi) (Real.rpow_nonneg (hx i hi).le _))
  have ea : ∀ i ∈ s, w i * x i ^ (q / 2) * x i ^ ((p - q) / 2) =
      w i * x i ^ (p / 2) := fun i hi => by
    rw [mul_assoc, ← Real.rpow_add (hx i hi),
      show q / 2 + (p - q) / 2 = p / 2 by ring]
  have eb : ∀ i ∈ s, w i * x i ^ (q / 2) * x i ^ (q / 2) = w i * x i ^ q :=
    fun i hi => by rw [mul_assoc, ← Real.rpow_add (hx i hi), add_halves]
  have ec : ∀ i ∈ s, w i * x i ^ (q / 2) * x i ^ ((p - q) / 2) *
      x i ^ (q / 2) = w i * x i ^ ((p + q) / 2) := fun i hi => by
    rw [ea i hi, mul_assoc, ← Real.rpow_add (hx i hi),
      show p / 2 + q / 2 = (p + q) / 2 by ring]
  rw [sum_congr rfl ea, sum_congr rfl eb, sum_congr rfl ec] at h2
  have hq0 : 0 ≤ ∑ i ∈ s, w i * x i ^ q :=
    sum_nonneg fun i hi =>
      mul_nonneg (hw i hi) (Real.rpow_nonneg (hx i hi).le _)
  calc (∑ i ∈ s, w i * x i ^ p) * ∑ i ∈ s, w i * x i ^ q ≤
        (M ^ (p / 2) * ∑ i ∈ s, w i * x i ^ (p / 2)) *
          ∑ i ∈ s, w i * x i ^ q := mul_le_mul_of_nonneg_right h1 hq0
    _ = M ^ (p / 2) * ((∑ i ∈ s, w i * x i ^ (p / 2)) *
          ∑ i ∈ s, w i * x i ^ q) := mul_assoc _ _ _
    _ ≤ M ^ (p / 2) * ((∑ i ∈ s, w i * x i ^ (q / 2)) *
          ∑ i ∈ s, w i * x i ^ ((p + q) / 2)) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hM0 _)
    _ = _ := (mul_assoc _ _ _).symm

/-- The lower bound of Theorems 2 and 4 of Kovač and Pečarić for a finite
family: for positive reals `x_i ≤ M`, nonnegative weights `w_i` and
`p, q ≥ 0`,
`(∑ w_i x_i ^ p) (∑ w_i x_i ^ q) /
  max (M ^ (p / 2) ∑ w_i x_i ^ (q / 2), M ^ (q / 2) ∑ w_i x_i ^ (p / 2)) ≤
  ∑ w_i x_i ^ ((p + q) / 2)`.
Apply `Real.sum_mul_rpow_mul_sum_mul_rpow_le` to whichever of `p, q` is
larger. -/
theorem Real.sum_mul_rpow_mul_sum_mul_rpow_div_max_le (s : Finset ι)
    (w x : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 < x i) {M : ℝ}
    (hM : ∀ i ∈ s, x i ≤ M) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (∑ i ∈ s, w i * x i ^ p) * (∑ i ∈ s, w i * x i ^ q) /
        max (M ^ (p / 2) * ∑ i ∈ s, w i * x i ^ (q / 2))
          (M ^ (q / 2) * ∑ i ∈ s, w i * x i ^ (p / 2)) ≤
      ∑ i ∈ s, w i * x i ^ ((p + q) / 2) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp only [sum_empty, mul_zero, zero_div, le_refl]
  have hM0 : 0 ≤ M := (hx i₀ hi₀).le.trans (hM i₀ hi₀)
  have hS : ∀ t : ℝ, 0 ≤ ∑ i ∈ s, w i * x i ^ t := fun t =>
    sum_nonneg fun i hi =>
      mul_nonneg (hw i hi) (Real.rpow_nonneg (hx i hi).le _)
  have hmax : 0 ≤ max (M ^ (p / 2) * ∑ i ∈ s, w i * x i ^ (q / 2))
      (M ^ (q / 2) * ∑ i ∈ s, w i * x i ^ (p / 2)) :=
    (mul_nonneg (Real.rpow_nonneg hM0 _) (hS _)).trans (le_max_left _ _)
  refine div_le_of_le_mul₀ hmax (hS _) ?_
  rcases le_total q p with h | h
  · calc (∑ i ∈ s, w i * x i ^ p) * (∑ i ∈ s, w i * x i ^ q) ≤
          M ^ (p / 2) * (∑ i ∈ s, w i * x i ^ (q / 2)) *
            ∑ i ∈ s, w i * x i ^ ((p + q) / 2) :=
          Real.sum_mul_rpow_mul_sum_mul_rpow_le s w x hw hx hM hq h
      _ ≤ _ := by
          rw [mul_comm (∑ i ∈ s, w i * x i ^ ((p + q) / 2))]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hS _)
  · calc (∑ i ∈ s, w i * x i ^ p) * (∑ i ∈ s, w i * x i ^ q) =
          (∑ i ∈ s, w i * x i ^ q) * (∑ i ∈ s, w i * x i ^ p) := mul_comm _ _
      _ ≤ M ^ (q / 2) * (∑ i ∈ s, w i * x i ^ (p / 2)) *
            ∑ i ∈ s, w i * x i ^ ((q + p) / 2) :=
          Real.sum_mul_rpow_mul_sum_mul_rpow_le s w x hw hx hM hp h
      _ ≤ _ := by
          rw [add_comm q p, mul_comm (∑ i ∈ s, w i * x i ^ ((p + q) / 2))]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (hS _)

/-! ### Fibonacci sums -/

/-- The sum of the squares of the first `n` Fibonacci numbers:
`∑_{k=1}^n F_k ^ 2 = F_n F_{n+1}`. -/
theorem Nat.sum_Icc_fib_sq (n : ℕ) :
    ∑ k ∈ Icc 1 n, Nat.fib k ^ 2 = Nat.fib n * Nat.fib (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), ih, Nat.fib_add_two]
    ring

/-- `∑_{i=1}^n F_{2i-1} = F_{2n}`. -/
theorem Nat.sum_Icc_fib_two_mul_sub_one (n : ℕ) :
    ∑ i ∈ Icc 1 n, Nat.fib (2 * i - 1) = Nat.fib (2 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), ih,
      show 2 * (n + 1) - 1 = 2 * n + 1 by omega,
      show 2 * (n + 1) = 2 * n + 2 by ring, Nat.fib_add_two]

/-- `∑_{i=1}^n F_{2i} + 1 = F_{2n+1}`. -/
theorem Nat.sum_Icc_fib_two_mul_add_one (n : ℕ) :
    ∑ i ∈ Icc 1 n, Nat.fib (2 * i) + 1 = Nat.fib (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), add_right_comm, ih,
      show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, Nat.fib_add_two,
      show 2 * n + 1 + 1 = 2 * (n + 1) by ring]

/-- `∑_{i=1}^n i F_i + F_{n+3} = n F_{n+2} + 2`. -/
theorem Nat.sum_Icc_mul_fib_add_fib (n : ℕ) :
    ∑ i ∈ Icc 1 n, i * Nat.fib i + Nat.fib (n + 3) =
      n * Nat.fib (n + 2) + 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega)]
    have h3 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) :=
      Nat.fib_add_two
    have h4 : Nat.fib (n + 1 + 3) = Nat.fib (n + 2) + Nat.fib (n + 3) :=
      Nat.fib_add_two
    rw [h4, show n + 1 + 2 = n + 3 by ring]
    rw [h3] at ih ⊢
    nlinarith [ih]

/-- `∑_{i=1}^n F_i F_{3i} = F_n F_{n+1} F_{2n+1}`. -/
theorem Nat.sum_Icc_fib_mul_fib_three_mul (n : ℕ) :
    ∑ i ∈ Icc 1 n, Nat.fib i * Nat.fib (3 * i) =
      Nat.fib n * Nat.fib (n + 1) * Nat.fib (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    have h2 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    have hodd : Nat.fib (2 * n + 1) = Nat.fib (n + 1) ^ 2 + Nat.fib n ^ 2 :=
      Nat.fib_two_mul_add_one n
    have hodd' : Nat.fib (2 * (n + 1) + 1) =
        Nat.fib (n + 2) ^ 2 + Nat.fib (n + 1) ^ 2 :=
      Nat.fib_two_mul_add_one (n + 1)
    have heven : Nat.fib (2 * n + 2) =
        Nat.fib n * Nat.fib (n + 1) + Nat.fib (n + 1) * Nat.fib (n + 2) := by
      rw [show 2 * n + 2 = n + (n + 1) + 1 by ring, Nat.fib_add]
    have htriple : Nat.fib (3 * (n + 1)) =
        Nat.fib (n + 1) * Nat.fib (2 * n + 1) +
          Nat.fib (n + 2) * Nat.fib (2 * n + 2) := by
      rw [show 3 * (n + 1) = n + 1 + (2 * n + 1) + 1 by ring, Nat.fib_add]
    rw [htriple, heven, hodd', hodd, h2]
    ring

/-- `∑_{i=0}^n binom(n, i) F_{i+m} = F_{2n+m}`. -/
theorem Nat.sum_range_choose_mul_fib_add (n m : ℕ) :
    ∑ i ∈ range (n + 1), n.choose i * Nat.fib (i + m) =
      Nat.fib (2 * n + m) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    have h2 : ∑ i ∈ range (n + 2), n.choose i * Nat.fib (i + m) =
        Nat.fib (2 * n + m) := by
      rw [sum_range_succ, ih, Nat.choose_succ_self, zero_mul, add_zero]
    rw [sum_range_succ'] at h2
    have h1 := ih (m + 1)
    rw [sum_range_succ']
    simp only [Nat.choose_succ_succ, add_mul, sum_add_distrib,
      Nat.choose_zero_right] at h2 ⊢
    have e : ∀ i, Nat.fib (i + 1 + m) = Nat.fib (i + (m + 1)) := fun i => by
      rw [add_assoc, add_comm 1 m]
    simp only [e] at h2 ⊢
    rw [add_assoc, h2, h1, show 2 * (n + 1) + m = 2 * n + m + 2 by ring,
      Nat.fib_add_two, add_comm, ← add_assoc]

/-- `∑_{i=1}^n binom(n, i) F_i = F_{2n}`. -/
theorem Nat.sum_Icc_choose_mul_fib (n : ℕ) :
    ∑ i ∈ Icc 1 n, n.choose i * Nat.fib i = Nat.fib (2 * n) := by
  have h := Nat.sum_range_choose_mul_fib_add n 0
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos n)] at h
  simpa only [Nat.fib_zero, mul_zero, zero_add, add_zero, Nat.succ_eq_add_one,
    Ico_add_one_right_eq_Icc] using h

/-- `∑_{k=1}^n F_k ^ 2 = F_n F_{n+1}` with real squares `rpow`. -/
theorem Nat.sum_Icc_fib_rpow_two (n : ℕ) :
    ∑ k ∈ Icc 1 n, (Nat.fib k : ℝ) ^ (2 : ℝ) = Nat.fib n * Nat.fib (n + 1) := by
  simp only [Real.rpow_two]
  exact_mod_cast Nat.sum_Icc_fib_sq n

/-- `F_k ≥ 1` for `1 ≤ k`, as a real number. -/
private theorem one_le_fib_of_mem_Icc {n k : ℕ} (hk : k ∈ Icc 1 n) :
    1 ≤ (Nat.fib k : ℝ) :=
  Nat.one_le_cast.mpr (Nat.fib_pos.mpr (mem_Icc.mp hk).1)

/-! ### Power sums -/

/-- Power sums of a nonnegative finite sequence are monotone in the exponent
after normalisation: if `α > β > 0` then
`(∑ x_k ^ α) ^ (1 / α) ≤ (∑ x_k ^ β) ^ (1 / β)`.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026),
Article A101, Proposition 1 (`integers-2026-A101-prop-1`).

Proves `Wanted` entry `power_sum_rpow_one_div_le`. -/
theorem power_sum_rpow_one_div_le {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) {α β : ℝ} (hβ : 0 < β) (hβα : β < α) :
    (∑ i, x i ^ α) ^ (1 / α) ≤ (∑ i, x i ^ β) ^ (1 / β) := by
  have hα : 0 < α := hβ.trans hβα
  have h := Real.sum_rpow_le_rpow_sum_rpow univ x (fun i _ => (hx i).le) hβ
    hβα.le
  have hS : 0 ≤ ∑ i, x i ^ β :=
    sum_nonneg fun i _ => Real.rpow_nonneg (hx i).le β
  calc (∑ i, x i ^ α) ^ (1 / α) ≤
        ((∑ i, x i ^ β) ^ (α / β)) ^ (1 / α) :=
        Real.rpow_le_rpow
          (sum_nonneg fun i _ => Real.rpow_nonneg (hx i).le α) h
          (one_div_nonneg.mpr hα.le)
    _ = (∑ i, x i ^ β) ^ (1 / β) := by
        rw [← Real.rpow_mul hS]
        congr 1
        field_simp

/-- Lower bound of Theorem 2: for `0 < x_1 ≤ ⋯ ≤ x_n`, `r, s > 0` and
`α = (r + s) / 2`,
`S^{[r]} S^{[s]} / max (x_n ^ (r/2) S^{[s/2]}, x_n ^ (s/2) S^{[r/2]})
≤ S^{[α]}`.
The paper states it in both cases `α ≥ β` and `α < β`; it does not involve
`β`.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026),
Article A101, Theorem 2 (`integers-2026-A101-thm-2`).

Proves `Wanted` entry `power_sum_mul_div_max_le`. -/
theorem power_sum_mul_div_max_le {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : Monotone x) (h0 : 0 < x 0) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (∑ i, x i ^ r) * (∑ i, x i ^ s) /
        max (x (Fin.last n) ^ (r / 2) * ∑ i, x i ^ (s / 2))
          (x (Fin.last n) ^ (s / 2) * ∑ i, x i ^ (r / 2)) ≤
      ∑ i, x i ^ ((r + s) / 2) := by
  simpa only [one_mul] using Real.sum_mul_rpow_mul_sum_mul_rpow_div_max_le univ
    (fun _ => 1) x (fun _ _ => zero_le_one)
    (fun i _ => h0.trans_le (hx (Fin.zero_le i)))
    (fun i _ => hx (Fin.le_last i)) hr.le hs.le

/-- Upper bound of Theorem 2(i): for positive `x_k` and `0 < β ≤ α`,
`S^{[α]} ≤ (S^{[β]}) ^ (α / β)` (in the paper `α = (r + s) / 2` with
`r, s > 0`, and the sequence is monotone; neither is needed here).

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026),
Article A101, Theorem 2(i) (`integers-2026-A101-thm-2`).

Proves `Wanted` entry `power_sum_le_rpow_of_le`. -/
theorem power_sum_le_rpow_of_le {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : ∀ i, 0 < x i) {α β : ℝ} (hβ : 0 < β) (hβα : β ≤ α) :
    ∑ i, x i ^ α ≤ (∑ i, x i ^ β) ^ (α / β) :=
  Real.sum_rpow_le_rpow_sum_rpow univ x (fun i _ => (hx i).le) hβ hβα

/-- Upper bounds of Theorem 2(ii): for positive `x_k` and `0 < α < β`,
`S^{[α]} ≤ n (S^{[β]} / n) ^ (α / β)`, and if moreover every `x_k ≥ 1` then
`n (S^{[β]} / n) ^ (α / β) ≤ S^{[β]}` (here `n` is the number of terms,
`n + 1` in Lean; in the paper `α = (r + s) / 2` and the sequence is monotone,
so `x_k ≥ 1` is the paper's `x_1 ≥ 1`).

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026),
Article A101, Theorem 2(ii), including (4) (`integers-2026-A101-thm-2`).

Proves `Wanted` entry `power_sum_le_card_mul_rpow_of_lt`. -/
theorem power_sum_le_card_mul_rpow_of_lt {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : ∀ i, 0 < x i) {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ∑ i, x i ^ α ≤
        ((n : ℝ) + 1) * ((∑ i, x i ^ β) / ((n : ℝ) + 1)) ^ (α / β) ∧
      ((∀ i, 1 ≤ x i) →
        ((n : ℝ) + 1) * ((∑ i, x i ^ β) / ((n : ℝ) + 1)) ^ (α / β) ≤
          ∑ i, x i ^ β) := by
  have hW : ∑ _i : Fin (n + 1), (1 : ℝ) = (n : ℝ) + 1 := by
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      Nat.cast_add, Nat.cast_one]
  have hW0 : 0 < ∑ _i : Fin (n + 1), (1 : ℝ) := by
    rw [hW]
    positivity
  have h1 := Real.sum_mul_rpow_le_mul_rpow_div univ (fun _ => 1) x
    (fun _ _ => zero_le_one) hW0 (fun i _ => (hx i).le) hα hαβ.le
  have h2 := fun (h : ∀ i, 1 ≤ x i) =>
    Real.mul_rpow_div_le_sum_mul_rpow univ (fun _ => 1) x
    (fun _ _ => zero_le_one) hW0 (fun i (_ : i ∈ univ) => h i) hα.le hαβ.le
  simp only [one_mul, hW] at h1 h2
  exact ⟨h1, h2⟩

set_option linter.unusedVariables false in
/-- Upper bounds of Theorem 3 for Fibonacci numbers, with `α = (r + s) / 2`:
if `α ≥ 2` then `∑_{k=1}^n F_k ^ α ≤ (F_n F_{n+1}) ^ (α / 2)`.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026),
Article A101, Theorem 3(i) (`integers-2026-A101-thm-3`).

Proves `Wanted` entry `sum_fib_rpow_le_of_two_le`. The hypothesis `hn` is
unused (both sides vanish at `n = 0`) and keeps the source's shape. -/
theorem sum_fib_rpow_le_of_two_le {n : ℕ} (hn : 1 ≤ n) {α : ℝ}
    (hα : 2 ≤ α) :
    ∑ k ∈ Finset.Icc 1 n, (Nat.fib k : ℝ) ^ α ≤
      ((Nat.fib n : ℝ) * Nat.fib (n + 1)) ^ (α / 2) := by
  rw [← Nat.sum_Icc_fib_rpow_two]
  exact Real.sum_rpow_le_rpow_sum_rpow _ _ (fun k _ => Nat.cast_nonneg _)
    two_pos hα

/-- Upper bounds of Theorem 3(ii) for Fibonacci numbers, with
`α = (r + s) / 2`: if `0 < α < 2` then
`∑_{k=1}^n F_k ^ α ≤ n (F_n F_{n+1} / n) ^ (α / 2) ≤ F_n F_{n+1}`.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026),
Article A101, Theorem 3(ii) (`integers-2026-A101-thm-3`).

Proves `Wanted` entry `sum_fib_rpow_le_card_mul_rpow`. -/
theorem sum_fib_rpow_le_card_mul_rpow {n : ℕ} (hn : 1 ≤ n) {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) :
    ∑ k ∈ Finset.Icc 1 n, (Nat.fib k : ℝ) ^ α ≤
        (n : ℝ) * ((Nat.fib n : ℝ) * Nat.fib (n + 1) / n) ^ (α / 2) ∧
      (n : ℝ) * ((Nat.fib n : ℝ) * Nat.fib (n + 1) / n) ^ (α / 2) ≤
        (Nat.fib n : ℝ) * Nat.fib (n + 1) := by
  have hW : ∑ _k ∈ Icc 1 n, (1 : ℝ) = n := by
    rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  have hW0 : 0 < ∑ _k ∈ Icc 1 n, (1 : ℝ) := by
    rw [hW]
    exact_mod_cast hn
  have h1 := Real.sum_mul_rpow_le_mul_rpow_div (Icc 1 n) (fun _ => 1)
    (fun k => (Nat.fib k : ℝ)) (fun _ _ => zero_le_one) hW0
    (fun k _ => Nat.cast_nonneg _) hα hα2.le
  have h2 := Real.mul_rpow_div_le_sum_mul_rpow (Icc 1 n) (fun _ => 1)
    (fun k => (Nat.fib k : ℝ)) (fun _ _ => zero_le_one) hW0
    (fun _ hk => one_le_fib_of_mem_Icc hk) hα.le hα2.le
  simp only [one_mul, hW, Nat.sum_Icc_fib_rpow_two] at h1 h2
  exact ⟨h1, h2⟩

/-- Lower bound (6), (7) of Theorem 4 (weighted): for `0 < x_1 ≤ ⋯ ≤ x_n`,
weights `w_k > 0`, `r, s > 0` and `α = (r + s) / 2`,
`S^{[r]}(x;w) S^{[s]}(x;w) /
max (x_n ^ (r/2) S^{[s/2]}(x;w), x_n ^ (s/2) S^{[r/2]}(x;w))
≤ S^{[α]}(x;w)`, where `S^{[p]}(x;w) = ∑ w_k x_k ^ p`.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026),
Article A101, Theorem 4 (`integers-2026-A101-thm-4`).

Proves `Wanted` entry `weighted_power_sum_mul_div_max_le`. -/
theorem weighted_power_sum_mul_div_max_le {n : ℕ} (x w : Fin (n + 1) → ℝ)
    (hx : Monotone x) (h0 : 0 < x 0) (hw : ∀ i, 0 < w i) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) :
    (∑ i, w i * x i ^ r) * (∑ i, w i * x i ^ s) /
        max (x (Fin.last n) ^ (r / 2) * ∑ i, w i * x i ^ (s / 2))
          (x (Fin.last n) ^ (s / 2) * ∑ i, w i * x i ^ (r / 2)) ≤
      ∑ i, w i * x i ^ ((r + s) / 2) :=
  Real.sum_mul_rpow_mul_sum_mul_rpow_div_max_le univ w x (fun i _ => (hw i).le)
    (fun i _ => h0.trans_le (hx (Fin.zero_le i)))
    (fun i _ => hx (Fin.le_last i)) hr.le hs.le

/-- Upper bounds (7), (8) of Theorem 4(ii) (weighted): for positive `x_k`,
weights `w_k > 0` with `W = ∑ w_k` and `0 < α < β`,
`S^{[α]}(x;w) ≤ W (S^{[β]}(x;w) / W) ^ (α / β)`, and if moreover every
`x_k ≥ 1` then `W (S^{[β]}(x;w) / W) ^ (α / β) ≤ S^{[β]}(x;w)` (in the paper
`α = (r + s) / 2` and the sequence is monotone).

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026),
Article A101, Theorem 4(ii) (`integers-2026-A101-thm-4`).

Proves `Wanted` entry `weighted_power_sum_le_mul_rpow_of_lt`. -/
theorem weighted_power_sum_le_mul_rpow_of_lt {n : ℕ}
    (x w : Fin (n + 1) → ℝ) (hx : ∀ i, 0 < x i) (hw : ∀ i, 0 < w i)
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ∑ i, w i * x i ^ α ≤
        (∑ i, w i) * ((∑ i, w i * x i ^ β) / ∑ i, w i) ^ (α / β) ∧
      ((∀ i, 1 ≤ x i) →
        (∑ i, w i) * ((∑ i, w i * x i ^ β) / ∑ i, w i) ^ (α / β) ≤
          ∑ i, w i * x i ^ β) := by
  have hW0 : 0 < ∑ i, w i := sum_pos (fun i _ => hw i) univ_nonempty
  exact ⟨Real.sum_mul_rpow_le_mul_rpow_div univ w x (fun i _ => (hw i).le) hW0
      (fun i _ => (hx i).le) hα hαβ.le,
    fun h => Real.mul_rpow_div_le_sum_mul_rpow univ w x
      (fun i _ => (hw i).le) hW0 (fun i _ => h i) hα.le hαβ.le⟩

/-- Upper bounds of Theorem 5(ii) (weighted Fibonacci), with
`α = (r + s) / 2`: for weights `w_k > 0`, `W = ∑_{k=1}^n w_k` and
`0 < α < 2`,
`∑ w_k F_k ^ α ≤ W (∑ w_k F_k ^ 2 / W) ^ (α / 2) ≤ ∑ w_k F_k ^ 2`.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026),
Article A101, Theorem 5(ii) (`integers-2026-A101-thm-5`).

Proves `Wanted` entry `weighted_sum_fib_rpow_le_mul_rpow`. -/
theorem weighted_sum_fib_rpow_le_mul_rpow {n : ℕ} (hn : 1 ≤ n) (w : ℕ → ℝ)
    (hw : ∀ k ∈ Finset.Icc 1 n, 0 < w k) {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) :
    ∑ k ∈ Finset.Icc 1 n, w k * (Nat.fib k : ℝ) ^ α ≤
        (∑ k ∈ Finset.Icc 1 n, w k) *
          ((∑ k ∈ Finset.Icc 1 n, w k * (Nat.fib k : ℝ) ^ (2 : ℝ)) /
            ∑ k ∈ Finset.Icc 1 n, w k) ^ (α / 2) ∧
      (∑ k ∈ Finset.Icc 1 n, w k) *
          ((∑ k ∈ Finset.Icc 1 n, w k * (Nat.fib k : ℝ) ^ (2 : ℝ)) /
            ∑ k ∈ Finset.Icc 1 n, w k) ^ (α / 2) ≤
        ∑ k ∈ Finset.Icc 1 n, w k * (Nat.fib k : ℝ) ^ (2 : ℝ) := by
  have hW0 : 0 < ∑ k ∈ Icc 1 n, w k :=
    sum_pos hw (nonempty_Icc.mpr hn)
  exact ⟨Real.sum_mul_rpow_le_mul_rpow_div (Icc 1 n) w
      (fun k => (Nat.fib k : ℝ)) (fun k hk => (hw k hk).le) hW0
      (fun k _ => Nat.cast_nonneg _) hα hα2.le,
    Real.mul_rpow_div_le_sum_mul_rpow (Icc 1 n) w (fun k => (Nat.fib k : ℝ))
      (fun k hk => (hw k hk).le) hW0 (fun _ hk => one_le_fib_of_mem_Icc hk)
      hα.le hα2.le⟩

set_option linter.unusedVariables false in
/-- Classical Fibonacci sums quoted in Lemma 1 (from Koshy): for `n ≥ 1`,
(b) `∑_{i=1}^n F_{2i-1} = F_{2n}`, (c) `∑_{i=1}^n F_{2i} = F_{2n+1} - 1`,
(d) `∑_{i=1}^n i F_i = n F_{n+2} - F_{n+3} + 2`,
(e) `∑_{i=1}^n F_i F_{3i} = F_n F_{n+1} F_{2n+1}`,
(g) `∑_{i=1}^n binom(n,i) F_i = F_{2n}`, over `ℤ`. Part (a),
`∑ F_i = F_{n+2} - 1`, is Mathlib's `Nat.fib_succ_eq_succ_sum` and is not
restated; parts (f) and (h) are omitted because their extracted text is
garbled.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026),
Article A101, Lemma 1 (`integers-2026-A101-lem-1`).

Proves `Wanted` entry `fib_power_sum_identities`. The hypothesis `hn` is
unused (all five identities also hold at `n = 0`) and keeps the source's
shape. -/
theorem fib_power_sum_identities {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ Finset.Icc 1 n, (Nat.fib (2 * i - 1) : ℤ)) = Nat.fib (2 * n) ∧
    (∑ i ∈ Finset.Icc 1 n, (Nat.fib (2 * i) : ℤ)) =
      Nat.fib (2 * n + 1) - 1 ∧
    (∑ i ∈ Finset.Icc 1 n, (i : ℤ) * Nat.fib i) =
      n * Nat.fib (n + 2) - Nat.fib (n + 3) + 2 ∧
    (∑ i ∈ Finset.Icc 1 n, (Nat.fib i : ℤ) * Nat.fib (3 * i)) =
      Nat.fib n * Nat.fib (n + 1) * Nat.fib (2 * n + 1) ∧
    (∑ i ∈ Finset.Icc 1 n, (n.choose i : ℤ) * Nat.fib i) =
      Nat.fib (2 * n) := by
  have hc : ((∑ i ∈ Icc 1 n, Nat.fib (2 * i) + 1 : ℕ) : ℤ) =
      Nat.fib (2 * n + 1) := congrArg _ (Nat.sum_Icc_fib_two_mul_add_one n)
  have hd : ((∑ i ∈ Icc 1 n, i * Nat.fib i + Nat.fib (n + 3) : ℕ) : ℤ) =
      ((n * Nat.fib (n + 2) + 2 : ℕ) : ℤ) :=
    congrArg _ (Nat.sum_Icc_mul_fib_add_fib n)
  push_cast at hc hd
  refine ⟨by exact_mod_cast Nat.sum_Icc_fib_two_mul_sub_one n, by linarith,
    by linarith, by exact_mod_cast Nat.sum_Icc_fib_mul_fib_three_mul n,
    by exact_mod_cast Nat.sum_Icc_choose_mul_fib n⟩

/-- For real `r, s` with `r + s ≥ 4` and `n ≥ 1`,
`(∑_{k=1}^n F_k^r)(∑_{k=1}^n F_k^s) ≥ (F_n F_{n+1})²`, with equality if and
only if `n = 1`, `n = 2`, or `n ≥ 3` and `r = s = 2`. Quoted in the paper
from its reference [2]; powers are real powers `rpow`.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026),
Article A101, Theorem 1 (`integers-2026-A101-thm-1`).

Proves `Wanted` entry `sum_fib_rpow_mul_sum_fib_rpow_ge`. -/
theorem sum_fib_rpow_mul_sum_fib_rpow_ge {n : ℕ} (hn : 1 ≤ n) {r s : ℝ}
    (hrs : 4 ≤ r + s) :
    ((Nat.fib n : ℝ) * Nat.fib (n + 1)) ^ 2 ≤
        (∑ k ∈ Finset.Icc 1 n, (Nat.fib k : ℝ) ^ r) *
          ∑ k ∈ Finset.Icc 1 n, (Nat.fib k : ℝ) ^ s ∧
      ((∑ k ∈ Finset.Icc 1 n, (Nat.fib k : ℝ) ^ r) *
            ∑ k ∈ Finset.Icc 1 n, (Nat.fib k : ℝ) ^ s =
          ((Nat.fib n : ℝ) * Nat.fib (n + 1)) ^ 2 ↔
        n = 1 ∨ n = 2 ∨ (3 ≤ n ∧ r = 2 ∧ s = 2)) := by
  have hF0 : ∀ k ∈ Icc 1 n, 0 < (Nat.fib k : ℝ) := fun k hk =>
    one_pos.trans_le (one_le_fib_of_mem_Icc hk)
  have hα : 2 ≤ (r + s) / 2 := by linarith
  -- Cauchy–Schwarz for `F_k ^ (r / 2)` and `F_k ^ (s / 2)`.
  have hfg : ∀ k ∈ Icc 1 n, (Nat.fib k : ℝ) ^ (r / 2) *
      (Nat.fib k : ℝ) ^ (s / 2) = (Nat.fib k : ℝ) ^ ((r + s) / 2) :=
    fun k hk => by rw [← Real.rpow_add (hF0 k hk), add_div]
  have hsq : ∀ (k : ℕ) (t : ℝ), ((Nat.fib k : ℝ) ^ (t / 2)) ^ 2 =
      (Nat.fib k : ℝ) ^ t := fun k t => by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _), Nat.cast_ofNat,
      div_mul_cancel₀ t two_ne_zero]
  have hCS := sum_mul_sq_le_sq_mul_sq (Icc 1 n)
    (fun k => (Nat.fib k : ℝ) ^ (r / 2)) (fun k => (Nat.fib k : ℝ) ^ (s / 2))
  simp only [hsq] at hCS
  rw [sum_congr rfl hfg] at hCS
  -- `F_n F_{n+1} = ∑ F_k ^ 2 ≤ ∑ F_k ^ ((r + s) / 2)`.
  have hP0 : 0 ≤ (Nat.fib n : ℝ) * Nat.fib (n + 1) := by positivity
  have hQ : (Nat.fib n : ℝ) * Nat.fib (n + 1) ≤
      ∑ k ∈ Icc 1 n, (Nat.fib k : ℝ) ^ ((r + s) / 2) := by
    rw [← Nat.sum_Icc_fib_rpow_two]
    exact sum_le_sum fun k hk =>
      Real.rpow_le_rpow_of_exponent_le (one_le_fib_of_mem_Icc hk) hα
  have hlow := pow_le_pow_left₀ hP0 hQ 2
  refine ⟨hlow.trans hCS, fun heq => ?_, fun h => ?_⟩
  · rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    refine Or.inr (Or.inr ⟨h3, ?_⟩)
    have h1mem : 1 ∈ Icc 1 n := mem_Icc.mpr ⟨le_rfl, hn⟩
    have h3mem : 3 ∈ Icc 1 n := mem_Icc.mpr ⟨by norm_num, h3⟩
    have hfib1 : (Nat.fib 1 : ℝ) = 1 := by rw [Nat.fib_one, Nat.cast_one]
    have hfib3 : (Nat.fib 3 : ℝ) = 2 := by
      rw [show Nat.fib 3 = 2 by rfl, Nat.cast_ofNat]
    -- Equality in Cauchy–Schwarz forces `r = s`, comparing `F_1` and `F_3`.
    have hrs_eq : r = s := by
      by_contra hne
      have hne' : (Nat.fib 1 : ℝ) ^ (r / 2) * (Nat.fib 3 : ℝ) ^ (s / 2) ≠
          (Nat.fib 3 : ℝ) ^ (r / 2) * (Nat.fib 1 : ℝ) ^ (s / 2) := by
        rw [hfib1, hfib3, Real.one_rpow, Real.one_rpow, one_mul, mul_one]
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact (Real.rpow_lt_rpow_of_exponent_lt one_lt_two
            (by linarith : r / 2 < s / 2)).ne'
        · exact (Real.rpow_lt_rpow_of_exponent_lt one_lt_two
            (by linarith : s / 2 < r / 2)).ne
      have hlt := Finset.sum_mul_sq_lt_sq_mul_sq (Icc 1 n)
        (fun k => (Nat.fib k : ℝ) ^ (r / 2))
        (fun k => (Nat.fib k : ℝ) ^ (s / 2)) h1mem h3mem hne'
      simp only [hsq] at hlt
      rw [sum_congr rfl hfg] at hlt
      linarith
    -- Equality in `∑ F_k ^ 2 ≤ ∑ F_k ^ ((r + s) / 2)` forces `r + s = 4`.
    have hα2 : (r + s) / 2 = 2 := by
      by_contra hne
      have hα' : 2 < (r + s) / 2 := lt_of_le_of_ne hα (Ne.symm hne)
      have hlt : (Nat.fib n : ℝ) * Nat.fib (n + 1) <
          ∑ k ∈ Icc 1 n, (Nat.fib k : ℝ) ^ ((r + s) / 2) := by
        rw [← Nat.sum_Icc_fib_rpow_two]
        refine sum_lt_sum (fun k hk =>
          Real.rpow_le_rpow_of_exponent_le (one_le_fib_of_mem_Icc hk) hα)
          ⟨3, h3mem, ?_⟩
        rw [hfib3]
        exact Real.rpow_lt_rpow_of_exponent_lt one_lt_two hα'
      have := pow_lt_pow_left₀ hlt hP0 two_ne_zero
      linarith
    constructor <;> linarith
  · rcases h with rfl | rfl | ⟨-, rfl, rfl⟩
    · simp
    · rw [show Icc 1 2 = {1, 2} by rfl, sum_pair (by norm_num),
        sum_pair (by norm_num), show Nat.fib 3 = 2 by rfl]
      norm_num
    · rw [Nat.sum_Icc_fib_rpow_two, sq]

end

end MetaMathlibExt
