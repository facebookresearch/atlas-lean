/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Algebra.Order.Chebyshev

/-!
# Nesterov's worst function and the lower complexity bound

Nesterov's lower complexity bound for first-order methods on `L`-smooth convex functions,
Theorem 2.1.6 of Yu. Nesterov, *Introductory Lectures on Convex Programming, Volume I: Basic
course* (lecture notes, July 2, 1998), proved with his "worst function in the world"
`f_m(x) = L / 4 (1 / 2 ((x₁)² + ∑_{i=1}^{m-1} (xᵢ - x_{i+1})² + (x_m)²) - x₁)` on `ℝⁿ`, `m ≤ n`.

Coordinates are `1`-indexed as in the source: `coordVec n m j` is the `j`-th basis vector of
`ℝⁿ` (coordinate `j - 1` of `Fin n`) for `1 ≤ j ≤ m`, `m ≤ n`, and `0` otherwise, so that
`⟪coordVec n m j, x⟫ = x_j`.
-/

@[expose] public section

open scoped ContDiff

namespace MathlibExt.Analysis.Convex.FirstOrderLowerBound

variable {n : ℕ}

local notation "E" n => EuclideanSpace ℝ (Fin n)

-- The `j`-th basis vector (`1`-indexed) of `ℝⁿ` if `1 ≤ j ≤ m` and `j ≤ n`, else `0`.
noncomputable def coordVec (n m j : ℕ) : EuclideanSpace ℝ (Fin n) :=
  if h : 1 ≤ j ∧ j ≤ m ∧ j ≤ n then EuclideanSpace.single ⟨j - 1, by omega⟩ 1 else 0

/-- **Nesterov's worst function in the world.** For `L > 0` and `m ≤ n`, the quadratic
`f_m(x) = L / 4 (1 / 2 ((x₁)² + ∑_{i=1}^{m-1} (xᵢ - x_{i+1})² + (x_m)²) - x₁)` on `ℝⁿ`, written
as `L / 4 (1 / 2 ∑_{i=0}^{m} (x_i - x_{i+1})² - x₁)` with `x₀ = x_{m+1} = 0`.
This is the family `f_k` of Section 2.1.2 of Yu. Nesterov, *Introductory Lectures on Convex
Programming, Volume I: Basic course* (lecture notes, July 2, 1998). -/
noncomputable def worstFunction (n m : ℕ) (L : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  L / 4 * (1 / 2 * ∑ i ∈ Finset.range (m + 1),
    inner ℝ (coordVec n m i - coordVec n m (i + 1)) x ^ 2 - inner ℝ (coordVec n m 1) x)

-- The gradient of `worstFunction`.
private noncomputable def worstGrad (n m : ℕ) (L : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  (L / 4) • (∑ i ∈ Finset.range (m + 1),
    inner ℝ (coordVec n m i - coordVec n m (i + 1)) x • (coordVec n m i - coordVec n m (i + 1))
    - coordVec n m 1)

private lemma coordVec_zero (m : ℕ) : coordVec n m 0 = 0 := by simp [coordVec]

private lemma coordVec_of_lt {m j : ℕ} (h : m < j) : coordVec n m j = 0 := by
  unfold coordVec; split_ifs with h' <;> first | rfl | omega

private lemma inner_coordVec_coordVec (m i j : ℕ) :
    inner ℝ (coordVec n m i) (coordVec n m j) =
      if i = j ∧ 1 ≤ i ∧ i ≤ m ∧ i ≤ n then 1 else 0 := by
  unfold coordVec
  split_ifs with h1 h2 h3 <;>
    simp_all [EuclideanSpace.inner_single_left, PiLp.single_apply, Fin.ext_iff] <;> omega

/-! ### Smoothness, convexity and the gradient -/

private lemma hasGradientAt_worstFunction (m : ℕ) (L : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    HasGradientAt (worstFunction n m L) (worstGrad n m L x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  set a : ℕ → EuclideanSpace ℝ (Fin n) := fun i => coordVec n m i - coordVec n m (i + 1)
  have hlin : ∀ b : EuclideanSpace ℝ (Fin n), HasFDerivAt (fun y => inner ℝ b y) (innerSL ℝ b) x :=
    fun b => (innerSL ℝ b).hasFDerivAt
  have hsq : ∀ i, HasFDerivAt (fun y => inner ℝ (a i) y ^ 2)
      ((2 * inner ℝ (a i) x) • innerSL ℝ (a i)) x := by
    intro i
    have := (hlin (a i)).pow 2
    convert this using 1
    simp
  have hsum := HasFDerivAt.fun_sum (u := Finset.range (m + 1)) (fun i _ => hsq i)
  have hf := ((hsum.const_mul (1 / 2 : ℝ)).sub (hlin (coordVec n m 1))).const_mul (L / 4)
  refine hf.congr_fderiv ?_
  ext w
  simp only [one_div, inner_sub_left, map_sub, smul_apply, sub_apply, sum_apply,
    coe_innerSL_apply, smul_eq_mul, Finset.mul_sum, worstGrad, map_smul, map_sum,
    InnerProductSpace.toDual_apply_apply, mul_eq_mul_left_iff, sub_left_inj, div_eq_zero_iff,
    OfNat.ofNat_ne_zero, or_false, a]
  left
  exact Finset.sum_congr rfl fun i _ => by ring

private lemma gradient_worstFunction (m : ℕ) (L : ℝ) :
    gradient (worstFunction n m L) = worstGrad n m L :=
  funext fun x => (hasGradientAt_worstFunction m L x).gradient

private lemma contDiff_worstFunction (m : ℕ) (L : ℝ) : ContDiff ℝ ∞ (worstFunction n m L) := by
  have hinner : ∀ b : EuclideanSpace ℝ (Fin n), ContDiff ℝ ∞ (fun x => inner ℝ b x) :=
    fun b => (innerSL ℝ b).contDiff
  unfold worstFunction
  exact contDiff_const.mul ((contDiff_const.mul
    (ContDiff.sum fun i _ => (hinner _).pow 2)).sub (hinner _))

private lemma convexOn_worstFunction (m : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    ConvexOn ℝ Set.univ (worstFunction n m L) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [worstFunction, smul_eq_mul, inner_add_right, inner_smul_right]
  have key : ∀ i ∈ Finset.range (m + 1),
      (a * inner ℝ (coordVec n m i - coordVec n m (i + 1)) x +
        b * inner ℝ (coordVec n m i - coordVec n m (i + 1)) y) ^ 2 ≤
      a * inner ℝ (coordVec n m i - coordVec n m (i + 1)) x ^ 2 +
        b * inner ℝ (coordVec n m i - coordVec n m (i + 1)) y ^ 2 := by
    intro i _
    set u := inner ℝ (coordVec n m i - coordVec n m (i + 1)) x
    set v := inner ℝ (coordVec n m i - coordVec n m (i + 1)) y
    have : a * u ^ 2 + b * v ^ 2 - (a * u + b * v) ^ 2 = a * b * (u - v) ^ 2 := by
      rw [show b = 1 - a by linarith]; ring
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (u - v))]
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hL4 : 0 ≤ L / 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsum hL4]

-- Bessel's inequality for the vectors `coordVec`.
private lemma sum_sq_inner_coordVec_le (m : ℕ) (s : Finset ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    ∑ i ∈ s, inner ℝ (coordVec n m i) u ^ 2 ≤ ‖u‖ ^ 2 := by
  set S := ∑ i ∈ s, inner ℝ (coordVec n m i) u ^ 2
  set w := ∑ i ∈ s, inner ℝ (coordVec n m i) u • coordVec n m i
  have hwu : inner ℝ w u = S := by
    simp only [w, S, sum_inner, real_inner_smul_left, sq]
  have hww : inner ℝ w w ≤ S := by
    simp only [w, S, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
      inner_coordVec_coordVec]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.sum_eq_single i]
    · split_ifs <;> nlinarith [sq_nonneg (inner ℝ (coordVec n m i) u)]
    · intro j _ hji
      split_ifs with h
      · exact absurd h.1 hji
      · ring
    · intro hi'; exact absurd hi hi'
  have h0 : 0 ≤ ‖u - w‖ ^ 2 := sq_nonneg _
  rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
    real_inner_comm w u, hwu] at h0
  rw [← real_inner_self_eq_norm_sq]
  linarith

private lemma lipschitzWith_worstGrad (m : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    LipschitzWith ⟨L, hL⟩ (worstGrad n m L) := by
  set a : ℕ → EuclideanSpace ℝ (Fin n) := fun i => coordVec n m i - coordVec n m (i + 1) with ha
  set T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun w => ∑ i ∈ Finset.range (m + 1), inner ℝ (a i) w • a i with hTdef
  have hA : ∀ u, ∑ i ∈ Finset.range (m + 1), inner ℝ (a i) u ^ 2 ≤ 4 * ‖u‖ ^ 2 := by
    intro u
    have h1 := sum_sq_inner_coordVec_le m (Finset.range (m + 1)) u
    have h2 := sum_sq_inner_coordVec_le m (Finset.range (m + 2)) u
    rw [Finset.sum_range_succ'] at h2
    have h3 : 0 ≤ inner ℝ (coordVec n m 0) u ^ 2 := sq_nonneg _
    have hterm : ∀ i ∈ Finset.range (m + 1), inner ℝ (a i) u ^ 2 ≤
        2 * inner ℝ (coordVec n m i) u ^ 2 + 2 * inner ℝ (coordVec n m (i + 1)) u ^ 2 := by
      intro i _
      simp only [ha, inner_sub_left]
      nlinarith [sq_nonneg (inner ℝ (coordVec n m i) u + inner ℝ (coordVec n m (i + 1)) u)]
    have := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
    linarith
  have hT : ∀ w, ‖T w‖ ≤ 4 * ‖w‖ := by
    intro w
    have hsq : ‖T w‖ ^ 2 = ∑ i ∈ Finset.range (m + 1), inner ℝ (a i) w * inner ℝ (a i) (T w) := by
      rw [← real_inner_self_eq_norm_sq]
      change inner ℝ (∑ i ∈ Finset.range (m + 1), inner ℝ (a i) w • a i) (T w) = _
      simp only [sum_inner, real_inner_smul_left]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (m + 1))
      (fun i => inner ℝ (a i) w) (fun i => inner ℝ (a i) (T w))
    rw [← hsq] at hcs
    have hw := hA w
    have hTw := hA (T w)
    have h16 : ‖T w‖ ^ 2 ≤ 16 * ‖w‖ ^ 2 := by
      rcases (norm_nonneg (T w)).lt_or_eq with hpos | hzero
      · have hpos2 : 0 < ‖T w‖ ^ 2 := by positivity
        have : (‖T w‖ ^ 2) ^ 2 ≤ (4 * ‖w‖ ^ 2) * (4 * ‖T w‖ ^ 2) :=
          hcs.trans (mul_le_mul hw hTw (Finset.sum_nonneg fun i _ => sq_nonneg _) (by positivity))
        nlinarith
      · rw [← hzero]; nlinarith [sq_nonneg ‖w‖]
    have h4 : 0 ≤ 4 * ‖w‖ := by positivity
    nlinarith [sq_nonneg (‖T w‖ - 4 * ‖w‖), norm_nonneg (T w)]
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have hdiff : worstGrad n m L x - worstGrad n m L y = (L / 4) • T (x - y) := by
    simp only [worstGrad, hTdef, ha, ← smul_sub, inner_sub_right, sub_smul,
      Finset.sum_sub_distrib]
    congr 1
    abel
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ L / 4)]
  have := hT (x - y)
  change L / 4 * ‖T (x - y)‖ ≤ L * ‖x - y‖
  nlinarith

/-- **The worst function is smooth, convex and `L`-smooth.** For `L ≥ 0`, `worstFunction n m L`
is `C^∞`, convex, and its gradient is `L`-Lipschitz: it lies in the class `F^{∞,1}_L(ℝⁿ)`, since
its Hessian `(L / 4) A_m` satisfies `0 ≤ (L / 4) A_m ≤ L I`, as shown in Section 2.1.2 of
Yu. Nesterov, *Introductory Lectures on Convex Programming, Volume I: Basic course* (lecture
notes, July 2, 1998). Here the Lipschitz bound comes from
`∑ᵢ ⟪eᵢ - e_{i+1}, u⟫² ≤ 4 ‖u‖²` and the Cauchy–Schwarz inequality. -/
lemma worstFunction_mem_class (m : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    ContDiff ℝ ∞ (worstFunction n m L) ∧ ConvexOn ℝ Set.univ (worstFunction n m L) ∧
      LipschitzWith ⟨L, hL⟩ (gradient (worstFunction n m L)) :=
  ⟨contDiff_worstFunction m L, convexOn_worstFunction m hL,
    (gradient_worstFunction m L).symm ▸ lipschitzWith_worstGrad m hL⟩

/-! ### The minimum on the first `k` coordinates -/

/-- **Minimum of the worst function on the first `k` coordinates.** Let `L ≥ 0` and
`1 ≤ k ≤ m`. If the coordinates `x_j`, `j > k`, of `z ∈ ℝⁿ` vanish (`⟪coordVec n m j, z⟫ = 0`),
then `f_m(z) ≥ -(L / 8) k / (k + 1)`; for `k = m` the hypothesis is empty and this bounds `f_m`
on all of `ℝⁿ`. On such vectors `f_m(z) ≥ f_k(z) ≥ f_k⋆ = (L / 8) (-1 + 1 / (k + 1))`, as in
Section 2.1.2 of Yu. Nesterov, *Introductory Lectures on Convex Programming, Volume I: Basic
course* (lecture notes, July 2, 1998) (the value `f_k⋆` and Corollary 2.1.1); the proof here
uses the Cauchy–Schwarz inequality on the `k` differences `x_i - x_{i+1}` instead of solving
`A_k x = e₁`. -/
lemma worstFunction_ge_of_support {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) {L : ℝ} (hL : 0 ≤ L)
    {z : EuclideanSpace ℝ (Fin n)} (hz : ∀ j, k < j → inner ℝ (coordVec n m j) z = 0) :
    -(L / 8) * (k / (k + 1)) ≤ worstFunction n m L z := by
  set c : ℕ → ℝ := fun j => inner ℝ (coordVec n m j) z with hc
  have hS : ∑ i ∈ Finset.range (m + 1),
      inner ℝ (coordVec n m i - coordVec n m (i + 1)) z ^ 2 =
      ∑ i ∈ Finset.range m, (c (i + 1) - c (i + 2)) ^ 2 + c 1 ^ 2 := by
    rw [Finset.sum_range_succ']
    simp only [inner_sub_left, hc, coordVec_zero, zero_sub, inner_neg_left, neg_sq, zero_add]
  have hsub : ∑ i ∈ Finset.range k, (c (i + 1) - c (i + 2)) ^ 2 ≤
      ∑ i ∈ Finset.range m, (c (i + 1) - c (i + 2)) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hkm)
      fun i _ _ => sq_nonneg _
  have htel : ∑ i ∈ Finset.range k, (c (i + 1) - c (i + 2)) = c 1 := by
    have := Finset.sum_range_sub' (fun i => c (i + 1)) k
    rw [this, hc]
    simp only [hz (k + 1) (by omega), sub_zero]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range k)
    (f := fun i => c (i + 1) - c (i + 2))
  simp only [Finset.card_range] at hcs
  rw [htel] at hcs
  unfold worstFunction
  rw [hS]
  set S' := ∑ i ∈ Finset.range k, (c (i + 1) - c (i + 2)) ^ 2
  set t := c 1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hS'0 : 0 ≤ S' := Finset.sum_nonneg fun i _ => sq_nonneg _
  set Sm := ∑ i ∈ Finset.range m, (c (i + 1) - c (i + 2)) ^ 2
  have hpos : (0 : ℝ) < 2 * k * (k + 1) := by positivity
  have key : 0 ≤ 1 / 2 * (Sm + t ^ 2) - t + k / (2 * (k + 1)) := by
    have e : (1 / 2 * (Sm + t ^ 2) - t + k / (2 * (k + 1))) * (2 * k * (k + 1)) =
        k * (k + 1) * (Sm + t ^ 2) - 2 * k * (k + 1) * t + k ^ 2 := by
      field_simp
    have h1 := mul_le_mul_of_nonneg_left hsub (by positivity : (0 : ℝ) ≤ k * (k + 1))
    have h2 := mul_le_mul_of_nonneg_left hcs (by positivity : (0 : ℝ) ≤ k + 1)
    have h3 : 0 ≤ k * (k + 1) * (Sm + t ^ 2) - 2 * k * (k + 1) * t + k ^ 2 := by
      nlinarith [sq_nonneg (((k : ℝ) + 1) * t - k)]
    rw [← e] at h3
    exact (mul_nonneg_iff_of_pos_right hpos).mp h3
  have e2 : -(L / 8) * (k / (k + 1)) = L / 4 * (-(k / (2 * (k + 1)))) := by
    field_simp; ring
  rw [e2]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

/-! ### The minimiser -/

/-- **Minimiser of the worst function.** The vector `x̄ ∈ ℝⁿ` with `x̄ⱼ = 1 - j / (m + 1)` for
`1 ≤ j ≤ m` and `x̄ⱼ = 0` for `j > m` (coordinates `1`-indexed), the solution of `A_m x = e₁`
computed in Section 2.1.2 of Yu. Nesterov, *Introductory Lectures on Convex Programming,
Volume I: Basic course* (lecture notes, July 2, 1998). -/
noncomputable def worstMinimizer (n m : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun p : Fin n => if (p : ℕ) < m then 1 - ((p : ℕ) + 1 : ℝ) / (m + 1) else 0

private lemma inner_coordVec_worstMinimizer {m : ℕ} (hmn : m ≤ n) (j : ℕ) :
    inner ℝ (coordVec n m j) (worstMinimizer n m) =
      if 1 ≤ j ∧ j ≤ m then 1 - (j : ℝ) / (m + 1) else 0 := by
  unfold coordVec worstMinimizer
  by_cases h : 1 ≤ j ∧ j ≤ m
  · have h' : 1 ≤ j ∧ j ≤ m ∧ j ≤ n := ⟨h.1, h.2, h.2.trans hmn⟩
    have h'' : j - 1 < m := by omega
    simp only [h', and_self, ↓reduceDIte, ↓reduceIte, EuclideanSpace.inner_single_left,
      map_one, one_mul, h'']
    rw [Nat.cast_sub h.1]; ring
  · have h' : ¬ (1 ≤ j ∧ j ≤ m ∧ j ≤ n) := by tauto
    simp only [h', h, ↓reduceDIte, ↓reduceIte, inner_zero_left]

/-- **Minimum value of the worst function.** For `1 ≤ m ≤ n`,
`f_m(x̄) = -(L / 8) m / (m + 1) = (L / 8) (-1 + 1 / (m + 1))`, the value `f_m⋆` of Section 2.1.2
of Yu. Nesterov, *Introductory Lectures on Convex Programming, Volume I: Basic course* (lecture
notes, July 2, 1998); with `worstFunction_ge_of_support` for `k = m` it shows that `x̄` minimises
`f_m`. -/
lemma worstFunction_worstMinimizer {m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (L : ℝ) :
    worstFunction n m L (worstMinimizer n m) = -(L / 8) * (m / (m + 1)) := by
  unfold worstFunction
  rw [Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range m,
      inner ℝ (coordVec n m (i + 1) - coordVec n m (i + 1 + 1)) (worstMinimizer n m) ^ 2 =
        (1 / ((m : ℝ) + 1)) ^ 2 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have c1 : 1 ≤ i + 1 ∧ i + 1 ≤ m := by omega
    rw [inner_sub_left, inner_coordVec_worstMinimizer hmn, inner_coordVec_worstMinimizer hmn]
    simp only [c1, and_self, ↓reduceIte]
    by_cases h2 : i + 1 + 1 ≤ m
    · have c2 : 1 ≤ i + 1 + 1 ∧ i + 1 + 1 ≤ m := ⟨by omega, h2⟩
      simp only [c2, and_self, ↓reduceIte]; push_cast; field_simp; ring
    · have c2 : ¬ (1 ≤ i + 1 + 1 ∧ i + 1 + 1 ≤ m) := by omega
      have : i + 1 = m := by omega
      simp only [c2, ↓reduceIte]
      rw [← this]; push_cast; field_simp; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    inner_sub_left, inner_coordVec_worstMinimizer hmn, inner_coordVec_worstMinimizer hmn]
  have c0 : ¬ (1 ≤ 0 ∧ 0 ≤ m) := by omega
  have c1 : 1 ≤ 0 + 1 ∧ 0 + 1 ≤ m := by omega
  simp only [c0, c1, and_self, ↓reduceIte, zero_add, Nat.cast_one]
  field_simp
  ring

private lemma sum_range_sq_succ_le (m : ℕ) :
    ∑ l ∈ Finset.range m, ((l : ℝ) + 1) ^ 2 ≤ ((m : ℝ) + 1) ^ 3 / 3 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ]; push_cast
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith

private lemma sum_range_sq_succ_ge (m : ℕ) :
    (m : ℝ) ^ 3 / 3 ≤ ∑ l ∈ Finset.range m, ((l : ℝ) + 1) ^ 2 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ]; push_cast
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith

private lemma sum_range_sq_reflect (m : ℕ) :
    ∑ p ∈ Finset.range m, ((m : ℝ) - p) ^ 2 = ∑ l ∈ Finset.range m, ((l : ℝ) + 1) ^ 2 := by
  rw [← Finset.sum_range_reflect (fun l => ((l : ℝ) + 1) ^ 2) m]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_range] at hp
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

-- Sums over the coordinates `p < m` of `ℝⁿ` written as sums over `range m`.
private lemma sum_fin_ite_eq {m : ℕ} (hmn : m ≤ n) (a : ℕ) (g : ℕ → ℝ) :
    ∑ p : Fin n, (if a ≤ (p : ℕ) ∧ (p : ℕ) < m then g p else 0) =
      ∑ q ∈ Finset.Ico a m, g q := by
  rw [Fin.sum_univ_eq_sum_range (fun q => if a ≤ q ∧ q < m then g q else 0) n,
    ← Finset.sum_filter]
  congr 1
  ext q; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega

private lemma norm_sq_worstMinimizer_le {m : ℕ} (hmn : m ≤ n) :
    ‖worstMinimizer n m‖ ^ 2 ≤ ((m : ℝ) + 1) / 3 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have h : ∀ p : Fin n, (worstMinimizer n m p) ^ 2 =
      if 0 ≤ (p : ℕ) ∧ (p : ℕ) < m then (((m : ℝ) - p) / (m + 1)) ^ 2 else 0 := by
    intro p
    simp only [worstMinimizer, PiLp.toLp_apply, zero_le, true_and]
    split_ifs
    · congr 1; field_simp; ring
    · ring
  simp only [h]
  rw [sum_fin_ite_eq hmn 0 (fun q => (((m : ℝ) - q) / (m + 1)) ^ 2), ← Finset.range_eq_Ico]
  simp only [div_pow]
  rw [← Finset.sum_div, sum_range_sq_reflect, div_le_iff₀ (by positivity)]
  have := sum_range_sq_succ_le m
  have e : ((m : ℝ) + 1) / 3 * ((m : ℝ) + 1) ^ 2 = ((m : ℝ) + 1) ^ 3 / 3 := by ring
  linarith

private lemma norm_sq_sub_worstMinimizer_ge {k : ℕ} (hmn : 2 * k + 1 ≤ n)
    {z : EuclideanSpace ℝ (Fin n)} (hz : ∀ j, k < j → inner ℝ (coordVec n (2 * k + 1) j) z = 0) :
    ((k : ℝ) + 1) / 12 ≤ ‖z - worstMinimizer n (2 * k + 1)‖ ^ 2 := by
  set m := 2 * k + 1 with hm
  rw [EuclideanSpace.real_norm_sq_eq]
  have hcoord : ∀ p : Fin n, k ≤ (p : ℕ) → (p : ℕ) < m → z p = 0 := by
    intro p hkp hpm
    have h := hz ((p : ℕ) + 1) (by omega)
    have hv : 1 ≤ (p : ℕ) + 1 ∧ (p : ℕ) + 1 ≤ m ∧ (p : ℕ) + 1 ≤ n := by omega
    simp only [coordVec, hv, and_self, ↓reduceDIte, EuclideanSpace.inner_single_left, map_one,
      one_mul, Nat.add_sub_cancel] at h
    exact h
  have hle : ∀ p : Fin n, (if k ≤ (p : ℕ) ∧ (p : ℕ) < m then
      (((m : ℝ) - p) / (m + 1)) ^ 2 else 0) ≤ ((z - worstMinimizer n m) p) ^ 2 := by
    intro p
    split_ifs with hp
    · rw [PiLp.sub_apply, hcoord p hp.1 hp.2]
      simp only [worstMinimizer, PiLp.toLp_apply, hp.2, ↓reduceIte, zero_sub, neg_sq]
      refine le_of_eq ?_
      congr 1; field_simp; ring
    · exact sq_nonneg _
  refine le_trans ?_ (Finset.sum_le_sum fun p _ => hle p)
  rw [sum_fin_ite_eq (by omega) k (fun q => (((m : ℝ) - q) / (m + 1)) ^ 2)]
  rw [Finset.sum_Ico_eq_sum_range]
  have e : ∀ l ∈ Finset.range (m - k), (((m : ℝ) - ((k + l : ℕ) : ℝ)) / (m + 1)) ^ 2 =
      (((k + 1 : ℕ) : ℝ) - l) ^ 2 / ((2 * k + 2 : ℕ) : ℝ) ^ 2 := by
    intro l _; rw [hm]; push_cast; field_simp; ring
  rw [Finset.sum_congr rfl e, show m - k = k + 1 by omega, ← Finset.sum_div,
    sum_range_sq_reflect, le_div_iff₀ (by positivity)]
  have := sum_range_sq_succ_ge (k + 1)
  push_cast at this ⊢
  nlinarith

/-! ### Krylov subspaces -/

-- Vectors whose coordinates beyond `j` vanish (for the block `1, …, m`).
private def support (n m j : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) where
  carrier := {z | ∀ i, j < i → inner ℝ (coordVec n m i) z = 0}
  add_mem' := by intro a b ha hb i hi; rw [inner_add_right, ha i hi, hb i hi, add_zero]
  zero_mem' := by intro i _; rw [inner_zero_right]
  smul_mem' := by intro c a ha i hi; rw [inner_smul_right, ha i hi, mul_zero]

private lemma support_mono {m a b : ℕ} (hab : a ≤ b) : support n m a ≤ support n m b :=
  fun _ hz i hi => hz i (lt_of_le_of_lt hab hi)

private lemma worstGrad_mem_support {m j : ℕ} (L : ℝ) {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ support n m j) : worstGrad n m L z ∈ support n m (j + 1) := by
  intro i hi
  simp only [worstGrad, real_inner_smul_right, inner_sub_right, inner_sum]
  have h1 : inner ℝ (coordVec n m i) (coordVec n m 1) = 0 := by
    rw [inner_coordVec_coordVec]
    simp only [show ¬ (i = 1 ∧ 1 ≤ i ∧ i ≤ m ∧ i ≤ n) by omega, ↓reduceIte]
  rw [h1, sub_zero]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : l = i ∨ l + 1 = i
  · have hzero : inner ℝ (coordVec n m l - coordVec n m (l + 1)) z = 0 := by
      rw [inner_sub_left, hz l (by omega), hz (l + 1) (by omega), sub_zero]
    rw [hzero, zero_mul]
  · rw [inner_coordVec_coordVec, inner_coordVec_coordVec]
    simp only [show ¬ (i = l ∧ 1 ≤ i ∧ i ≤ m ∧ i ≤ n) by omega,
      show ¬ (i = l + 1 ∧ 1 ≤ i ∧ i ≤ m ∧ i ≤ n) by omega, ↓reduceIte, sub_zero, mul_zero]

private lemma mem_support_of_mem_span {m : ℕ} (L : ℝ) {z : ℕ → EuclideanSpace ℝ (Fin n)}
    (hspan : ∀ j, z j ∈ Submodule.span ℝ ((fun i => worstGrad n m L (z i)) '' Set.Iio j)) :
    ∀ j, z j ∈ support n m j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    refine (Submodule.span_le.mpr ?_) (hspan j)
    rintro _ ⟨i, hi, rfl⟩
    exact support_mono (m := m) (Nat.succ_le_of_lt hi) (worstGrad_mem_support L (ih i hi))

/-! ### The lower complexity bound -/

/-- **Lower complexity bound for smooth convex minimisation.** Let `L > 0`, `1 ≤ k` and
`2 k + 1 ≤ n`. For every `x₀ ∈ ℝⁿ` there is a convex `C^∞` function `f` on `ℝⁿ` with `L`-Lipschitz
gradient and a minimiser `x⋆` of `f` such that every sequence with `x 0 = x₀` and
`x j - x₀ ∈ span {∇f (x i) : i < j}` for all `j` satisfies
`f (x k) - f x⋆ ≥ 3 L ‖x₀ - x⋆‖ ^ 2 / (32 (k + 1) ^ 2)` and
`‖x k - x⋆‖ ^ 2 ≥ ‖x₀ - x⋆‖ ^ 2 / 32`.

This is Theorem 2.1.6 of Yu. Nesterov, *Introductory Lectures on Convex Programming, Volume I:
Basic course* (lecture notes, July 2, 1998), whose hypothesis `1 ≤ k ≤ (n - 1) / 2` is
`2 k + 1 ≤ n`. The function is the shift by `x₀` of `worstFunction n (2 k + 1) L`, and `x⋆` is
the shift of its minimiser `x̄ᵢ = 1 - i / (2 k + 2)` (`i ≤ 2 k + 1`), `x̄ᵢ = 0` otherwise; for
`n > 2 k + 1` the minimiser is not unique and the bound is claimed for this one. -/
theorem exists_lower_bound_smooth_convex {k : ℕ} (hk : 1 ≤ k) (hkn : 2 * k + 1 ≤ n)
    {L : ℝ} (hL : 0 < L) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ f ∧ ConvexOn ℝ Set.univ f ∧
      LipschitzWith ⟨L, hL.le⟩ (gradient f) ∧
      ∃ xstar : EuclideanSpace ℝ (Fin n), (∀ z, f xstar ≤ f z) ∧
        ∀ x : ℕ → EuclideanSpace ℝ (Fin n), x 0 = x₀ →
          (∀ j, x j - x₀ ∈ Submodule.span ℝ ((fun i => gradient f (x i)) '' Set.Iio j)) →
          3 * L * ‖x₀ - xstar‖ ^ 2 / (32 * ((k : ℝ) + 1) ^ 2) ≤ f (x k) - f xstar ∧
            ‖x₀ - xstar‖ ^ 2 / 32 ≤ ‖x k - xstar‖ ^ 2 := by
  set m := 2 * k + 1 with hm
  set g := worstFunction n m L
  set f : EuclideanSpace ℝ (Fin n) → ℝ := fun x => g (x - x₀) with hfdef
  have hgradf : ∀ x, gradient f x = worstGrad n m L (x - x₀) := by
    intro x
    have h := (hasGradientAt_worstFunction m L (x - x₀))
    rw [hasGradientAt_iff_hasFDerivAt] at h
    have h2 := h.comp x ((hasFDerivAt_id x).sub_const x₀)
    simp only [ContinuousLinearMap.comp_id] at h2
    exact (hasGradientAt_iff_hasFDerivAt.mpr h2).gradient
  obtain ⟨hcd, hcv, hlip⟩ := worstFunction_mem_class (n := n) m hL.le
  refine ⟨f, ?_, ?_, ?_, x₀ + worstMinimizer n m, ?_, ?_⟩
  · exact hcd.comp (contDiff_id.sub contDiff_const)
  · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have h := hcv.2 (Set.mem_univ (x - x₀)) (Set.mem_univ (y - x₀)) ha hb hab
    have e : a • (x - x₀) + b • (y - x₀) = a • x + b • y - x₀ := by
      rw [smul_sub, smul_sub, ← sub_eq_zero]
      have : x₀ = (a + b) • x₀ := by rw [hab, one_smul]
      nth_rewrite 3 [this]
      rw [add_smul]; abel
    rw [e] at h
    exact h
  · rw [show gradient f = fun x => worstGrad n m L (x - x₀) from funext hgradf]
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have := hlip.dist_le_mul (x - x₀) (y - x₀)
    rwa [dist_sub_right, gradient_worstFunction] at this
  · intro z
    simp only [f, g, add_sub_cancel_left]
    rw [worstFunction_worstMinimizer (by omega) hkn]
    exact worstFunction_ge_of_support (by omega) le_rfl hL.le
      fun j hj => by rw [coordVec_of_lt hj, inner_zero_left]
  · intro x hx0 hspan
    set z : ℕ → EuclideanSpace ℝ (Fin n) := fun j => x j - x₀
    have hspan' : ∀ j, z j ∈ Submodule.span ℝ ((fun i => worstGrad n m L (z i)) '' Set.Iio j) := by
      intro j
      have := hspan j
      simp only [hgradf] at this
      exact this
    have hzk := mem_support_of_mem_span L hspan' k
    have hnorm := norm_sq_worstMinimizer_le (n := n) (m := m) hkn
    have hx0s : ‖x₀ - (x₀ + worstMinimizer n m)‖ = ‖worstMinimizer n m‖ := by
      rw [sub_add_cancel_left, norm_neg]
    have hxks : x k - (x₀ + worstMinimizer n m) = z k - worstMinimizer n m := by
      simp only [z]; abel
    rw [hx0s, hxks]
    have hm1 : ((m : ℕ) : ℝ) + 1 = 2 * ((k : ℝ) + 1) := by rw [hm]; push_cast; ring
    rw [hm1] at hnorm
    have hk0 : (0 : ℝ) < k + 1 := by positivity
    constructor
    · simp only [f, g, add_sub_cancel_left]
      rw [worstFunction_worstMinimizer (by omega) hkn]
      have hlow := worstFunction_ge_of_support (n := n) (m := m) hk (by omega) hL.le hzk
      have hgap : -(L / 8) * (k / (k + 1)) - -(L / 8) * ((m : ℕ) / ((m : ℕ) + 1)) =
          L / (16 * (k + 1)) := by
        rw [hm1]; rw [hm]; push_cast; field_simp; ring
      have hb : 3 * L * ‖worstMinimizer n m‖ ^ 2 / (32 * ((k : ℝ) + 1) ^ 2) ≤
          L / (16 * (k + 1)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hnorm (by positivity : (0 : ℝ) ≤ 3 * L)]
      simp only [z] at hlow
      linarith
    · have hlow := norm_sq_sub_worstMinimizer_ge (n := n) (k := k) hkn hzk
      linarith

end MathlibExt.Analysis.Convex.FirstOrderLowerBound
