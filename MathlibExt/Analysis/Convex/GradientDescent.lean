/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Algebra.BigOperators.Field

/-!
# Gradient descent on smooth convex functions

This file proves the descent and first-order estimates used to obtain the `O(1 / k)` objective
gap for fixed-step gradient descent on a smooth convex function.
-/

@[expose] public section

namespace MetaMathlibExt

private theorem gradientDescent_hasDerivAt_line
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} (hdiff : Differentiable ℝ f) (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • d))
      (inner ℝ (gradient f (x + t • d)) d) t := by
  have hpath : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have hf := (hdiff (x + t • d)).hasGradientAt.hasFDerivAt
  simpa [Function.comp_def] using (hf.comp t hpath.hasFDerivAt).hasDerivAt

private theorem gradientDescent_descent_lemma
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {L : ℝ} (hL : 0 ≤ L) (hdiff : Differentiable ℝ f)
    (hsmooth : LipschitzWith ⟨L, hL⟩ (gradient f)) (x d : E) :
    f (x + d) ≤ f x + inner ℝ (gradient f x) d + L / 2 * ‖d‖ ^ 2 := by
  have hB (t : ℝ) :
      HasDerivAt (fun s : ℝ => f x + s * inner ℝ (gradient f x) d +
        L / 2 * s ^ 2 * ‖d‖ ^ 2)
        (inner ℝ (gradient f x) d + L * t * ‖d‖ ^ 2) t := by
    have hlin : HasDerivAt
        (fun s : ℝ => f x + s * inner ℝ (gradient f x) d)
        (inner ℝ (gradient f x) d) t := by
      simpa using ((hasDerivAt_id t).mul_const (inner ℝ (gradient f x) d)).const_add
        (f x)
    have hquad : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖d‖ ^ 2)
        (L * t * ‖d‖ ^ 2) t := by
      have h := (((hasDerivAt_id t).mul (hasDerivAt_id t)).const_mul
        (L / 2)).mul_const (‖d‖ ^ 2)
      convert h using 1
      · funext s
        simp only [Pi.mul_apply, id_eq]
        ring
      · simp only [id_eq]
        ring
    convert hlin.add hquad using 1
  have hgrad (t : ℝ) (ht : 0 ≤ t) :
      inner ℝ (gradient f (x + t • d) - gradient f x) d ≤ L * t * ‖d‖ ^ 2 := by
    calc
      inner ℝ (gradient f (x + t • d) - gradient f x) d ≤
          ‖gradient f (x + t • d) - gradient f x‖ * ‖d‖ :=
        real_inner_le_norm _ _
      _ = dist (gradient f (x + t • d)) (gradient f x) * ‖d‖ := by
        rw [dist_eq_norm]
      _ ≤ (L * dist (x + t • d) x) * ‖d‖ := by
        exact mul_le_mul_of_nonneg_right (hsmooth.dist_le_mul _ _) (norm_nonneg d)
      _ = L * t * ‖d‖ ^ 2 := by
        rw [dist_eq_norm]
        simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
        ring
  have hcurve : Continuous (fun t : ℝ => f (x + t • d)) := by
    apply hdiff.continuous.comp
    fun_prop
  have hbound := image_le_of_deriv_right_le_deriv_boundary
    (f := fun t : ℝ => f (x + t • d))
    (f' := fun t => inner ℝ (gradient f (x + t • d)) d)
    (B := fun t => f x + t * inner ℝ (gradient f x) d + L / 2 * t ^ 2 * ‖d‖ ^ 2)
    (B' := fun t => inner ℝ (gradient f x) d + L * t * ‖d‖ ^ 2)
    hcurve.continuousOn
    (fun t _ => (gradientDescent_hasDerivAt_line hdiff x d t).hasDerivWithinAt)
    (by simp) (by fun_prop) (fun t _ => (hB t).hasDerivWithinAt) (by
      intro t ht
      have h := hgrad t ht.1
      rw [inner_sub_left] at h
      linarith)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)
  simpa using hbound

private theorem gradientDescent_sufficient_decrease
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {L : ℝ} (hL : 0 < L) (hdiff : Differentiable ℝ f)
    (hsmooth : LipschitzWith ⟨L, le_of_lt hL⟩ (gradient f))
    {η : ℝ} (hη : η ∈ Set.Ioc 0 (1 / L)) (x : E) :
    f (x - η • gradient f x) ≤ f x - η / 2 * ‖gradient f x‖ ^ 2 := by
  have h := gradientDescent_descent_lemma (le_of_lt hL) hdiff hsmooth x
    (-η • gradient f x)
  have hηL : η * L ≤ 1 := (le_div_iff₀ hL).mp hη.2
  have hcoeff : L * η ^ 2 ≤ η := by
    calc
      L * η ^ 2 = η * (η * L) := by ring
      _ ≤ η * 1 := mul_le_mul_of_nonneg_left hηL (le_of_lt hη.1)
      _ = η := mul_one η
  have hterm := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg ‖gradient f x‖)
  rw [show x + -η • gradient f x = x - η • gradient f x by
    rw [neg_smul, sub_eq_add_neg]] at h
  simp only [inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
    Real.norm_eq_abs, abs_neg, abs_of_pos hη.1] at h
  nlinarith

private theorem gradientDescent_first_order
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} (hconvex : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (x y : E) : f x + inner ℝ (gradient f x) (y - x) ≤ f y := by
  have hlineconvex : ConvexOn ℝ Set.univ
      (fun t : ℝ => f (x + t • (y - x))) := by
    have h := hconvex.comp_affineMap (AffineMap.lineMap x y)
    simpa [Function.comp_def, AffineMap.lineMap_apply, add_comm] using h
  have hderiv : HasDerivAt (fun t : ℝ => f (x + t • (y - x)))
      (inner ℝ (gradient f x) (y - x)) 0 := by
    simpa using gradientDescent_hasDerivAt_line hdiff x (y - x) 0
  have hslope := hlineconvex.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    zero_lt_one hderiv
  rw [slope_def_field] at hslope
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at hslope
  rw [show x + (y - x) = y by abel] at hslope
  linarith

private theorem gradientDescent_one_step
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {L : ℝ} (hL : 0 < L) (hconvex : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f)
    (hsmooth : LipschitzWith ⟨L, le_of_lt hL⟩ (gradient f))
    {η : ℝ} (hη : η ∈ Set.Ioc 0 (1 / L)) (x xstar : E) :
    f (x - η • gradient f x) - f xstar ≤
      (‖x - xstar‖ ^ 2 - ‖x - η • gradient f x - xstar‖ ^ 2) / (2 * η) := by
  apply (le_div_iff₀ (mul_pos (by norm_num) hη.1)).2
  have hdec := gradientDescent_sufficient_decrease hL hdiff hsmooth hη x
  have hfirst := gradientDescent_first_order hconvex hdiff x xstar
  rw [show xstar - x = -(x - xstar) by abel, inner_neg_right] at hfirst
  have hgap : f (x - η • gradient f x) - f xstar ≤
      inner ℝ (gradient f x) (x - xstar) - η / 2 * ‖gradient f x‖ ^ 2 := by
    linarith
  have htwoη : 0 ≤ 2 * η := le_of_lt (mul_pos (by norm_num) hη.1)
  have hmul : (f (x - η • gradient f x) - f xstar) * (2 * η) ≤
      (inner ℝ (gradient f x) (x - xstar) - η / 2 * ‖gradient f x‖ ^ 2) *
        (2 * η) := mul_le_mul_of_nonneg_right hgap htwoη
  have hdist : ‖x - xstar‖ ^ 2 - ‖x - η • gradient f x - xstar‖ ^ 2 =
      (inner ℝ (gradient f x) (x - xstar) - η / 2 * ‖gradient f x‖ ^ 2) *
        (2 * η) := by
    rw [show x - η • gradient f x - xstar =
      (x - xstar) - η • gradient f x by abel]
    rw [norm_sub_sq_real (x - xstar) (η • gradient f x)]
    simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hη.1]
    rw [real_inner_comm]
    ring
  rw [hdist]
  exact hmul

private theorem gradientDescent_antitone
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {L : ℝ} (hL : 0 < L) (hdiff : Differentiable ℝ f)
    (hsmooth : LipschitzWith ⟨L, le_of_lt hL⟩ (gradient f))
    {η : ℝ} (hη : η ∈ Set.Ioc 0 (1 / L))
    {X : ℕ → E} (hX : ∀ k, X (k + 1) = X k - η • gradient f (X k)) :
    Antitone (fun k => f (X k)) := by
  apply antitone_nat_of_succ_le
  intro k
  rw [hX k]
  calc
    f (X k - η • gradient f (X k)) ≤
        f (X k) - η / 2 * ‖gradient f (X k)‖ ^ 2 :=
      gradientDescent_sufficient_decrease hL hdiff hsmooth hη (X k)
    _ ≤ f (X k) := sub_le_self _
      (mul_nonneg (div_nonneg (le_of_lt hη.1) (by norm_num)) (sq_nonneg _))

private theorem gradientDescent_sum_range_sub_div (p : ℕ → ℝ) (k : ℕ) (c : ℝ) :
    ∑ i ∈ Finset.range k, (p i - p (i + 1)) / c = (p 0 - p k) / c := by
  rw [← Finset.sum_div]
  congr 1
  calc
    ∑ i ∈ Finset.range k, (p i - p (i + 1)) =
        -∑ i ∈ Finset.range k, (p (i + 1) - p i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = -(p k - p 0) := by rw [Finset.sum_range_sub]
    _ = p 0 - p k := by ring

private theorem gradientDescent_sum_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {L : ℝ} (hL : 0 < L) (hconvex : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f)
    (hsmooth : LipschitzWith ⟨L, le_of_lt hL⟩ (gradient f))
    {xstar : E} {η : ℝ} (hη : η ∈ Set.Ioc 0 (1 / L))
    {X : ℕ → E} (hX : ∀ k, X (k + 1) = X k - η • gradient f (X k)) (k : ℕ) :
    ∑ i ∈ Finset.range k, (f (X (i + 1)) - f xstar) ≤
      ‖X 0 - xstar‖ ^ 2 / (2 * η) := by
  have hsum : ∑ i ∈ Finset.range k, (f (X (i + 1)) - f xstar) ≤
      ∑ i ∈ Finset.range k,
        (‖X i - xstar‖ ^ 2 - ‖X (i + 1) - xstar‖ ^ 2) / (2 * η) := by
    apply Finset.sum_le_sum
    intro i _
    have h := gradientDescent_one_step hL hconvex hdiff hsmooth hη (X i) xstar
    rw [← hX i] at h
    exact h
  calc
    ∑ i ∈ Finset.range k, (f (X (i + 1)) - f xstar) ≤
        ∑ i ∈ Finset.range k,
          (‖X i - xstar‖ ^ 2 - ‖X (i + 1) - xstar‖ ^ 2) / (2 * η) := hsum
    _ = (‖X 0 - xstar‖ ^ 2 - ‖X k - xstar‖ ^ 2) / (2 * η) :=
      gradientDescent_sum_range_sub_div (fun i => ‖X i - xstar‖ ^ 2) k (2 * η)
    _ ≤ ‖X 0 - xstar‖ ^ 2 / (2 * η) :=
      (div_le_div_iff_of_pos_right (mul_pos (by norm_num) hη.1)).2
        (sub_le_self _ (sq_nonneg _))

/-- **Sublinear rate of gradient descent for smooth convex functions.** Let $E$ be a
finite-dimensional real inner product space, let $L > 0$, and let $f : E \to \mathbb{R}$ be
convex and differentiable with $L$-Lipschitz gradient $\nabla f$. Let $x^\star \in E$ be a global
minimizer of $f$, let $0 < \eta \le 1/L$, and let $(x_k)_{k \ge 0}$ be any sequence in $E$ with
$x_{k+1} = x_k - \eta \nabla f(x_k)$ for all $k$. Then for every $k \ge 1$,
$f(x_k) - f(x^\star) \le \|x_0 - x^\star\|^2 / (2 \eta k)$.

Proves `Wanted` entry `gradient_descent_convex_sublinear_rate`.

Proof: The descent lemma and first-order convexity inequality are proved on affine lines. They
bound each objective gap by a difference of squared distances to $x^\star$; telescoping and the
monotonicity of $f(x_k)$ in $k$ give the rate, as in L. Vandenberghe, ECE236C lecture notes
"Gradient method" (Spring 2022), slides 1.23-1.26.

Sources: `Mathlib/docs/undergrad.yaml`, section `Numerical Analysis` /
`Iterative methods of solving systems of real and vector-valued equations`,
entries `optimization of convex function in finite dimension` and
`gradient descent square root` (unmapped);
Y. Nesterov, Introductory Lectures on Convex Optimization, Section 2.1;
stable ref https://en.wikipedia.org/wiki/Gradient_descent.
-/
theorem gradient_descent_convex_sublinear_rate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E]
    {f : E → ℝ} {L : ℝ} (hL : 0 < L)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f)
    (hsmooth : LipschitzWith ⟨L, le_of_lt hL⟩ (gradient f))
    {xstar : E} (hmin : ∀ x, f xstar ≤ f x)
    {η : ℝ} (hη : η ∈ Set.Ioc 0 (1 / L))
    {X : ℕ → E} (hX : ∀ k, X (k + 1) = X k - η • gradient f (X k)) :
    ∀ k : ℕ, 0 < k →
      f (X k) - f xstar ≤ ‖X 0 - xstar‖ ^ 2 / (2 * η * (k : ℝ)) := by
  intro k hk
  have hanti := gradientDescent_antitone hL hdiff hsmooth hη hX
  have hsum_lower :
      ∑ i ∈ Finset.range k, (f (X k) - f xstar) ≤
        ∑ i ∈ Finset.range k, (f (X (i + 1)) - f xstar) := by
    apply Finset.sum_le_sum
    intro i hi
    exact sub_le_sub_right (hanti (Nat.succ_le_iff.mpr (Finset.mem_range.mp hi))) _
  have hkgap : (k : ℝ) * (f (X k) - f xstar) ≤
      ∑ i ∈ Finset.range k, (f (X (i + 1)) - f xstar) := by
    calc
      (k : ℝ) * (f (X k) - f xstar) =
          ∑ _i ∈ Finset.range k, (f (X k) - f xstar) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.range k, (f (X (i + 1)) - f xstar) := hsum_lower
  have hsum_upper := gradientDescent_sum_bound hL hconvex hdiff hsmooth
    (xstar := xstar) hη hX k
  have hbound : (k : ℝ) * (f (X k) - f xstar) ≤
      ‖X 0 - xstar‖ ^ 2 / (2 * η) := hkgap.trans hsum_upper
  have hgap_nonneg : 0 ≤ f (X k) - f xstar := sub_nonneg.mpr (hmin (X k))
  have hbound_abs : (k : ℝ) * |f (X k) - f xstar| ≤
      ‖X 0 - xstar‖ ^ 2 / (2 * η) := by
    simpa [abs_of_nonneg hgap_nonneg] using hbound
  have htwoη : 0 < 2 * η := mul_pos (by norm_num) hη.1
  have hscaled := (le_div_iff₀ htwoη).mp hbound_abs
  calc
    f (X k) - f xstar = |f (X k) - f xstar| :=
      (abs_of_nonneg hgap_nonneg).symm
    _ ≤ ‖X 0 - xstar‖ ^ 2 / (2 * η * (k : ℝ)) := by
      apply (le_div_iff₀ (mul_pos htwoη (Nat.cast_pos.mpr hk))).2
      calc
        |f (X k) - f xstar| * (2 * η * (k : ℝ)) =
            ((k : ℝ) * |f (X k) - f xstar|) * (2 * η) := by ring
        _ ≤ ‖X 0 - xstar‖ ^ 2 := hscaled

end MetaMathlibExt
