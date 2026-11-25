/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.GradientDescent
public import MathlibExt.Analysis.Convex.GradientDescentStronglyConvex

/-!
# Co-coercivity and expansiveness of the gradient step

For a differentiable function `f` on a real Hilbert space whose gradient is `β`-Lipschitz, the
gradient update `G(w) = w - α ∇f(w)` is `(1 + α β)`-Lipschitz; if `f` is moreover convex, its
gradient is co-coercive, `⟪∇f(v) - ∇f(w), v - w⟫ ≥ ‖∇f(v) - ∇f(w)‖² / β`, and for
`0 ≤ α ≤ 2 / β` the gradient update is non-expansive (M. Hardt, B. Recht and Y. Singer, *Train
faster, generalize better: stability of stochastic gradient descent*, ICML 2016,
arXiv:1509.01240, Lemma 3.7 and Appendix A). If `f` is `L`-Lipschitz, the step moves by at most
`α L` (ibid., Lemma 3.3). These are the update-rule properties behind the stability of
stochastic gradient descent.

## Main results

- `inner_gradient_sub_ge`: co-coercivity of the gradient of a convex function with Lipschitz
  gradient.
- `norm_gradientStep_sub_le_one_add_mul`: the gradient update is `(1 + α β)`-expansive.
- `norm_gradientStep_sub_le`: for convex `f` and `0 ≤ α ≤ 2 / β`, it is `1`-expansive.
- `norm_smul_gradient_le`: for `L`-Lipschitz `f`, it is `α L`-bounded.
-/

@[expose] public section

open MetaMathlibExt MathlibExt.Analysis.Convex.GradientDescentStronglyConvex

namespace MathlibExt.Analysis.Convex.Cocoercivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The convex upper model: for convex `f` with `β`-Lipschitz gradient,
`f x + ⟪∇f(x), y - x⟫ + ‖∇f(y) - ∇f(x)‖² / (2 β) ≤ f y`. -/
private theorem add_inner_add_norm_sq_le {f : E → ℝ} {β : ℝ} (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (hsmooth : LipschitzWith ⟨β, hβ.le⟩ (gradient f)) (x y : E) :
    f x + inner ℝ (gradient f x) (y - x) +
      ‖gradient f y - gradient f x‖ ^ 2 / (2 * β) ≤ f y := by
  set g := gradient f y - gradient f x with hg
  set d : E := -(1 / β) • g with hd
  have hc := add_inner_add_le_of_strongConvexOn (strongConvexOn_zero.mpr hconv)
    (Set.mem_univ x) (Set.mem_univ (y + d)) (hdiff x).hasGradientAt
  have hdesc := gradientDescent_descent_lemma hβ.le hdiff hsmooth y d
  have hsplit : inner ℝ (gradient f x) (y + d - x) =
      inner ℝ (gradient f x) (y - x) + inner ℝ (gradient f x) d := by
    rw [← inner_add_right]; congr 1; abel
  have hgd : inner ℝ (gradient f y) d - inner ℝ (gradient f x) d = -(1 / β) * ‖g‖ ^ 2 := by
    rw [← inner_sub_left, ← hg, hd, inner_smul_right, real_inner_self_eq_norm_sq]
  have hnd : ‖d‖ ^ 2 = (1 / β) ^ 2 * ‖g‖ ^ 2 := by
    rw [hd, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity), mul_pow]
  rw [hsplit] at hc
  simp only [zero_div, zero_mul, add_zero] at hc
  have key : ‖g‖ ^ 2 / (2 * β) = (1 / β) * ‖g‖ ^ 2 - β / 2 * ((1 / β) ^ 2 * ‖g‖ ^ 2) := by
    field_simp; ring
  rw [key]
  nlinarith [hc, hdesc, hgd, hnd]

/-- **Co-coercivity of the gradient.** If `f` is convex and differentiable on a real Hilbert
space and its gradient is `β`-Lipschitz (`β > 0`), then for all `v, w`,
`(1 / β) ‖∇f(v) - ∇f(w)‖² ≤ ⟪∇f(v) - ∇f(w), v - w⟫`.

Source: M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of
stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Appendix A, inequality (A.1) in the proof
of Lemma 3.7.2 (stated there without proof). The proof here adds the convex upper model
`f x + ⟪∇f(x), y - x⟫ + ‖∇f(y) - ∇f(x)‖² / (2 β) ≤ f y`, obtained from the first-order convexity
inequality at `x` and the descent lemma at `y` with the step `-(1/β)(∇f(y) - ∇f(x))`, to its
counterpart with `x` and `y` exchanged. -/
theorem inner_gradient_sub_ge {f : E → ℝ} {β : ℝ} (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (hsmooth : LipschitzWith ⟨β, hβ.le⟩ (gradient f)) (v w : E) :
    1 / β * ‖gradient f v - gradient f w‖ ^ 2 ≤
      inner ℝ (gradient f v - gradient f w) (v - w) := by
  have h1 := add_inner_add_norm_sq_le hβ hconv hdiff hsmooth v w
  have h2 := add_inner_add_norm_sq_le hβ hconv hdiff hsmooth w v
  rw [norm_sub_rev (gradient f w) (gradient f v)] at h1
  have hinner : inner ℝ (gradient f v - gradient f w) (v - w) =
      -inner ℝ (gradient f v) (w - v) - inner ℝ (gradient f w) (v - w) := by
    rw [inner_sub_left, ← inner_neg_right, neg_sub]
  rw [hinner]
  have : 1 / β * ‖gradient f v - gradient f w‖ ^ 2 =
      ‖gradient f v - gradient f w‖ ^ 2 / (2 * β) +
        ‖gradient f v - gradient f w‖ ^ 2 / (2 * β) := by
    field_simp; ring
  rw [this]
  linarith

/-- **The gradient update is `(1 + α β)`-expansive.** If the gradient of `f` is `β`-Lipschitz and
`α ≥ 0`, then the gradient update `G(w) = w - α ∇f(w)` satisfies
`‖G(v) - G(w)‖ ≤ (1 + α β) ‖v - w‖`.

Source: M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of
stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Lemma 3.7.1 (proof in Appendix A). -/
theorem norm_gradientStep_sub_le_one_add_mul {f : E → ℝ} {β : ℝ} (hβ : 0 ≤ β)
    (hsmooth : LipschitzWith ⟨β, hβ⟩ (gradient f)) {α : ℝ} (hα : 0 ≤ α) (v w : E) :
    ‖(v - α • gradient f v) - (w - α • gradient f w)‖ ≤ (1 + α * β) * ‖v - w‖ := by
  have hrw : (v - α • gradient f v) - (w - α • gradient f w) =
      (v - w) - α • (gradient f v - gradient f w) := by
    rw [smul_sub]; abel
  rw [hrw]
  have hL : ‖gradient f v - gradient f w‖ ≤ β * ‖v - w‖ := by
    have := hsmooth.dist_le_mul v w
    rw [dist_eq_norm, dist_eq_norm] at this
    exact this
  calc ‖(v - w) - α • (gradient f v - gradient f w)‖
      ≤ ‖v - w‖ + ‖α • (gradient f v - gradient f w)‖ := norm_sub_le _ _
    _ = ‖v - w‖ + α * ‖gradient f v - gradient f w‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hα]
    _ ≤ ‖v - w‖ + α * (β * ‖v - w‖) := by gcongr
    _ = (1 + α * β) * ‖v - w‖ := by ring

/-- **The gradient update of a convex smooth function is non-expansive.** If `f` is convex and
differentiable on a real Hilbert space with `β`-Lipschitz gradient (`β > 0`) and
`0 ≤ α ≤ 2 / β`, then the gradient update `G(w) = w - α ∇f(w)` satisfies
`‖G(v) - G(w)‖ ≤ ‖v - w‖`.

Source: M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of
stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Lemma 3.7.2 (proof in Appendix A, from
co-coercivity (A.1)). -/
theorem norm_gradientStep_sub_le {f : E → ℝ} {β : ℝ} (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (hsmooth : LipschitzWith ⟨β, hβ.le⟩ (gradient f)) {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 2 / β)
    (v w : E) :
    ‖(v - α • gradient f v) - (w - α • gradient f w)‖ ≤ ‖v - w‖ := by
  have hrw : (v - α • gradient f v) - (w - α • gradient f w) =
      (v - w) - α • (gradient f v - gradient f w) := by
    rw [smul_sub]; abel
  rw [hrw]
  have hco := inner_gradient_sub_ge hβ hconv hdiff hsmooth v w
  set g := gradient f v - gradient f w
  have hsq : ‖(v - w) - α • g‖ ^ 2 =
      ‖v - w‖ ^ 2 - 2 * α * inner ℝ g (v - w) + α ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_comm]
    ring
  have hαβ : 0 ≤ 2 / β - α := by linarith
  have hfac : α * (2 / β - α) * ‖g‖ ^ 2 = 2 * α * (1 / β * ‖g‖ ^ 2) - α ^ 2 * ‖g‖ ^ 2 := by
    field_simp
  have hnn : 0 ≤ α * (2 / β - α) * ‖g‖ ^ 2 := by positivity
  have hle : ‖(v - w) - α • g‖ ^ 2 ≤ ‖v - w‖ ^ 2 := by
    rw [hsq]
    nlinarith [mul_le_mul_of_nonneg_left hco (by linarith : (0 : ℝ) ≤ 2 * α)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hle

/-- **The gradient update of a Lipschitz function is `α L`-bounded.** If `f` is `L`-Lipschitz on
a real Hilbert space and `α ≥ 0`, then the gradient update `G(w) = w - α ∇f(w)` moves every point
by at most `α L`: `‖α ∇f(w)‖ ≤ α L`.

Source: M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of
stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Lemma 3.3. -/
theorem norm_smul_gradient_le {f : E → ℝ} {L : NNReal} (hf : LipschitzWith L f) {α : ℝ}
    (hα : 0 ≤ α) (w : E) : ‖α • gradient f w‖ ≤ α * L := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hα]
  gcongr
  rw [gradient, LinearIsometryEquiv.norm_map]
  exact norm_fderiv_le_of_lipschitz ℝ hf

end MathlibExt.Analysis.Convex.Cocoercivity
