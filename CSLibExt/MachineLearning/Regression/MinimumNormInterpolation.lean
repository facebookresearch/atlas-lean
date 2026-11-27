/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Implicit regularization of stochastic gradient descent in linear models

For a linear model `x ↦ ⟪w, x⟫` fitted to data points `x₁, …, xₙ`, every stochastic gradient update
has the form `w_{t+1} = w_t - η_t e_t x_{i_t}` with a scalar prediction error `e_t`. Started from
`w₀ = 0`, the iterates stay in the span of the data points; and an interpolating solution in that
span is the unique one of minimum norm. Hence, if SGD converges to a solution of `⟪w, xᵢ⟫ = yᵢ`
for all `i`, it converges to the minimum-norm solution (C. Zhang, S. Bengio, M. Hardt, B. Recht and
O. Vinyals, *Understanding deep learning requires rethinking generalization*, ICLR 2017,
arXiv:1611.03530, Section 5).

## Main results

- `sgdIterate_mem_span`: SGD iterates from `0` lie in the span of the data.
- `norm_le_of_mem_span_of_interpolates`: an interpolant in the span has minimum norm among all
  interpolants.
- `eq_of_mem_span_of_interpolates`: it is the unique interpolant in the span.
- `norm_le_of_tendsto_sgdIterate`: a limit of SGD from `0` that interpolates the data is a
  minimum-norm interpolant.
-/

@[expose] public section

open Filter Topology
open scoped InnerProductSpace

namespace CSLibExt.MachineLearning.MinimumNormInterpolation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Stochastic gradient iterates of a linear model.** For data points `x : Fin n → E`, indices
`ι t`, step sizes `η t` and scalar prediction errors `e t`, the iterates `w₀ = 0` and
`w_{t+1} = w_t - η_t e_t x_{ι t}`. For a loss `ℓ(⟪w, x⟫, y)`, the gradient at the example `i` is
`ℓ'(⟪w, xᵢ⟫, yᵢ) xᵢ`, so every stochastic gradient run on the linear model is of this form.

Source: C. Zhang, S. Bengio, M. Hardt, B. Recht and O. Vinyals, *Understanding deep learning
requires rethinking generalization*, ICLR 2017, arXiv:1611.03530, Section 5 (the update
`w_{t+1} = w_t - η_t e_t x_{i_t}` with `w₀ = 0`). -/
def sgdIterate {n : ℕ} (x : Fin n → E) (ι : ℕ → Fin n) (η e : ℕ → ℝ) : ℕ → E
  | 0 => 0
  | t + 1 => sgdIterate x ι η e t - (η t * e t) • x (ι t)

/-- **SGD from zero stays in the span of the data.** Every iterate `sgdIterate x ι η e t` lies in
the span of the data points `x₁, …, xₙ`: it is `Xᵀ α` for some coefficients `α`.

Source: C. Zhang, S. Bengio, M. Hardt, B. Recht and O. Vinyals, *Understanding deep learning
requires rethinking generalization*, ICLR 2017, arXiv:1611.03530, Section 5 ("if `w₀ = 0`, we must
have that the solution has the form `w = ∑ᵢ αᵢ xᵢ`"). -/
theorem sgdIterate_mem_span {n : ℕ} (x : Fin n → E) (ι : ℕ → Fin n) (η e : ℕ → ℝ) (t : ℕ) :
    sgdIterate x ι η e t ∈ Submodule.span ℝ (Set.range x) := by
  induction t with
  | zero => exact Submodule.zero_mem _
  | succ t ih =>
    exact Submodule.sub_mem _ ih
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨ι t, rfl⟩))

private theorem inner_eq_zero_of_interpolates {n : ℕ} {x : Fin n → E} {w w' : E}
    (hw : w ∈ Submodule.span ℝ (Set.range x)) {y : Fin n → ℝ} (hy : ∀ i, ⟪w, x i⟫_ℝ = y i)
    (hy' : ∀ i, ⟪w', x i⟫_ℝ = y i) : ⟪w, w' - w⟫_ℝ = 0 := by
  have horth : w' - w ∈ (Submodule.span ℝ (Set.range x))ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    refine Submodule.span_induction (p := fun u _ => ⟪w' - w, u⟫_ℝ = 0) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨i, rfl⟩
      rw [inner_sub_left, hy i, hy' i, sub_self]
    · exact inner_zero_right _
    · intro a b _ _ ha hb
      rw [inner_add_right, ha, hb, add_zero]
    · intro c a _ ha
      rw [inner_smul_right, ha, mul_zero]
  exact Submodule.inner_right_of_mem_orthogonal hw horth

/-- **An interpolant in the span of the data has minimum norm.** If `w` lies in the span of the
data points and `⟪w, xᵢ⟫ = yᵢ` for every `i`, then every `w'` with `⟪w', xᵢ⟫ = yᵢ` for every `i`
satisfies `‖w‖ ≤ ‖w'‖`: `w` is the minimum-norm solution of `X w = y`.

Source: C. Zhang, S. Bengio, M. Hardt, B. Recht and O. Vinyals, *Understanding deep learning
requires rethinking generalization*, ICLR 2017, arXiv:1611.03530, Section 5 ("simple algebra
reveals that it is equivalent to the minimum `ℓ₂`-norm solution of `Xw = y`"). -/
theorem norm_le_of_mem_span_of_interpolates {n : ℕ} {x : Fin n → E} {w : E}
    (hw : w ∈ Submodule.span ℝ (Set.range x)) {y : Fin n → ℝ} (hy : ∀ i, ⟪w, x i⟫_ℝ = y i)
    {w' : E} (hy' : ∀ i, ⟪w', x i⟫_ℝ = y i) : ‖w‖ ≤ ‖w'‖ := by
  have h0 := inner_eq_zero_of_interpolates hw hy hy'
  have hsq : ‖w'‖ ^ 2 = ‖w‖ ^ 2 + ‖w' - w‖ ^ 2 := by
    have : w' = w + (w' - w) := by abel
    conv_lhs => rw [this]
    rw [norm_add_sq_real, h0]
    ring
  have hle : ‖w‖ ^ 2 ≤ ‖w'‖ ^ 2 := by rw [hsq]; nlinarith [sq_nonneg ‖w' - w‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hle

/-- **The interpolant in the span of the data is unique.** If `w` and `w'` both lie in the span of
the data points and both satisfy `⟪·, xᵢ⟫ = yᵢ` for every `i`, then `w = w'`.

Source: C. Zhang, S. Bengio, M. Hardt, B. Recht and O. Vinyals, *Understanding deep learning
requires rethinking generalization*, ICLR 2017, arXiv:1611.03530, Section 5 (equation (3),
`X Xᵀ α = y`, "has a unique solution"; uniqueness of `w = Xᵀ α` holds without assuming that `X` has
rank `n`). -/
theorem eq_of_mem_span_of_interpolates {n : ℕ} {x : Fin n → E} {w w' : E}
    (hw : w ∈ Submodule.span ℝ (Set.range x)) (hw' : w' ∈ Submodule.span ℝ (Set.range x))
    {y : Fin n → ℝ} (hy : ∀ i, ⟪w, x i⟫_ℝ = y i) (hy' : ∀ i, ⟪w', x i⟫_ℝ = y i) : w = w' := by
  have h1 := inner_eq_zero_of_interpolates hw hy hy'
  have h2 := inner_eq_zero_of_interpolates hw' hy' hy
  have h : ⟪w' - w, w' - w⟫_ℝ = 0 := by
    rw [inner_sub_left, h1, ← neg_sub w w', inner_neg_right, h2]
    simp
  exact (sub_eq_zero.mp (inner_self_eq_zero.mp h)).symm

/-- **A limit of SGD from zero that interpolates is the minimum-norm interpolant.** Let the
stochastic gradient iterates of the linear model, started at `0`, converge to `w`, and let `w`
interpolate the data, `⟪w, xᵢ⟫ = yᵢ` for every `i`. Then `‖w‖ ≤ ‖w'‖` for every interpolant `w'`.

Source: C. Zhang, S. Bengio, M. Hardt, B. Recht and O. Vinyals, *Understanding deep learning
requires rethinking generalization*, ICLR 2017, arXiv:1611.03530, Section 5 ("out of all models
that exactly fit the data, SGD will often converge to the solution with minimum norm"; the
convergence of SGD is assumed here, not proved). -/
theorem norm_le_of_tendsto_sgdIterate {n : ℕ} {x : Fin n → E} {ι : ℕ → Fin n} {η e : ℕ → ℝ}
    {w : E} (hlim : Tendsto (sgdIterate x ι η e) atTop (𝓝 w)) {y : Fin n → ℝ}
    (hy : ∀ i, ⟪w, x i⟫_ℝ = y i) {w' : E} (hy' : ∀ i, ⟪w', x i⟫_ℝ = y i) : ‖w‖ ≤ ‖w'‖ := by
  have : FiniteDimensional ℝ (Submodule.span ℝ (Set.range x)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range x)
  have hclosed : IsClosed (Submodule.span ℝ (Set.range x) : Set E) :=
    Submodule.closed_of_finiteDimensional _
  have hw : w ∈ Submodule.span ℝ (Set.range x) :=
    hclosed.mem_of_tendsto hlim (Eventually.of_forall fun t => sgdIterate_mem_span x ι η e t)
  exact norm_le_of_mem_span_of_interpolates hw hy hy'

end CSLibExt.MachineLearning.MinimumNormInterpolation
