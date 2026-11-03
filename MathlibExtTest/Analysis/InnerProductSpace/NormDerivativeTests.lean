/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.NormDerivative
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for the Fréchet derivative of the norm in a Hilbert space

* `reInnerSL ℝ` on `ℝ²` at `(3, 4)`, applied to `(1, 2)`, is `11`.
* The derivative of the norm at `(3, 4)` in the direction `(1, 0)` is `3 / 5`,
  and it has operator norm `1`.
* On `ℂ²`, the derivative of the norm at `(1, 0)` in the direction `(I, 0)` is `0`.
* The squared-distance gradient on `ℝ²`: at `x = (3, 4)`, `a = (1, 0)`, in
  direction `(1, 1)`, the derivative is `12`.
* The unit circle in `ℝ²` has velocity orthogonal to position.
* The orthogonal projection onto the `x`-axis sends `(3, 4)` to `(3, 0)`, the
  distance from `(3, 4)` to the `x`-axis is `4`, and the squared distance to
  the `x`-axis is differentiable at `(3, 4)` with gradient twice the
  residual `(0, 4)`.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.InnerProductSpace.NormDerivativeTests

open MathlibExt.Analysis.InnerProductSpace.NormDerivative

/-- The norming functional on `ℝ²` at `(3, 4)`, applied to `(1, 2)`, is `11`. -/
example : reInnerSL ℝ (WithLp.toLp 2 ![3, 4] : EuclideanSpace ℝ (Fin 2))
    (WithLp.toLp 2 ![1, 2]) = 11 := by
  simp [reInnerSL_apply, EuclideanSpace.inner_toLp_toLp]
  norm_num

/-- `(3, 4) ≠ 0` in `ℝ²`. -/
example : (WithLp.toLp 2 ![3, 4] : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by simp

/-- The derivative of the norm at `(3, 4)` in the direction `(1, 0)` is `3 / 5`. -/
example : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 2) => ‖z‖)
      (WithLp.toLp 2 ![3, 4]) (WithLp.toLp 2 ![1, 0]) = 3 / 5 := by
  have hx : (WithLp.toLp 2 ![3, 4] : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by simp
  have hnorm : ‖(WithLp.toLp 2 ![3, 4] : EuclideanSpace ℝ (Fin 2))‖ = 5 := by
    rw [EuclideanSpace.norm_eq]
    rw [show (∑ i, ‖(WithLp.toLp 2 ![3, 4] : EuclideanSpace ℝ (Fin 2)) i‖ ^ 2) = 25 by
      simp [Fin.sum_univ_two]
      norm_num]
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [fderiv_norm_apply_real hx, hnorm]
  simp [EuclideanSpace.inner_toLp_toLp]

/-- The derivative of the norm at `(3, 4)` has operator norm `1`. -/
example : ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 2) => ‖z‖)
      (WithLp.toLp 2 ![3, 4])‖ = 1 :=
  norm_fderiv_norm ℝ (by simp)

/-- On `ℂ²`, the derivative of the norm at `(1, 0)` in the direction `(I, 0)` is `0`. -/
example : fderiv ℝ (fun z : EuclideanSpace ℂ (Fin 2) => ‖z‖)
      (WithLp.toLp 2 ![1, 0]) (WithLp.toLp 2 ![Complex.I, 0]) = 0 := by
  have hx : (WithLp.toLp 2 ![1, 0] : EuclideanSpace ℂ (Fin 2)) ≠ 0 := by simp
  rw [fderiv_norm_apply (K := ℂ) hx]
  simp [PiLp.inner_apply, Fin.sum_univ_two, EuclideanSpace.norm_eq]

/-- The squared-distance gradient on `ℝ²`: at `x = (3, 4)`, `a = (1, 0)`, in
direction `(1, 1)`, the derivative is `12`. -/
example : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 2) => dist z (WithLp.toLp 2 ![1, 0]) ^ 2)
    (WithLp.toLp 2 ![3, 4]) (WithLp.toLp 2 ![1, 1]) = 12 := by
  rw [fderiv_dist_sq_apply (K := ℝ)]
  simp [inner_sub_left, EuclideanSpace.inner_toLp_toLp]
  norm_num

/-- The unit circle in `ℝ²`, traversed with the usual parametrization, has
velocity orthogonal to position: an instance of the sphere-tangency theorem. -/
example (t : ℝ) :
    RCLike.re (inner ℝ
      (Real.cos t • (WithLp.toLp 2 ![1, 0] : EuclideanSpace ℝ (Fin 2)) +
        Real.sin t • (WithLp.toLp 2 ![0, 1] : EuclideanSpace ℝ (Fin 2)))
      (deriv (fun s => Real.cos s • (WithLp.toLp 2 ![1, 0] : EuclideanSpace ℝ (Fin 2)) +
        Real.sin s • (WithLp.toLp 2 ![0, 1] : EuclideanSpace ℝ (Fin 2))) t)) = 0 := by
  have hdiff : Differentiable ℝ (fun s => Real.cos s •
      (WithLp.toLp 2 ![1, 0] : EuclideanSpace ℝ (Fin 2)) +
        Real.sin s • (WithLp.toLp 2 ![0, 1] : EuclideanSpace ℝ (Fin 2))) :=
    (Differentiable.smul_const Real.differentiable_cos _).add
      (Differentiable.smul_const Real.differentiable_sin _)
  have hnorm : ∀ s : ℝ, ‖Real.cos s • (WithLp.toLp 2 ![1, 0] : EuclideanSpace ℝ (Fin 2)) +
        Real.sin s • (WithLp.toLp 2 ![0, 1] : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    intro s
    have hcoord : ∀ i : Fin 2,
        (Real.cos s • (WithLp.toLp 2 ![1, 0] : EuclideanSpace ℝ (Fin 2)) +
          Real.sin s • (WithLp.toLp 2 ![0, 1] : EuclideanSpace ℝ (Fin 2))) i
          = ![Real.cos s, Real.sin s] i := by
      intro i
      fin_cases i <;> simp
    rw [EuclideanSpace.norm_eq]
    simp only [hcoord]
    rw [Fin.sum_univ_two]
    simp [Real.cos_sq_add_sin_sq]
  exact re_inner_self_deriv_eq_zero_of_forall_norm_eq_one (K := ℝ) hdiff hnorm t

/-- The orthogonal projection onto the `x`-axis in `ℝ²` sends `(3, 4)` to `(3, 0)`. -/
theorem starProjection_xAxis_apply :
    (Submodule.span ℝ {(WithLp.toLp 2 ![1, 0] : EuclideanSpace ℝ (Fin 2))}).starProjection
      (WithLp.toLp 2 ![3, 4]) = WithLp.toLp 2 ![3, 0] := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · have h3 : (WithLp.toLp 2 ![3, 0] : EuclideanSpace ℝ (Fin 2))
        = (3 : ℝ) • WithLp.toLp 2 ![1, 0] := by
      ext i
      fin_cases i <;> simp
    rw [h3]
    exact Submodule.smul_mem
      (Submodule.span ℝ {(WithLp.toLp 2 ![1, 0] : EuclideanSpace ℝ (Fin 2))}) (3 : ℝ)
      (Submodule.subset_span (Set.mem_singleton _))
  · intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    simp [inner_smul_right, inner_sub_left, EuclideanSpace.inner_toLp_toLp]

/-- The distance from `(3, 4)` to the `x`-axis in `ℝ²` is `4`. -/
example : Metric.infDist (WithLp.toLp 2 ![3, 4] : EuclideanSpace ℝ (Fin 2))
    ((Submodule.span ℝ {(WithLp.toLp 2 ![1, 0] : EuclideanSpace ℝ (Fin 2))}) : Set _) = 4 := by
  rw [infDist_eq_norm_sub_starProjection (K := ℝ), starProjection_xAxis_apply,
    ← WithLp.toLp_sub, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two]

/-- The squared distance to the `x`-axis in `ℝ²` is differentiable at `(3, 4)`,
with gradient given by twice the residual `(0, 4)`. -/
example : HasStrictFDerivAt
    (fun y : EuclideanSpace ℝ (Fin 2) => Metric.infDist y
      ((Submodule.span ℝ {(WithLp.toLp 2 ![1, 0] : EuclideanSpace ℝ (Fin 2))}) : Set _) ^ 2)
    (2 • reInnerSL ℝ ((WithLp.toLp 2 ![3, 4]) -
      (Submodule.span ℝ {(WithLp.toLp 2 ![1, 0] : EuclideanSpace ℝ (Fin 2))}).starProjection
        (WithLp.toLp 2 ![3, 4]))) (WithLp.toLp 2 ![3, 4]) :=
  hasStrictFDerivAt_infDist_sq (K := ℝ) (WithLp.toLp 2 ![3, 4])

end MathlibExtTest.Analysis.InnerProductSpace.NormDerivativeTests
