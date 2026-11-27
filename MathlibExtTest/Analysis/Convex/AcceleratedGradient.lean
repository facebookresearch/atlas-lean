/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.AcceleratedGradient
public import MathlibExt.Analysis.Convex.AcceleratedGradientFlow
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Tests for Nesterov's accelerated gradient method and its continuous-time limit

Non-vacuity: the hypotheses of `nesterov_accelerated_rate` are met by an explicit run of the
method on `f x = x² / 2` over `ℝ`, and those of `bregmanLagrangian_rate` and `suBoydCandes_rate`
by explicit non-constant trajectories.
-/

@[expose] public section

namespace MathlibExtTest.AcceleratedGradient

open MathlibExt.Analysis.Convex.AcceleratedGradient
open MathlibExt.Analysis.Convex.AcceleratedGradientFlow

/-- `f x = ‖x‖² / 2`. -/
noncomputable def quadratic {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) : ℝ :=
  (1 / 2 : ℝ) * ‖x‖ ^ 2

theorem quadratic_hasGradientAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (x : E) : HasGradientAt quadratic x x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  change HasFDerivAt (fun y : E => (1 / 2 : ℝ) * ‖y‖ ^ 2)
    ((InnerProductSpace.toDual ℝ E) x) x
  convert! (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1 / 2 : ℝ) using 1
  ext y
  simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]

theorem quadratic_gradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] : gradient (quadratic (E := E)) = id := by
  ext x; exact (quadratic_hasGradientAt x).gradient

theorem quadratic_convexOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ConvexOn ℝ Set.univ (quadratic (E := E)) := by
  change ConvexOn ℝ Set.univ (fun x : E => (1 / 2 : ℝ) * ‖x‖ ^ 2)
  have h : ConvexOn ℝ Set.univ (fun x : E => ‖x‖ ^ 2) :=
    (convexOn_norm (E := E) (s := Set.univ) convex_univ).pow
      (fun (x : E) _ => norm_nonneg x) 2
  simpa only [smul_eq_mul] using h.smul (c := (1 / 2 : ℝ)) (by norm_num)

theorem quadratic_differentiable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] : Differentiable ℝ (quadratic (E := E)) :=
  fun x => (quadratic_hasGradientAt x).differentiableAt

theorem quadratic_lipschitz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :
    LipschitzWith ⟨1, le_of_lt (one_pos : (0 : ℝ) < 1)⟩ (gradient (quadratic (E := E))) := by
  rw [quadratic_gradient]
  exact LipschitzWith.id

/-- The gradient of `x² / 2` is also `2`-Lipschitz, so the method can be run with `L = 2`, where
the gradient step `x ↦ x / 2` does not jump to the minimizer and the momentum is exercised. -/
theorem quadratic_lipschitz_two {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :
    LipschitzWith ⟨2, by norm_num⟩ (gradient (quadratic (E := E))) := by
  rw [quadratic_gradient]
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  change dist x y ≤ (2 : ℝ) * dist x y
  nlinarith [dist_nonneg (x := x) (y := y)]

/-! ## An explicit run of the accelerated method on `x² / 2` over `ℝ`, with `L = 2` -/

/-- The pair `(y k, z k)` of the accelerated method on `x² / 2` (gradient `x`), `L = 2`. -/
noncomputable def run (z₀ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (z₀, z₀)
  | k + 1 =>
    let x := ((k : ℝ) / (k + 2)) * (run z₀ k).1 + (2 / ((k : ℝ) + 2)) * (run z₀ k).2
    (x - (1 / 2) * x, (run z₀ k).2 - (((k : ℝ) + 1) / (2 * 2)) * x)

/-- The coupling point `x (k + 1)` of the run. -/
noncomputable def runX (z₀ : ℝ) : ℕ → ℝ
  | 0 => z₀
  | k + 1 => ((k : ℝ) / (k + 2)) * (run z₀ k).1 + (2 / ((k : ℝ) + 2)) * (run z₀ k).2

/-- The hypotheses of `nesterov_accelerated_rate` hold for the explicit run with `L = 2`, so
the rate applies to it. -/
theorem run_rate (z₀ : ℝ) {k : ℕ} (hk : 0 < k) :
    quadratic (run z₀ k).1 - quadratic (0 : ℝ) ≤
      2 * 2 * ‖(run z₀ 0).2 - 0‖ ^ 2 / ((k : ℝ) * (k + 1)) := by
  refine nesterov_accelerated_rate (L := 2) two_pos quadratic_convexOn quadratic_differentiable
    quadratic_lipschitz_two 0 (x := runX z₀) (y := fun k => (run z₀ k).1)
    (z := fun k => (run z₀ k).2) ?_ ?_ ?_ hk
  · intro k; simp [runX, smul_eq_mul]
  · intro k; simp [run, runX, quadratic_gradient, smul_eq_mul]
  · intro k; simp [run, runX, quadratic_gradient, smul_eq_mul]

/-- The first iterates from `z₀ = 1`: `y₁ = 1/2`, `z₁ = 3/4`, then `y₂ = 1/3`, `z₂ = 5/12`
(the coupling point is `x₂ = 2/3`, a genuine combination of `y₁` and `z₁`). -/
example : run 1 1 = (1 / 2, 3 / 4) := by norm_num [run]

example : run 1 2 = (1 / 3, 5 / 12) := by norm_num [run]

/-! ## Continuous time -/

theorem zero_gradient (x : ℝ) : gradient (fun _ : ℝ => (0 : ℝ)) x = 0 := by
  rw [gradient_eq_deriv']; simp

/-- A non-constant solution of the Euler–Lagrange system with `α = 0`, `β t = t`, `f = 0`:
`X t = e^{-t}`, `Z = 0`; the rate theorem applies to it. -/
example {t : ℝ} (ht : 0 ≤ t) :
    (fun _ : ℝ => (0 : ℝ)) (Real.exp (-t)) - 0 ≤
      energy (fun _ : ℝ => (0 : ℝ)) (fun s => s) (fun s => Real.exp (-s)) (fun _ => 0) 0 0 *
        Real.exp (-t) := by
  refine bregmanLagrangian_rate (α := fun _ => 0) (β' := fun _ => 1) (t₀ := 0)
    (convexOn_const 0 convex_univ) (differentiable_const 0) (fun _ => le_rfl)
    (fun s _ => hasDerivAt_id s) (fun s _ => by simp) (fun s _ => ?_) (fun s _ => ?_) ht
  · have := (hasDerivAt_neg s).exp
    convert this using 1
    simp
  · rw [zero_gradient, smul_zero]
    exact hasDerivAt_const s 0

/-- A non-constant solution of `X'' + (3 / t) X' = 0` (the Su–Boyd–Candès ODE with `f = 0`):
`X t = -1 / (2 t²)`, `V t = 1 / t³` on `[1, ∞)`; the rate theorem applies to it. -/
example {t : ℝ} (ht : 1 ≤ t) :
    (fun _ : ℝ => (0 : ℝ)) (-(t ^ 2)⁻¹ / 2) - 0 ≤
      (2 * ‖(-((1 : ℝ) ^ 2)⁻¹ / 2) + ((1 : ℝ) / 2) • ((1 : ℝ) ^ 3)⁻¹ - 0‖ ^ 2 +
        1 ^ 2 * (0 - 0)) / t ^ 2 := by
  refine suBoydCandes_rate (X := fun s => -(s ^ 2)⁻¹ / 2) (V := fun s => (s ^ 3)⁻¹)
    (convexOn_const 0 convex_univ) (differentiable_const 0) (fun _ => le_rfl) one_pos
    (fun s hs => ?_) (fun s hs => ?_) ht
  · have hs0 : s ≠ 0 := (lt_of_lt_of_le one_pos hs).ne'
    have := ((HasDerivAt.inv (hasDerivAt_pow 2 s) (pow_ne_zero 2 hs0)).neg).div_const 2
    convert this using 1
    field_simp
    push_cast
    ring
  · have hs0 : s ≠ 0 := (lt_of_lt_of_le one_pos hs).ne'
    have := HasDerivAt.inv (hasDerivAt_pow 3 s) (pow_ne_zero 3 hs0)
    rw [zero_gradient, sub_zero, smul_eq_mul]
    convert this using 1
    field_simp
    push_cast
    ring

/-- Time dilation by `τ t = 2 t` of the solution `X t = e^{-t}`, `Z = 0` (`α = 0`, `f = 0`):
the hypotheses of `timeDilation` hold at every `t`. -/
example (t : ℝ) :
    HasDerivAt ((fun s => Real.exp (-s)) ∘ (fun s : ℝ => 2 * s))
        (Real.exp ((fun _ : ℝ => (0 : ℝ)) (2 * t) + Real.log 2) •
          (((fun _ : ℝ => (0 : ℝ)) ∘ (fun s : ℝ => 2 * s)) t -
            ((fun s => Real.exp (-s)) ∘ (fun s : ℝ => 2 * s)) t)) t := by
  refine (timeDilation (f := fun _ : ℝ => (0 : ℝ)) (α := fun _ => 0) (β := fun s => s)
    (τ := fun s : ℝ => 2 * s) (X := fun s => Real.exp (-s)) (Z := fun _ => 0) (t := t) (τ' := 2)
    ?_ two_pos ?_ ?_).1
  · simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
  · have := (hasDerivAt_neg (2 * t)).exp
    convert this using 1
    simp
  · rw [zero_gradient, smul_zero]
    exact hasDerivAt_const _ 0

/-! ## A non-degenerate continuous-time instance: `f x = x² / 2`, `α = β = 0` -/

/-- `ω = √3 / 2`. -/
noncomputable def ω : ℝ := Real.sqrt 3 / 2

theorem ω_sq : ω ^ 2 = 3 / 4 := by
  rw [ω, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num

/-- The damped oscillation `X t = e^{-t/2} cos (ω t)`. -/
noncomputable def oscX (t : ℝ) : ℝ := Real.exp (-t / 2) * Real.cos (ω * t)

/-- `Z t = X t + X' t = e^{-t/2} (cos (ω t) / 2 - ω sin (ω t))`. -/
noncomputable def oscZ (t : ℝ) : ℝ :=
  Real.exp (-t / 2) * (Real.cos (ω * t) / 2 - ω * Real.sin (ω * t))

theorem hasDerivAt_oscX (t : ℝ) : HasDerivAt oscX (oscZ t - oscX t) t := by
  have he : HasDerivAt (fun s => Real.exp (-s / 2)) (Real.exp (-t / 2) * (-1 / 2)) t := by
    have := ((hasDerivAt_neg t).div_const 2).exp
    simpa [neg_div] using this
  have hc : HasDerivAt (fun s => Real.cos (ω * s)) (-Real.sin (ω * t) * ω) t := by
    have := HasDerivAt.cos (HasDerivAt.const_mul ω (hasDerivAt_id t))
    convert this using 1 <;> simp
  refine HasDerivAt.congr_deriv (f := oscX) (he.mul hc) ?_
  simp only [oscX, oscZ]; ring

theorem hasDerivAt_oscZ (t : ℝ) : HasDerivAt oscZ (-oscX t) t := by
  have he : HasDerivAt (fun s => Real.exp (-s / 2)) (Real.exp (-t / 2) * (-1 / 2)) t := by
    have := ((hasDerivAt_neg t).div_const 2).exp
    simpa [neg_div] using this
  have hc : HasDerivAt (fun s => Real.cos (ω * s)) (-Real.sin (ω * t) * ω) t := by
    have := HasDerivAt.cos (HasDerivAt.const_mul ω (hasDerivAt_id t))
    convert this using 1 <;> simp
  have hs : HasDerivAt (fun s => Real.sin (ω * s)) (Real.cos (ω * t) * ω) t := by
    have := HasDerivAt.sin (HasDerivAt.const_mul ω (hasDerivAt_id t))
    convert this using 1 <;> simp
  refine HasDerivAt.congr_deriv (f := oscZ) (he.mul ((hc.div_const 2).sub (hs.const_mul ω))) ?_
  simp only [oscX]
  linear_combination (-(Real.exp (-t / 2) * Real.cos (ω * t))) * ω_sq

/-- With `f x = x² / 2` (so `∇f = id`), `α = β = 0` (ideal scaling `0 ≤ e^0`), the damped
oscillation `(oscX, oscZ)` solves the Euler–Lagrange system `X' = Z - X`, `Z' = -∇f(X)`, and the
energy bound applies: `X t² / 2 ≤ 𝓔 0` for `t ≥ 0`. -/
example {t : ℝ} (ht : 0 ≤ t) :
    quadratic (oscX t) - quadratic (0 : ℝ) ≤
      energy quadratic (fun _ => 0) oscX oscZ 0 0 * Real.exp (-(fun _ : ℝ => (0 : ℝ)) t) :=
  bregmanLagrangian_rate (α := fun _ => 0) (β' := fun _ => 0) quadratic_convexOn
    quadratic_differentiable (fun x => by simp [quadratic]; positivity)
    (fun s _ => hasDerivAt_const s 0) (fun s _ => by simp)
    (fun s _ => by simpa using hasDerivAt_oscX s)
    (fun s _ => by simpa [quadratic_gradient] using hasDerivAt_oscZ s) ht

end MathlibExtTest.AcceleratedGradient
