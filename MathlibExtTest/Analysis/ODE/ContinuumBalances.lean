/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.ContinuumBalances

@[expose] public section

open Set
open MathlibExt.Analysis.ODE.GreensOperator (sineBasisFun)
open MathlibExt.Analysis.ODE.DirichletSineEigenfunctions
open MathlibExt.Analysis.ODE.ContinuumBalances

namespace MathlibExtTest.Analysis.ODE.ContinuumBalances

/-!
# Tests for continuum balances and the diffusion equation

Concrete checks: positive cell widths, a three-cell no-flux slab, boundary-flux telescoping,
integral balances with increasing, reversed and equal endpoints, the variable-diffusivity
counterexample `D x = x`, `u x = x²`, a steady linear profile, the first heat mode, its energy
decay, and uniqueness for data equal to the first mode or to zero.
-/

/-! ## Finite volumes -/

/-- A no-flux slab of three cells of width `1/2` with concentrations `1, 2, 3` and interior
fluxes `1, -2`: one step with `τ = 1/10` gives `4/5, 13/5, 13/5`. -/
example : (fun i : Fin 3 =>
    ![1, 2, 3] i + (1 / 10 : ℝ) * discreteBalance ⟨1 / 2, by norm_num⟩ ![0, 1, -2, 0] i) =
      ![4 / 5, 13 / 5, 13 / 5] := by
  funext i
  fin_cases i <;> simp [discreteBalance] <;> norm_num

/-- The same step preserves the total concentration `6` exactly. -/
example : ∑ i : Fin 3,
    (![1, 2, 3] i + (1 / 10 : ℝ) * discreteBalance ⟨1 / 2, by norm_num⟩ ![0, 1, -2, 0] i) = 6 := by
  rw [sum_add_mul_discreteBalance_of_noFlux _ _ _ rfl rfl, Fin.sum_univ_three]
  norm_num

/-- With boundary fluxes `F 0 = 1` and `F 3 = 3` the interior fluxes cancel and the total
change is `-(3 - 1) / (1/2) = -4`. -/
example : totalDiscreteChange ⟨1 / 2, by norm_num⟩ ![1, 4, -2, 3] = -4 := by
  rw [totalDiscreteChange_eq]
  simp [Fin.last]
  norm_num

/-- A finite-volume width must carry a positivity proof; zero and negative reals are rejected. -/
example : True := by
  fail_if_success
    have _ := discreteBalance (0 : ℝ) ![1, 3] (0 : Fin 1)
  fail_if_success
    have _ := discreteBalance (-1 : ℝ) ![1, 3] (0 : Fin 1)
  trivial

/-- Multiplying by the positive width recovers the boundary-flux difference. -/
example {n : ℕ} (Δx : {x : ℝ // 0 < x}) (F : Fin (n + 1) → ℝ) :
    (Δx : ℝ) * totalDiscreteChange Δx F = F 0 - F (Fin.last n) := by
  rw [totalDiscreteChange_eq]
  field_simp [ne_of_gt Δx.property]
  ring

/-! ## Integral balance and divergence-form diffusion -/

/-- Density `u = t`, flux `q = -x`, no source: `∂ₜu + ∂ₓq = 1 - 1 = 0`, and
`d/dt ∫₀¹ u = q(0) - q(1) = 1`. -/
example (t : ℝ) : HasDerivAt (fun τ => ∫ _ in (0 : ℝ)..1, τ) 1 t := by
  have h := hasDerivAt_integral_of_localConservation (u := fun τ _ => τ) (q := fun _ x => -x)
    (s := fun _ _ => 0) (a := 0) (b := 1) (t := t) contDiff_fst contDiff_snd.neg
    fun x _ => by simp [localConservation]
  simpa [integralBalance] using h

/-- Reversed endpoints give the signed derivative `-1`, not the geometric amount's `1`. -/
example (t : ℝ) : HasDerivAt (fun τ => ∫ _ in (1 : ℝ)..0, τ) (-1) t := by
  have h := hasDerivAt_integral_of_localConservation (u := fun τ _ => τ) (q := fun _ x => -x)
    (s := fun _ _ => 0) (a := 1) (b := 0) (t := t) contDiff_fst contDiff_snd.neg
    fun x _ => by simp [localConservation]
  simpa [integralBalance] using h

/-- Coincident endpoints give zero signed amount and zero balance. -/
example (t : ℝ) : HasDerivAt (fun τ => ∫ _ in (1 : ℝ)..1, τ) 0 t := by
  have h := hasDerivAt_integral_of_localConservation (u := fun τ _ => τ) (q := fun _ x => -x)
    (s := fun _ _ => 0) (a := 1) (b := 1) (t := t) contDiff_fst contDiff_snd.neg
    fun x _ => by simp [localConservation]
  simpa [integralBalance] using h

/-- The counterexample `D x = x`, `u x = x²` at `x = 1`: `∂ₓ(D ∂ₓu) = 4` but `D ∂ₓₓu = 2`. -/
example : deriv (fun y : ℝ => y * deriv (fun z : ℝ => z ^ 2) y) 1 ≠
    1 * iteratedDeriv 2 (fun z : ℝ => z ^ 2) 1 := by
  rw [(deriv_id_mul_deriv_sq 1).1, (deriv_id_mul_deriv_sq 1).2]
  norm_num

/-- The product rule restores the missing term: `D' ∂ₓu + D ∂ₓₓu = 1 · 2x + x · 2 = 4x`. -/
example (x : ℝ) : deriv (fun y : ℝ => y) x * deriv (fun z : ℝ => z ^ 2) x +
    x * iteratedDeriv 2 (fun z : ℝ => z ^ 2) x = 4 * x := by
  have hd : deriv (fun z : ℝ => z ^ 2) = fun z => 2 * z := funext fun z => by
    rw [show (fun z : ℝ => z ^ 2) = fun z => z * z from funext fun z => sq z,
      ((hasDerivAt_id' z).fun_mul (hasDerivAt_id' z)).deriv]
    ring
  have h := deriv_mul_deriv (D := fun y : ℝ => y) (v := fun z : ℝ => z ^ 2) (x := x)
    differentiableAt_id (by rw [hd]; exact differentiableAt_id.const_mul 2)
  rw [← h, (deriv_id_mul_deriv_sq x).1]

/-! ## Steady linear profiles -/

/-- With `a = 0`, `b = 2`, `uA = 1` and `uB = 5`, any `u` with `u'' = 0` on `[0, 2]` has
`u 1 = 3`. -/
example {u u' : ℝ → ℝ} (hu : ∀ x ∈ Icc (0 : ℝ) 2, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Icc (0 : ℝ) 2, HasDerivAt u' 0 x) (h0 : u 0 = 1) (h2 : u 2 = 5) :
    u 1 = 3 := by
  rw [eq_linear_of_hasDerivAt_zero (by norm_num) hu hu' h0 h2 ⟨by norm_num, by norm_num⟩]
  norm_num

/-- The profile `1 + (5 - 1) x / 2` solves `u'' = 0` with `u 0 = 1` and `u 2 = 5`. -/
example : (∀ x, iteratedDeriv 2 (fun y : ℝ => 1 + (5 - 1) * (y - 0) / (2 - 0)) x = 0) ∧
    (fun y : ℝ => 1 + (5 - 1) * (y - 0) / (2 - 0)) 0 = 1 ∧
    (fun y : ℝ => 1 + (5 - 1) * (y - 0) / (2 - 0)) 2 = 5 :=
  linear_solves_steady (by norm_num)

/-! ## The first heat mode -/

/-- The first mode is `exp(-D π² t) √2 sin(πx)`. -/
example (D t x : ℝ) : heatMode D 1 t x =
    Real.exp (-D * Real.pi ^ 2 * t) * (Real.sqrt 2 * Real.sin (Real.pi * x)) := by
  simp [heatMode, dirichletLaplacianEigenvalue, sineBasisFun]

/-- The first mode solves `∂ₜu = D ∂ₓₓu`. -/
example (D t x : ℝ) :
    deriv (fun τ => heatMode D 1 τ x) t = D * iteratedDeriv 2 (heatMode D 1 t) x :=
  heatMode_heatEquation D 1 t x

/-- Both sides of the heat equation for the first mode equal `-D π² u`. -/
example (D t x : ℝ) :
    deriv (fun τ => heatMode D 1 τ x) t = -D * Real.pi ^ 2 * heatMode D 1 t x ∧
      D * iteratedDeriv 2 (heatMode D 1 t) x = -D * Real.pi ^ 2 * heatMode D 1 t x := by
  have heig : dirichletLaplacianEigenvalue 1 = Real.pi ^ 2 := by
    simp [dirichletLaplacianEigenvalue]
  rw [(hasDerivAt_heatMode_time D 1 t x).deriv, iteratedDeriv_two_heatMode, heig]
  constructor <;> ring

/-- Dirichlet values of the first mode. -/
example (D t : ℝ) : heatMode D 1 t 0 = 0 ∧ heatMode D 1 t 1 = 0 :=
  ⟨heatMode_space_zero D 1 t, heatMode_space_one D 1 t⟩

/-- Initial data of the first mode. -/
example (D x : ℝ) : heatMode D 1 0 x = Real.sqrt 2 * Real.sin (Real.pi * x) := by
  rw [heatMode_time_zero]
  simp [sineBasisFun]

/-! ## Energy decay and uniqueness -/

/-- The energy of the first mode decays exactly like `exp(-2Dπ²t)`. -/
example (D t : ℝ) : heatEnergy 1 (heatMode D 1) t =
    Real.exp (-2 * D * Real.pi ^ 2 * t) * heatEnergy 1 (heatMode D 1) 0 := by
  simp only [heatEnergy, heatMode, mul_pow, intervalIntegral.integral_const_mul, mul_zero,
    Real.exp_zero, one_mul]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  simp only [dirichletLaplacianEigenvalue, PNat.val_ofNat, Nat.cast_one, one_mul]
  push_cast
  ring

/-- The energy identity for the first mode: `E'(t) = -2D ∫₀¹ (∂ₓu)²`. -/
example (D t : ℝ) : HasDerivAt (heatEnergy 1 (heatMode D 1))
    (-2 * D * ∫ x in (0 : ℝ)..1, deriv (heatMode D 1 t) x ^ 2) t :=
  hasDerivAt_heatEnergy zero_le_one ((contDiff_heatMode D 1).of_le le_top)
    (fun x _ => heatMode_heatEquation D 1 t x) (heatMode_space_zero D 1 t)
    (heatMode_space_one D 1 t)

/-- The energy of the first mode has nonpositive derivative for `D ≥ 0`. -/
example (D t : ℝ) (hD : 0 ≤ D) : deriv (heatEnergy 1 (heatMode D 1)) t ≤ 0 :=
  deriv_heatEnergy_nonpos hD zero_le_one ((contDiff_heatMode D 1).of_le le_top)
    (fun x _ => heatMode_heatEquation D 1 t x) (heatMode_space_zero D 1 t)
    (heatMode_space_one D 1 t)

/-- The energy of the first mode is nonincreasing for `t ≥ 0`. -/
example (D : ℝ) (hD : 0 ≤ D) : AntitoneOn (heatEnergy 1 (heatMode D 1)) (Ici 0) :=
  antitoneOn_heatEnergy hD zero_le_one ((contDiff_heatMode D 1).of_le le_top)
    (fun t _ x _ => heatMode_heatEquation D 1 t x) (fun t _ => heatMode_space_zero D 1 t)
    fun t _ => heatMode_space_one D 1 t

/-- Uniqueness: a solution in the class with the initial data of the first mode is the first
mode. -/
example {D : ℝ} (hD : 0 ≤ D) {v : ℝ → ℝ → ℝ} (hv : ContDiff ℝ 2 (Function.uncurry v))
    (hv_heat : ∀ t, 0 ≤ t → ∀ x ∈ Icc (0 : ℝ) 1,
      deriv (fun τ => v τ x) t = D * iteratedDeriv 2 (v t) x)
    (hv_left : ∀ t, 0 ≤ t → v t 0 = 0) (hv_right : ∀ t, 0 ≤ t → v t 1 = 0)
    (hv_init : ∀ x ∈ Icc (0 : ℝ) 1, v 0 x = sineBasisFun 1 x) {t x : ℝ} (ht : 0 ≤ t)
    (hx : x ∈ Icc (0 : ℝ) 1) : v t x = heatMode D 1 t x :=
  heatEquation_unique hD one_pos hv ((contDiff_heatMode D 1).of_le le_top) hv_heat
    (fun t _ x _ => heatMode_heatEquation D 1 t x) hv_left hv_right
    (fun t _ => heatMode_space_zero D 1 t) (fun t _ => heatMode_space_one D 1 t)
    (fun x hx => by rw [hv_init x hx, heatMode_time_zero]) ht hx

/-- Uniqueness: a solution in the class with zero initial data is zero. -/
example {D L : ℝ} (hD : 0 ≤ D) (hL : 0 < L) {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hu_heat : ∀ t, 0 ≤ t → ∀ x ∈ Icc 0 L,
      deriv (fun τ => u τ x) t = D * iteratedDeriv 2 (u t) x)
    (hu_left : ∀ t, 0 ≤ t → u t 0 = 0) (hu_right : ∀ t, 0 ≤ t → u t L = 0)
    (hu_init : ∀ x ∈ Icc 0 L, u 0 x = 0) {t x : ℝ} (ht : 0 ≤ t) (hx : x ∈ Icc 0 L) :
    u t x = 0 :=
  heatEquation_unique (v := fun _ _ => 0) hD hL hu contDiff_const hu_heat
    (fun _ _ _ _ => by simp) hu_left hu_right (fun _ _ => rfl) (fun _ _ => rfl) hu_init ht hx

end MathlibExtTest.Analysis.ODE.ContinuumBalances
