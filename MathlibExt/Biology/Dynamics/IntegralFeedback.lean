/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Integral feedback and perfect adaptation

Yi, Huang, Simon and Doyle (2000) explained the robust perfect adaptation of bacterial
chemotaxis by integral feedback control: if some state variable `z` of the system satisfies
`ż = y`, where `y` is the output measured from its adapted value, then `y = 0` at every
steady state, whatever the input and the parameters (their block diagram: `ẋ = y`, so `y = 0`
at steady state for all `u`), and they argue that integral control in some form is necessary
for a robust implementation of perfect adaptation. This file states both directions for a
linear time-invariant system

  `ẋ = A x + u b`,   `y = c ⬝ x + d u`

with a nonsingular state matrix `A` and constant input `u`.

* `HasPerfectAdaptation`: at every equilibrium, for every constant input, the output is `0`.
* `HasIntegralFeedback`: some linear functional `z = k ⬝ x` of the state is the time integral of
  the output along every trajectory, `k ⬝ (A x + u b) = c ⬝ x + d u` for all `x`, `u`.

## Main results

* `hasPerfectAdaptation_of_hasIntegralFeedback`: integral feedback gives perfect adaptation
  (no invertibility needed).
* `hasIntegralFeedback_iff_hasPerfectAdaptation`: for nonsingular `A` the converse holds:
  perfect adaptation forces an integral-feedback functional, `k = c A⁻¹`.
* `hasPerfectAdaptation_iff_dcGain_eq_zero`: for nonsingular `A`, perfect adaptation holds iff
  the steady-state gain `d - c A⁻¹ b` vanishes (the transfer function has a zero at `s = 0`).
* `hasDerivAt_integral`: along a trajectory, `d/dt (k ⬝ x(t)) = y(t)`.
* `output_eq_zero_of_integral_feedback`: the nonlinear version: if a differentiable `z` has
  `Dz(x) (F p x) = y p x` for every parameter `p`, then `y p x = 0` at every equilibrium of
  every `F p` (robustness: the conclusion holds for all parameters at once).

Equilibria are the steady states; convergence of trajectories to them (stability of `A`) is not
treated, and the robustness of a structural property over an open set of parameters is
expressed only through the parametric nonlinear statement. The matrix formulation is a
formalization of the linear argument, not a transcription of a numbered result of the paper;
the Barkai–Leibler chemotaxis model itself is not formalized.

## References

* T.-M. Yi, Y. Huang, M. I. Simon and J. Doyle, *Robust perfect adaptation in bacterial
  chemotaxis through integral feedback control*, Proc. Natl. Acad. Sci. USA 97 (2000)
  4649–4653.
* N. Barkai and S. Leibler, *Robustness in simple biochemical networks*, Nature 387 (1997)
  913–917.
-/

@[expose] public section

open Matrix

namespace MathlibExt.Biology.Dynamics.IntegralFeedback

/-- A single-input single-output linear time-invariant system `ẋ = A x + u b`,
`y = c ⬝ x + d u` with state space `n → ℝ`. -/
structure LinearSystem (n : Type*) where
  /-- The state matrix. -/
  A : Matrix n n ℝ
  /-- The input vector. -/
  b : n → ℝ
  /-- The output functional. -/
  c : n → ℝ
  /-- The direct feedthrough from input to output. -/
  d : ℝ

variable {n : Type*} [Fintype n] (S : LinearSystem n)

namespace LinearSystem

/-- The vector field `A x + u b` at state `x` and input `u`. -/
def field (x : n → ℝ) (u : ℝ) : n → ℝ :=
  S.A *ᵥ x + u • S.b

/-- The output `c ⬝ x + d u`, measured from its adapted value. -/
def output (x : n → ℝ) (u : ℝ) : ℝ :=
  S.c ⬝ᵥ x + S.d * u

/-- **Perfect adaptation**: for every constant input `u`, the output vanishes at every
equilibrium. -/
def HasPerfectAdaptation : Prop :=
  ∀ (u : ℝ) (x : n → ℝ), S.field x u = 0 → S.output x u = 0

/-- **Integral feedback**: a linear functional `z = k ⬝ x` of the state integrates the output,
`ż = k ⬝ (A x + u b) = y`, for every state and input. -/
def HasIntegralFeedback : Prop :=
  ∃ k : n → ℝ, ∀ (x : n → ℝ) (u : ℝ), k ⬝ᵥ S.field x u = S.output x u

/-- The steady-state (DC) gain `d - c ⬝ A⁻¹ b`; for nonsingular `A` the output at the
equilibrium for input `u` is `dcGain * u`. -/
noncomputable def dcGain [DecidableEq n] : ℝ :=
  S.d - S.c ⬝ᵥ (S.A⁻¹ *ᵥ S.b)

/-- Integral feedback implies perfect adaptation. -/
theorem hasPerfectAdaptation_of_hasIntegralFeedback (h : S.HasIntegralFeedback) :
    S.HasPerfectAdaptation := by
  obtain ⟨k, hk⟩ := h
  intro u x hx
  rw [← hk, hx, dotProduct_zero]

/-- For nonsingular `A`, the unique equilibrium for input `u` is `x = -u • A⁻¹ b`. -/
theorem field_eq_zero_iff [DecidableEq n] (hA : IsUnit S.A.det) (x : n → ℝ) (u : ℝ) :
    S.field x u = 0 ↔ x = -(u • (S.A⁻¹ *ᵥ S.b)) := by
  unfold field
  constructor
  · intro h
    have h' : S.A *ᵥ x = -(u • S.b) := eq_neg_of_add_eq_zero_left h
    calc x = S.A⁻¹ *ᵥ (S.A *ᵥ x) := by rw [mulVec_mulVec, nonsing_inv_mul _ hA, one_mulVec]
      _ = -(u • (S.A⁻¹ *ᵥ S.b)) := by rw [h', mulVec_neg, mulVec_smul]
  · rintro rfl
    rw [mulVec_neg, mulVec_smul, mulVec_mulVec, mul_nonsing_inv _ hA, one_mulVec,
      neg_add_cancel]

/-- For nonsingular `A`, the output at the equilibrium for input `u` is `dcGain * u`. -/
theorem output_equilibrium [DecidableEq n] (u : ℝ) :
    S.output (-(u • (S.A⁻¹ *ᵥ S.b))) u = S.dcGain * u := by
  simp only [output, dcGain, dotProduct_neg, dotProduct_smul, smul_eq_mul]
  ring

/-- For nonsingular `A`, perfect adaptation holds iff the steady-state gain vanishes. -/
theorem hasPerfectAdaptation_iff_dcGain_eq_zero [DecidableEq n] (hA : IsUnit S.A.det) :
    S.HasPerfectAdaptation ↔ S.dcGain = 0 := by
  constructor
  · intro h
    have := h 1 _ ((S.field_eq_zero_iff hA _ 1).2 rfl)
    rwa [output_equilibrium S, mul_one] at this
  · intro h u x hx
    rw [(S.field_eq_zero_iff hA x u).1 hx, output_equilibrium S, h, zero_mul]

/-- **Integral feedback is necessary** (linear systems with nonsingular `A`): perfect
adaptation holds iff some linear functional of the state integrates the output; one such
functional is `k = c A⁻¹`. -/
theorem hasIntegralFeedback_iff_hasPerfectAdaptation [DecidableEq n] (hA : IsUnit S.A.det) :
    S.HasIntegralFeedback ↔ S.HasPerfectAdaptation := by
  refine ⟨S.hasPerfectAdaptation_of_hasIntegralFeedback, fun h ↦ ?_⟩
  have hg := (S.hasPerfectAdaptation_iff_dcGain_eq_zero hA).1 h
  refine ⟨S.c ᵥ* S.A⁻¹, fun x u ↦ ?_⟩
  have hd : S.d = S.c ⬝ᵥ (S.A⁻¹ *ᵥ S.b) := by rw [dcGain] at hg; linarith
  simp only [field, output, dotProduct_add, dotProduct_smul, smul_eq_mul, ← dotProduct_mulVec,
    mulVec_mulVec, nonsing_inv_mul _ hA, one_mulVec, hd]
  ring

/-- Along a trajectory `ẋ(t) = A x(t) + u(t) b`, the functional `k ⬝ x(t)` of an
integral-feedback system has derivative `y(t) = c ⬝ x(t) + d u(t)`: it is the time integral of
the output. -/
theorem hasDerivAt_integral {k : n → ℝ} (hk : ∀ x u, k ⬝ᵥ S.field x u = S.output x u)
    {x : ℝ → n → ℝ} {u : ℝ → ℝ} {t : ℝ} (hx : HasDerivAt x (S.field (x t) (u t)) t) :
    HasDerivAt (fun s ↦ k ⬝ᵥ x s) (S.output (x t) (u t)) t := by
  rw [← hk]
  have hi : ∀ i, HasDerivAt (fun s ↦ x s i) (S.field (x t) (u t) i) t :=
    fun i ↦ (hasDerivAt_pi.1 hx) i
  simpa [dotProduct] using HasDerivAt.fun_sum (fun i _ ↦ (hi i).const_mul (k i))

end LinearSystem

/-- **Integral feedback gives robust perfect adaptation** (nonlinear form). Let `F p` be the
vector field and `y p` the output of a system with parameters `p`, and let `z` have derivative
`z' x` with `z' x (F p x) = y p x` for all `p`, `x` (so `ż = y` along every trajectory, for
every parameter). Then the output vanishes at every equilibrium of every `F p`. -/
theorem output_eq_zero_of_integral_feedback {P E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : P → E → E) (y : P → E → ℝ) (z' : E → E →L[ℝ] ℝ)
    (h : ∀ p x, z' x (F p x) = y p x) {p : P} {x : E} (hx : F p x = 0) : y p x = 0 := by
  rw [← h, hx, map_zero]

end MathlibExt.Biology.Dynamics.IntegralFeedback
