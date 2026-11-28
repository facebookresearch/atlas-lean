/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Module.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Inv

/-!
# The θ-method for ordinary differential equations

`IsThetaStep` relates the current state to a candidate next state; it does not assume that
an implicit step is solvable. On a uniform grid, impose the relation at each consecutive
pair of states and prescribe the initial state. For the scalar equation $y' = \lambda y$,
the step reduces to a single linear equation, including when its leading coefficient vanishes.

## References

* E. Süli, *Numerical Solution of Ordinary Differential Equations*, Mathematical Institute,
  University of Oxford, 2 March 2022, §2.1, equations (14)–(17) and the remarks following (17).
  <https://people.maths.ox.ac.uk/suli/nsodes.pdf>. The scalar linear formulas are derived from (16).
-/

@[expose] public section

namespace MetaMathlibExt.ODE

section Module

variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

/-- One θ-method step for the vector field `f`, from state `y` at time `t` to state `yNext`
at time `t + h`. The usual method takes `θ ∈ [0, 1]`; the algebraic relation is defined for
any `θ`. Except at `θ = 0`, the right-hand side generally depends on `yNext`. -/
def IsThetaStep (f : ℝ → E → E) (θ t h : ℝ) (y yNext : E) : Prop :=
  yNext = y + h • ((1 - θ) • f t y + θ • f (t + h) yNext)

/-- At `θ = 0` the θ-method is the explicit Euler update. -/
lemma isThetaStep_zero_iff {f : ℝ → E → E} {t h : ℝ} {y yNext : E} :
    IsThetaStep f 0 t h y yNext ↔ yNext = y + h • f t y := by
  simp [IsThetaStep]

/-- At `θ = 1` the θ-method is the implicit Euler update, using the field at the next state
and time. -/
lemma isThetaStep_one_iff {f : ℝ → E → E} {t h : ℝ} {y yNext : E} :
    IsThetaStep f 1 t h y yNext ↔ yNext = y + h • f (t + h) yNext := by
  simp [IsThetaStep]

/-- At `θ = 1/2` the θ-method is the trapezium rule, with equal weights at the two endpoints. -/
lemma isThetaStep_half_iff {f : ℝ → E → E} {t h : ℝ} {y yNext : E} :
    IsThetaStep f (1 / 2) t h y yNext ↔
      yNext = y + (h / 2) • (f t y + f (t + h) yNext) := by
  rw [IsThetaStep, show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← smul_add, smul_smul, mul_one_div]

/-- On the uniform grid with `N` subintervals, impose `u 0 = y₀` and one θ-step for every
`n : Fin N`. This gives the θ-method recurrence evaluated at the two mesh times
`tₙ = t₀ + n * h` and `tₙ₊₁ = t₀ + (n + 1) * h`, where `h = (tEnd - t₀) / N`.
For the usual interval mesh take `t₀ < tEnd`, `0 < N` and `θ ∈ [0, 1]`. The equivalence
itself is algebraic; when `N = 0` the step condition is empty. -/
lemma thetaMethod_uniformGrid_iff (f : ℝ → E → E) (θ t₀ tEnd : ℝ) (N : ℕ)
    (y₀ : E) (u : Fin (N + 1) → E) :
    let h := (tEnd - t₀) / (N : ℝ)
    let t : Fin (N + 1) → ℝ := fun n ↦ t₀ + (n.val : ℝ) * h
    (u 0 = y₀ ∧ ∀ n : Fin N, IsThetaStep f θ (t n.castSucc) h (u n.castSucc) (u n.succ)) ↔
      u 0 = y₀ ∧ ∀ n : Fin N, u n.succ = u n.castSucc + h •
        ((1 - θ) • f (t n.castSucc) (u n.castSucc) + θ • f (t n.succ) (u n.succ)) := by
  intro h t
  have ht (n : Fin N) : t n.castSucc + h = t n.succ := by
    simp only [t, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one, add_mul,
      one_mul, add_assoc]
  simp only [IsThetaStep, ht]

end Module

/-- On `y' = λ y` the θ-method is equivalent to a linear equation in `yNext`. -/
lemma isThetaStep_linear_iff {θ t h lam y yNext : ℝ} :
    IsThetaStep (fun _ z ↦ lam * z) θ t h y yNext ↔
      (1 - h * θ * lam) * yNext = (1 + h * (1 - θ) * lam) * y := by
  change yNext = y + h * ((1 - θ) * (lam * y) + θ * (lam * yNext)) ↔ _
  constructor <;> intro hs <;> linear_combination hs

/-- When the denominator is nonzero, the scalar linear step holds exactly at its closed-form
next value. -/
lemma isThetaStep_linear_iff_eq {θ t h lam y yNext : ℝ} (hden : 1 - h * θ * lam ≠ 0) :
    IsThetaStep (fun _ z ↦ lam * z) θ t h y yNext ↔
      yNext = ((1 + h * (1 - θ) * lam) * y) / (1 - h * θ * lam) := by
  rw [isThetaStep_linear_iff, eq_div_iff hden, mul_comm yNext]

/-- If the scalar denominator vanishes, every next value solves the step when the right-hand
side is zero, and no next value solves it otherwise. -/
lemma isThetaStep_linear_singular_iff {θ t h lam y yNext : ℝ} (hden : 1 - h * θ * lam = 0) :
    IsThetaStep (fun _ z ↦ lam * z) θ t h y yNext ↔ (1 + h * (1 - θ) * lam) * y = 0 := by
  rw [isThetaStep_linear_iff, hden, zero_mul, eq_comm]

/-- The scalar linear θ-step has exactly one solution if and only if its denominator is
nonzero. -/
lemma existsUnique_isThetaStep_linear_iff {θ t h lam y : ℝ} :
    (∃! yNext, IsThetaStep (fun _ z ↦ lam * z) θ t h y yNext) ↔ 1 - h * θ * lam ≠ 0 := by
  constructor
  · rintro ⟨z, hz, huniq⟩ hden
    have hrhs := (isThetaStep_linear_singular_iff hden).1 hz
    have hzero : (0 : ℝ) = z := huniq 0 ((isThetaStep_linear_singular_iff hden).2 hrhs)
    have hone : (1 : ℝ) = z := huniq 1 ((isThetaStep_linear_singular_iff hden).2 hrhs)
    exact zero_ne_one (hzero.trans hone.symm)
  · intro hden
    refine ⟨_, (isThetaStep_linear_iff_eq hden).2 rfl, ?_⟩
    exact fun _ hz ↦ (isThetaStep_linear_iff_eq hden).1 hz

end MetaMathlibExt.ODE
