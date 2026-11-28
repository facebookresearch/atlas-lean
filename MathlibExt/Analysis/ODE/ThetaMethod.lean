/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Module.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum.Inv

/-!
# The θ-method for ordinary differential equations

`IsThetaStep` relates the current state to a candidate next state; it does not assume that
an implicit step has a solution or that its solution is unique. The cases `θ = 0`, `θ = 1`
and `θ = 1/2` give explicit Euler, implicit Euler and the trapezium rule. On a uniform grid,
impose the relation at each consecutive pair of states and prescribe the initial state.

## References

* E. Süli, *Numerical Solution of Ordinary Differential Equations*, Mathematical Institute,
  University of Oxford, 2 March 2022, §2.1, equations (14)–(17) and the remarks following (17).
  <https://people.maths.ox.ac.uk/suli/nsodes.pdf>.
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

end MetaMathlibExt.ODE
