/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Equiv.Basic
import MathlibExt.Analysis.ODE.LinearizedStability

/-!
# Scalar linearized stability (conditional decay)

A scalar equilibrium with negative derivative is conditionally exponentially
stable: for some `δ, C, α > 0`, every solution of `x' = f(x)` defined on all
of `[0, ∞)` with `|x 0 - xstar| < δ` satisfies
`|x t - xstar| ≤ C * exp (-(α * t)) * |x 0 - xstar|` for all `t ≥ 0`
(Atlas roadmap M12.T03). This is the scalar specialization of Lyapunov's
indirect method (Khalil, *Nonlinear Systems*, Theorem 4.7).

## Main results

* `MathlibExt.Analysis.ODE.ScalarStability.scalar_sign_decay_of_hasDerivAt`

The conclusion is CONDITIONAL decay: it does NOT assert solution existence,
continuation, or invariance. The proof applies the Atlas kernel
`MathlibExt.Analysis.ODE.LinearizedStability.globalSolution_decay_of_hasFDerivAt`
with `ι = Fin 1`, lifting the scalar derivative to the `1 × 1` Jacobian
`f' • 1`, which is Hurwitz because `f' < 0`.
-/

@[expose] public section

namespace MathlibExt.Analysis.ODE.ScalarStability

/-- Scalar sign condition gives conditional exponential decay (Atlas roadmap M12.T03).
FROZEN: this is CONDITIONAL decay — the conclusion holds for solutions defined on
all of `[0, ∞)`. It does NOT assert solution existence, continuation, or invariance.
Proved by specializing the Atlas linearized-stability kernel
`globalSolution_decay_of_hasFDerivAt` to the `1 × 1` Jacobian `f' • 1`. -/
theorem scalar_sign_decay_of_hasDerivAt
    {f : ℝ → ℝ} {xstar f' : ℝ}
    (hf : f xstar = 0) (hfA : HasDerivAt f f' xstar) (hneg : f' < 0) :
    ∃ δ C α : ℝ, 0 < δ ∧ 0 < C ∧ 0 < α ∧ ∀ x : ℝ → ℝ,
      (∀ t, 0 ≤ t → HasDerivAt x (f (x t)) t) → |x 0 - xstar| < δ →
        ∀ t, 0 ≤ t → |x t - xstar| ≤ C * Real.exp (-(α * t)) * |x 0 - xstar| := by
  have hcons : ∀ (a : ℝ) (i : Fin 1), ![a] i = a := fun a i => by
    have hi : i = 0 := Unique.eq_default i
    subst hi
    exact Matrix.cons_val_zero a Matrix.vecEmpty
  have hnorm : ∀ (y : Fin 1 → ℝ), ‖y‖ = ‖y 0‖ := fun y => by
    simp [Pi.norm_def, Finset.univ_unique]
  have h00 : (f' • 1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = f' := by
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  set e : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ with he
  have he1 : ∀ (y : Fin 1 → ℝ), e.toContinuousLinearMap y = y 0 := fun y => rfl
  have he2 : ∀ (s : ℝ) (i : Fin 1), e.symm.toContinuousLinearMap s i = s :=
    fun s i => rfl
  have hlin : ∀ (y : Fin 1 → ℝ) (i : Fin 1),
      LinearMap.toContinuousLinearMap (Matrix.toLin' (f' • 1)) y i
      = ∑ j, (f' • 1 : Matrix (Fin 1) (Fin 1) ℝ) i j * y j := fun y i => rfl
  have hFeq : ∀ (y : Fin 1 → ℝ), (fun y : Fin 1 → ℝ => ![f (y 0)]) y
      = (⇑e.symm.toContinuousLinearMap ∘ (f ∘ ⇑e.toContinuousLinearMap)) y :=
    fun y => by
      ext i
      simp only [Function.comp_apply, he1, he2, hcons]
  have hDerivEq : e.symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.toSpanSingleton ℝ f').comp e.toContinuousLinearMap)
      = LinearMap.toContinuousLinearMap (Matrix.toLin' (f' • 1)) := by
    ext y i
    have hi : i = 0 := Unique.eq_default i
    subst hi
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, he1, he2, hlin]
    rw [smul_eq_mul, Fin.sum_univ_one, h00]
    exact mul_comm (y 0) f'
  have hFderiv : HasFDerivAt (fun y : Fin 1 → ℝ => ![f (y 0)])
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (f' • 1))) ![xstar] := by
    have hscalar : HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℝ f') xstar :=
      hfA.hasFDerivAt
    have heF : HasFDerivAt (⇑e.toContinuousLinearMap) e.toContinuousLinearMap ![xstar] :=
      e.toContinuousLinearMap.hasFDerivAt
    have hcomp1 : HasFDerivAt (f ∘ ⇑e.toContinuousLinearMap)
        ((ContinuousLinearMap.toSpanSingleton ℝ f').comp e.toContinuousLinearMap) ![xstar] :=
      HasFDerivAt.comp ![xstar] hscalar heF
    have hcomp2 : HasFDerivAt
        (⇑e.symm.toContinuousLinearMap ∘ (f ∘ ⇑e.toContinuousLinearMap))
        (e.symm.toContinuousLinearMap.comp
          ((ContinuousLinearMap.toSpanSingleton ℝ f').comp e.toContinuousLinearMap)) ![xstar] :=
      HasFDerivAt.comp ![xstar] e.symm.toContinuousLinearMap.hasFDerivAt hcomp1
    have hD : HasFDerivAt (fun y : Fin 1 → ℝ => ![f (y 0)])
        (e.symm.toContinuousLinearMap.comp
          ((ContinuousLinearMap.toSpanSingleton ℝ f').comp e.toContinuousLinearMap)) ![xstar] :=
      hcomp2.congr_of_eventuallyEq (Filter.Eventually.of_forall hFeq)
    rw [hDerivEq] at hD
    exact hD
  have hF0 : (fun y : Fin 1 → ℝ => ![f (y 0)]) ![xstar] = 0 := by
    ext i
    simp [hf]
  have hMap : (f' • 1 : Matrix (Fin 1) (Fin 1) ℝ).map (algebraMap ℝ ℂ)
      = Matrix.diagonal (fun _ : Fin 1 => algebraMap ℝ ℂ f') := by
    ext i j
    have hi : i = 0 := Unique.eq_default i
    have hj : j = 0 := Unique.eq_default j
    subst hi
    subst hj
    rw [Matrix.map_apply, Matrix.diagonal_apply, h00]
    simp
  have hSpec : ∀ μ ∈ spectrum ℂ ((f' • 1 : Matrix (Fin 1) (Fin 1) ℝ).map (algebraMap ℝ ℂ)),
      μ.re < 0 := by
    rw [hMap, spectrum_diagonal]
    intro μ hμ
    rw [Set.mem_range] at hμ
    obtain ⟨i, hi⟩ := hμ
    have hi' : algebraMap ℝ ℂ f' = μ := hi
    rw [← hi']
    have hre : (algebraMap ℝ ℂ f').re = f' := Complex.ofReal_re f'
    rw [hre]
    exact hneg
  -- `Matrix.IsHurwitz` is defined as exactly the `∀ μ ∈ spectrum …` statement
  -- proved in `hSpec`.
  have hA : (f' • 1 : Matrix (Fin 1) (Fin 1) ℝ).IsHurwitz := hSpec
  obtain ⟨δ, C, α, hδ, hC, hα, hdec⟩ :=
    MathlibExt.Analysis.ODE.LinearizedStability.globalSolution_decay_of_hasFDerivAt
      hF0 hFderiv hA
  refine ⟨δ, C, α, hδ, hC, hα, fun x hx hδx t ht => ?_⟩
  have hXfun : (⇑e.symm.toContinuousLinearMap ∘ x) = (fun t => ![x t]) := by
    funext t i
    simp only [Function.comp_apply, he2, hcons]
  have hXderiv : ∀ t : ℝ, e.symm.toContinuousLinearMap (f (x t))
      = (fun y : Fin 1 → ℝ => ![f (y 0)]) ((fun t => ![x t]) t) := fun t => by
    have hx0 : ((fun t => ![x t]) t) 0 = x t := hcons (x t) 0
    ext i
    show f (x t) = ![f (((fun t => ![x t]) t) 0)] i
    rw [hx0, hcons]
  have hX : ∀ t, 0 ≤ t → HasDerivAt (fun t => ![x t])
      ((fun y : Fin 1 → ℝ => ![f (y 0)]) ((fun t => ![x t]) t)) t := by
    intro s hs
    have h := HasFDerivAt.comp_hasDerivAt s
      e.symm.toContinuousLinearMap.hasFDerivAt (hx s hs)
    rw [hXfun, hXderiv s] at h
    exact h
  have hX0 : ‖(fun t => ![x t]) 0 - ![xstar]‖ < δ := by
    have h : ‖(fun t => ![x t]) 0 - ![xstar]‖ = |x 0 - xstar| := by
      simp only [hnorm, Pi.sub_apply, hcons, Real.norm_eq_abs]
    rw [h]
    exact hδx
  have h := hdec (fun t => ![x t]) hX hX0 t ht
  have e1 : ‖(fun t => ![x t]) t - ![xstar]‖ = |x t - xstar| := by
    simp only [hnorm, Pi.sub_apply, hcons, Real.norm_eq_abs]
  have e0 : ‖(fun t => ![x t]) 0 - ![xstar]‖ = |x 0 - xstar| := by
    simp only [hnorm, Pi.sub_apply, hcons, Real.norm_eq_abs]
  rw [e1, e0] at h
  exact h

end MathlibExt.Analysis.ODE.ScalarStability
