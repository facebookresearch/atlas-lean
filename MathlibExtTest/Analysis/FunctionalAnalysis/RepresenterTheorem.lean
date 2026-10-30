/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.RepresenterTheorem
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

@[expose] public section

/-!
# Tests for the representer theorem and kernel ridge regression
-/

set_option autoImplicit false

open Filter Matrix RKHS
open MathlibExt.Analysis.FunctionalAnalysis.RepresenterTheorem

namespace MathlibExtTest.Analysis.FunctionalAnalysis.RepresenterTheorem

/-- A concrete RKHS: the space of the rank-one kernel `k(a, b) = f a * f b` on two points. -/
abbrev H₁ (f : Fin 2 → ℝ) := RKHS.OfKernel (RKHS.outerKernel ℝ f)

/-- The ridge penalty `Ω t = λ t²` (`λ > 0`) is strictly increasing on `[0, ∞)`. -/
theorem strictMonoOn_ridge {lam : ℝ} (hlam : 0 < lam) :
    StrictMonoOn (fun t : ℝ => lam * t ^ 2) (Set.Ici 0) := fun a ha b _ hab => by
  have := pow_lt_pow_left₀ hab (Set.mem_Ici.mp ha) two_ne_zero
  simpa using mul_lt_mul_of_pos_left this hlam

/-- The ridge penalty is strictly convex on `[0, ∞)`. -/
theorem strictConvexOn_ridge {lam : ℝ} (hlam : 0 < lam) :
    StrictConvexOn ℝ (Set.Ici 0) (fun t : ℝ => lam * t ^ 2) := by
  have h := (strictConvexOn_pow (n := 2) (by norm_num))
  exact ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => by
    have := h.2 hx hy hxy ha hb hab
    simp only [smul_eq_mul] at this ⊢
    nlinarith⟩

/-- The squared loss is convex. -/
theorem convexOn_sqLoss {n : ℕ} (y : Fin n → ℝ) :
    ConvexOn ℝ Set.univ (fun v : Fin n → ℝ => ∑ i, (y i - v i) ^ 2) := by
  refine ⟨convex_univ, fun u _ w _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  obtain rfl : b = 1 - a := by linarith
  nlinarith [sq_nonneg (u i - w i), mul_nonneg ha hb]

/-- Non-vacuity of the representer theorem: with the squared loss and the ridge penalty on a
concrete RKHS, every minimizer is a kernel expansion. -/
example (f : Fin 2 → ℝ) (x : Fin 2 → Fin 2) (y : Fin 2 → ℝ) (g : H₁ f)
    (hg : ∀ h : H₁ f, regularizedRisk (H₁ f) x (fun v => ∑ i, (y i - v i) ^ 2)
      (fun t => 1 * t ^ 2) g ≤
      regularizedRisk (H₁ f) x (fun v => ∑ i, (y i - v i) ^ 2) (fun t => 1 * t ^ 2) h) :
    ∃ c : Fin 2 → ℝ, g = kernelExpansion (H₁ f) x c :=
  exists_eq_kernelExpansion_of_isMinimizer (strictMonoOn_ridge one_pos) hg

/-- Non-vacuity of the existence theorem: the squared loss is continuous and bounded below, the
ridge penalty is continuous, monotone and coercive. -/
example (f : Fin 2 → ℝ) (x : Fin 2 → Fin 2) (y : Fin 2 → ℝ) :
    ∃ c : Fin 2 → ℝ, ∀ h : H₁ f,
      regularizedRisk (H₁ f) x (fun v => ∑ i, (y i - v i) ^ 2) (fun t => 1 * t ^ 2)
          (kernelExpansion (H₁ f) x c) ≤
        regularizedRisk (H₁ f) x (fun v => ∑ i, (y i - v i) ^ 2) (fun t => 1 * t ^ 2) h :=
  exists_kernelExpansion_isMinimizer x (by fun_prop)
    ⟨0, by rintro _ ⟨v, rfl⟩; exact Finset.sum_nonneg fun i _ => sq_nonneg _⟩ (by fun_prop)
    (strictMonoOn_ridge one_pos).monotoneOn
    (by simp)

/-- Non-vacuity of the uniqueness theorem. -/
example (f : Fin 2 → ℝ) (x : Fin 2 → Fin 2) (y : Fin 2 → ℝ) (g₁ g₂ : H₁ f)
    (h₁ : ∀ h : H₁ f, regularizedRisk (H₁ f) x (fun v => ∑ i, (y i - v i) ^ 2)
      (fun t => 1 * t ^ 2) g₁ ≤
      regularizedRisk (H₁ f) x (fun v => ∑ i, (y i - v i) ^ 2) (fun t => 1 * t ^ 2) h)
    (h₂ : ∀ h : H₁ f, regularizedRisk (H₁ f) x (fun v => ∑ i, (y i - v i) ^ 2)
      (fun t => 1 * t ^ 2) g₂ ≤
      regularizedRisk (H₁ f) x (fun v => ∑ i, (y i - v i) ^ 2) (fun t => 1 * t ^ 2) h) :
    g₁ = g₂ :=
  isMinimizer_unique (convexOn_sqLoss y) (strictConvexOn_ridge one_pos)
    (strictMonoOn_ridge one_pos).monotoneOn h₁ h₂

/-- The Gram matrix of the rank-one kernel is `f(xᵢ) f(xⱼ)`. -/
theorem kernelGram_H₁ (f : Fin 2 → ℝ) (x : Fin 2 → Fin 2) (i j : Fin 2) :
    kernelGram (H₁ f) x i j = f (x i) * f (x j) := by
  simp [kernelGram, RKHS.OfKernel.kernel_ofKernel, RKHS.outerKernel_apply]
  ring

/-- Kernel ridge regression on the concrete RKHS: the fit minimizes the objective, uniquely. -/
example (f : Fin 2 → ℝ) (x : Fin 2 → Fin 2) (y : Fin 2 → ℝ) (g : H₁ f) :
    kernelRidgeRisk (H₁ f) x y 1 (kernelRidgeFit (H₁ f) x y 1) ≤
      kernelRidgeRisk (H₁ f) x y 1 g :=
  kernelRidgeRisk_kernelRidgeFit_le x y one_pos g

/-- Boundary case (junk value outside the domain `λ > 0`): for the zero kernel and `λ = 0`,
`K + λ I = 0` is singular, Lean's matrix inverse returns `0`, and the "fit" is `0`. The
theorems above require `λ > 0`. -/
example (x : Fin 2 → Fin 2) (y : Fin 2 → ℝ) : kernelRidgeFit (H₁ 0) x y 0 = 0 := by
  have hK : kernelGram (H₁ 0) x = 0 := by
    ext i j
    simp [kernelGram_H₁]
  simp [kernelRidgeFit, hK]

end MathlibExtTest.Analysis.FunctionalAnalysis.RepresenterTheorem
