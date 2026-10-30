/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.ComplexHessian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- Constants have vanishing real and complex Hessians.
example (z a b : EuclideanSpace ℂ (Fin 2)) : realHessian (fun _ => (3 : ℝ)) z a b = 0 := by
  simp

example (z : EuclideanSpace ℂ (Fin 2)) : complexHessian (fun _ => (3 : ℝ)) z = 0 := by
  simp

-- The entries unfold to the real-coordinate formula.
example (u : EuclideanSpace ℂ (Fin 1) → ℝ) (z : EuclideanSpace ℂ (Fin 1)) :
    complexHessian u z 0 0 =
      ((realHessian u z (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) +
          realHessian u z (Complex.I • EuclideanSpace.single 0 1)
            (Complex.I • EuclideanSpace.single 0 1) : ℝ) +
        ((realHessian u z (EuclideanSpace.single 0 1) (Complex.I • EuclideanSpace.single 0 1) -
            realHessian u z (Complex.I • EuclideanSpace.single 0 1)
              (EuclideanSpace.single 0 1) : ℝ) : ℂ) * Complex.I) / 4 :=
  complexHessian_apply u z 0 0

namespace ComplexHessianValueTests

noncomputable section

/-- Real quadratic calculus gives `D²‖z‖²(a,b) = 2 ⟪a,b⟫`, independently of the
complex-Hessian conversion and its normalization. -/
private theorem normSq_realHessian
    (z a b : EuclideanSpace ℂ (Fin 1)) :
    realHessian (fun x : EuclideanSpace ℂ (Fin 1) => ‖x‖ ^ 2) z a b =
      2 * inner ℝ a b := by
  have hL : fderiv ℝ (fun x : EuclideanSpace ℂ (Fin 1) => ‖x‖ ^ 2) =
      ⇑((2 : ℝ) • (innerSL ℝ (E := EuclideanSpace ℂ (Fin 1)))) := by
    rw [fderiv_norm_sq]
    ext
    simp
  unfold realHessian
  rw [hL, ContinuousLinearMap.fderiv]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rfl

/-- `∂z ∂z̄ |z|² = 1`; a wrong normalization or missing `y-y` term changes this value. -/
example (z : EuclideanSpace ℂ (Fin 1)) :
    complexHessian (fun x : EuclideanSpace ℂ (Fin 1) => ‖x‖ ^ 2) z 0 0 = 1 := by
  simp only [complexHessian, normSq_realHessian, PiLp.inner_apply, Fin.sum_univ_one]
  norm_num [Complex.inner, PiLp.single_apply]

/-- The real coordinate `x₀`. -/
private def x0 : EuclideanSpace ℂ (Fin 2) →L[ℝ] ℝ :=
  Complex.reCLM.comp
    ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ).restrictScalars ℝ)

/-- The real linear coordinate combination `x₁ + y₁`. -/
private def x1y1 : EuclideanSpace ℂ (Fin 2) →L[ℝ] ℝ :=
  Complex.reCLM.comp
      ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ).restrictScalars ℝ) +
    Complex.imCLM.comp
      ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ).restrictScalars ℝ)

/-- The nonconstant real polynomial `x₀ x₁ + x₀ y₁`. -/
private def mixedQuadratic (z : EuclideanSpace ℂ (Fin 2)) : ℝ := x0 z * x1y1 z

private theorem mixedQuadratic_apply (z : EuclideanSpace ℂ (Fin 2)) :
    mixedQuadratic z = (z 0).re * ((z 1).re + (z 1).im) := rfl

/-- Its first derivative is a linear function of the base point, by the product rule. -/
private def mixedDerivative :
    EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 2) →L[ℝ] ℝ :=
  x0.smulRight x1y1 + x1y1.smulRight x0

private theorem mixedQuadratic_fderiv (z : EuclideanSpace ℂ (Fin 2)) :
    fderiv ℝ mixedQuadratic z = mixedDerivative z := by
  have h0 : HasFDerivAt ⇑x0 x0 z := x0.hasFDerivAt
  have h1 : HasFDerivAt ⇑x1y1 x1y1 z := x1y1.hasFDerivAt
  have h : HasFDerivAt mixedQuadratic (mixedDerivative z) z := by
    convert! h0.fun_mul h1 using 1
  exact h.fderiv

/-- The second real derivative is the symmetric bilinear product-rule expression. -/
private theorem mixedQuadratic_realHessian (z a b : EuclideanSpace ℂ (Fin 2)) :
    realHessian mixedQuadratic z a b = x0 a * x1y1 b + x1y1 a * x0 b := by
  have hD : fderiv ℝ mixedQuadratic = ⇑mixedDerivative :=
    funext mixedQuadratic_fderiv
  unfold realHessian
  rw [hD, ContinuousLinearMap.fderiv]
  simp [mixedDerivative, ContinuousLinearMap.smulRight_apply, smul_eq_mul]

/-- The real mixed partial is `1` and the `x₀-y₁` partial is `1`, so this entry is
`(1+i)/4`. Wrong real indexing or an imaginary-sign change alters the literal value. -/
example (z : EuclideanSpace ℂ (Fin 2)) :
    complexHessian mixedQuadratic z 0 1 = (1 + Complex.I) / 4 := by
  norm_num [complexHessian, mixedQuadratic_realHessian, x0, x1y1,
    EuclideanSpace.coe_proj, PiLp.single_apply]

/-- Reversing the indices conjugates the entry: `(1-i)/4`. A sum instead of the
mixed-partial difference passes the other order but fails this one. -/
example (z : EuclideanSpace ℂ (Fin 2)) :
    complexHessian mixedQuadratic z 1 0 = (1 - Complex.I) / 4 := by
  norm_num [complexHessian, mixedQuadratic_realHessian, x0, x1y1,
    EuclideanSpace.coe_proj, PiLp.single_apply, sub_eq_add_neg]

end

end ComplexHessianValueTests
