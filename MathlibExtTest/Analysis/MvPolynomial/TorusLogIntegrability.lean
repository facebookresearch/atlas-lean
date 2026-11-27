/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.MvPolynomial.TorusLogIntegrability

@[expose] public section

open MeasureTheory

/-- Consumer with the original binders. -/
private theorem exactSource {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    IntegrableOn
      (fun θ : Fin n → ℝ ↦ Real.log ‖MvPolynomial.eval (fun i ↦ circleMap 0 1 (θ i)) P‖)
      (MvPolynomial.torusBox n) :=
  MvPolynomial.integrableOn_log_norm_eval_circleMap P

/-- The zero polynomial is included: its log-norm is the constant
`Real.log 0 = 0` function. -/
example {n : ℕ} :
    IntegrableOn
      (fun θ : Fin n → ℝ ↦
        Real.log ‖MvPolynomial.eval (fun i ↦ circleMap 0 1 (θ i)) (0 : MvPolynomial (Fin n) ℂ)‖)
      (MvPolynomial.torusBox n) :=
  MvPolynomial.integrableOn_log_norm_eval_circleMap 0

/-- The zero-variable case is included. -/
example (P : MvPolynomial (Fin 0) ℂ) :
    IntegrableOn
      (fun θ : Fin 0 → ℝ ↦ Real.log ‖MvPolynomial.eval (fun i ↦ circleMap 0 1 (θ i)) P‖)
      (MvPolynomial.torusBox 0) :=
  MvPolynomial.integrableOn_log_norm_eval_circleMap P
