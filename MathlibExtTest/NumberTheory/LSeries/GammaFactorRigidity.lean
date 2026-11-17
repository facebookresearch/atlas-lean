/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LSeries.GammaFactorRigidity

/-!
# Tests for Gamma-factor rigidity
-/

open Complex

@[expose] public section

/-- `exp` is `exp` of the polynomial `X`. -/
example : ∃ g : Polynomial ℂ, ∀ z, Complex.exp z = Complex.exp (g.eval z) :=
  Complex.exists_polynomial_eq_exp_of_hasGrowthOrderLE differentiable_exp
    (Complex.hasGrowthOrderLE_one_of_isBigO_exp_mul_norm (A := 1)
      (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun z => by
        rw [norm_exp, one_mul, one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_exp.2 (re_le_norm z))))
    Complex.exp_ne_zero

/-- The hypotheses of the rigidity theorem are satisfiable: `f = 1` with no Gamma factors. -/
example : ∃ C : ℂ, ∀ s : ℂ, 1 / 2 ≤ s.re → (fun _ : ℂ => (1 : ℂ)) s = C :=
  LSeries.exists_eq_const_of_gamma_functional_equation (fun _ => 1) analyticOnNhd_const
    (fun _ _ => one_ne_zero) ⟨0, 0, fun s _ => ⟨LSeriesSummable_zero, by simp⟩⟩ 1 one_pos 0 0
    (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
    (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) 1 (by simp)
    (Filter.Eventually.of_forall fun s => by simp)
    ⟨fun _ => 1, 0, differentiable_const _, Complex.hasGrowthOrderLE_const _ _,
      Filter.Eventually.of_forall fun s => by simp⟩
