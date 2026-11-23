/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.EntireIteratedDerivPoly
import Mathlib.Analysis.Calculus.Deriv.Add

open MathlibExt.Analysis.Complex.EntireIteratedDerivPolyWanted

-- At the first positive order, a pointwise formula gives the polynomial derivative.
example {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h : ∀ z, deriv f z = z + 1) :
    ∃ q : Polynomial ℂ, f = fun z => q.eval z := by
  apply exists_polynomial_of_iteratedDeriv_eq_polynomial (k := 1) (by decide) hf
  exact ⟨Polynomial.X + 1, funext fun z => by simpa [iteratedDeriv_one] using h z⟩

-- An affine function with arbitrary constant term has zero second derivative.
example (c : ℂ) : ∃ q : Polynomial ℂ, (fun z : ℂ => z + c) = fun z => q.eval z := by
  apply exists_polynomial_of_iteratedDeriv_eq_polynomial (k := 1 + 1) (by decide)
    (differentiable_id.add_const c)
  refine ⟨0, ?_⟩
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_add_const']
  simp
