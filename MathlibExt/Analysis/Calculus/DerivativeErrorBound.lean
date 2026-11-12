/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# A derivative bound yields an output-error bound

If `|f'| ≤ L` everywhere and the input error satisfies `|x - x₀| ≤ δ`,
then the output error satisfies `|f x - f x₀| ≤ L * δ`.

## i. Overview

The derivative bound makes `f` Lipschitz with constant `L`
(`lipschitzWith_of_nnnorm_deriv_le`), which gives
`|f x - f x₀| ≤ L * |x - x₀|`, and `|x - x₀| ≤ δ` with `L ≥ 0` finishes it.

## ii. Key results

- `MathlibExt.Analysis.output_error_bound_of_deriv_bound`: a derivative
  bound yields a deterministic output-error bound.

## iii. References

- `lipschitzWith_of_nnnorm_deriv_le` (Mathlib).
-/

@[expose] public section

namespace MathlibExt.Analysis

/-- A derivative bound yields a deterministic output-error bound: if
`|f'| ≤ L` everywhere and the input error satisfies `|x - x₀| ≤ δ`, then
the output error satisfies `|f x - f x₀| ≤ L * δ`. -/
theorem output_error_bound_of_deriv_bound {f : ℝ → ℝ} {L : ℝ}
    (hf : Differentiable ℝ f) (hderiv : ∀ x, |deriv f x| ≤ L)
    {x x₀ δ : ℝ} (hδ : |x - x₀| ≤ δ) :
    |f x - f x₀| ≤ L * δ := by
  have hL : 0 ≤ L := le_trans (abs_nonneg (deriv f 0)) (hderiv 0)
  have hLip : LipschitzWith (⟨L, hL⟩ : NNReal) f :=
    lipschitzWith_of_nnnorm_deriv_le hf (fun x => hderiv x)
  have h := hLip.dist_le_mul x x₀
  simp only [Real.dist_eq] at h
  calc |f x - f x₀| ≤ L * |x - x₀| := h
    _ ≤ L * δ := mul_le_mul_of_nonneg_left hδ hL

end MathlibExt.Analysis
