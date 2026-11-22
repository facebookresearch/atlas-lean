/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
/-!
# Rayleigh fractionation: derivative and endpoint

For `R(f) = R0 * f^(α-1)` with remaining carrier fraction `f > 0`,
`dR/df = (α-1) * R / f` and `R(1) = R0`.

## i. Overview

Ideal Rayleigh fractionation law with `f ∈ (0, 1]`. Here `^` is the real
power `Real.rpow`, and `α` is the product/reservoir fractionation factor:
`α = R_product / R_reservoir` for the instantaneous product, so `α > 1`
means the instantaneous product is enriched relative to the reservoir.
No delta-as-linear-mixture shortcut is used: the statement is about the
ratio `R` itself.

## ii. Key results

- `EarthScience.rayleigh_hasDerivAt`: `dR/df = (α-1)*R/f`.
- `EarthScience.rayleigh_at_one`: `R(1) = R0`.

## iii. References

- Hoefs, J., *Stable Isotope Geochemistry*, 8th ed., Springer, 2018:
  the Rayleigh fractionation/distillation law `R = R0 * f ^ (α - 1)`,
  with `α` the product/reservoir fractionation factor.
- Rayleigh, Lord, "Theoretical considerations respecting the separation
  of gases by diffusion and similar processes", *Philosophical Magazine*
  42 (1896), the original Rayleigh distillation equation.
- `Real.hasDerivAt_rpow_const` in
  `Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean`.
- `Real.rpow_sub`, `Real.one_rpow` for the power algebra.
-/

@[expose] public section

namespace EarthScience

/-- Rayleigh fractionation: for `R(f) = R0 * f^(α-1)` with `f > 0`,
`dR/df = (α-1) * R / f`. Here `^` is the real power `Real.rpow`. -/
theorem rayleigh_hasDerivAt (R0 alpha f : ℝ) (hf : 0 < f) :
    HasDerivAt (fun f => R0 * f ^ (alpha - 1))
      ((alpha - 1) * (R0 * f ^ (alpha - 1)) / f) f := by
  have hfne : f ≠ 0 := ne_of_gt hf
  have hbase : HasDerivAt (fun x : ℝ => x ^ (alpha - 1))
      ((alpha - 1) * f ^ (alpha - 1 - 1)) f :=
    Real.hasDerivAt_rpow_const (Or.inl hfne)
  have hmul := HasDerivAt.const_mul R0 hbase
  have hrpow : f ^ (alpha - 1 - 1) = f ^ (alpha - 1) / f := by
    have h := Real.rpow_sub hf (alpha - 1) 1
    rwa [Real.rpow_one] at h
  have heq : R0 * ((alpha - 1) * f ^ (alpha - 1 - 1))
      = (alpha - 1) * (R0 * f ^ (alpha - 1)) / f := by
    rw [hrpow]
    field_simp
  rwa [heq] at hmul

/-- Rayleigh fractionation at full remaining fraction: `R(1) = R0`. -/
theorem rayleigh_at_one (R0 alpha : ℝ) :
    R0 * (1 : ℝ) ^ (alpha - 1) = R0 := by
  rw [Real.one_rpow, mul_one]

end EarthScience
