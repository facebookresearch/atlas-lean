/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!

# The critical point of the square-lattice Ising model

The Onsager integrand `cosh² 2β - sinh 2β (cos k₁ + cos k₂)` and the critical inverse temperature
`β_c = ½ log (1 + √2)`.

## i. Overview

The integrand of Onsager's free energy is `g(β, k₁, k₂) = cosh² 2β - sinh 2β (cos k₁ + cos k₂)`. For
`β ≥ 0` it is minimized at `k₁ = k₂ = 0`, where it equals `(sinh 2β - 1)²`. So the integrand
vanishes somewhere exactly when `sinh 2β = 1`, which for `β > 0` happens only at the Kramers-Wannier
critical point `β_c = ½ log (1 + √2)`.

## ii. Key results

- `ons_gInt` : the Onsager integrand
- `ons_betaC` : the critical inverse temperature
- `ons_gInt_min` : for `β ≥ 0` the integrand is minimal at `k = 0`
- `ons_betaC_sinh` : `sinh 2β_c = 1`
- `ons_betaC_unique` : `β_c` is the only positive solution of `sinh 2β = 1`

## iii. Table of contents

- A. The Onsager integrand
- B. The critical inverse temperature

## iv. References

- H. A. Kramers and G. H. Wannier, *Statistics of the two-dimensional ferromagnet. Part I*, Phys.
  Rev. 60 (1941) 252-262
- L. Onsager, *Crystal statistics. I. A two-dimensional model with an order-disorder transition*,
  Phys. Rev. 65 (1944) 117-149

-/

@[expose] public section

namespace StatMech.Onsager

open Real

/-! ## A. The Onsager integrand -/

/-- The Onsager integrand `cosh² 2β - sinh 2β (cos k₁ + cos k₂)` at inverse temperature `β` and
momentum `(k₁, k₂)`. -/
noncomputable def ons_gInt (β k₁ k₂ : ℝ) : ℝ :=
  Real.cosh (2*β)^2 - Real.sinh (2*β) * (Real.cos k₁ + Real.cos k₂)

/-- The critical inverse temperature `β_c = ½ log (1 + √2)` of the square-lattice Ising model with
unit couplings. -/
noncomputable def ons_betaC : ℝ := (1/2) * Real.log (1 + Real.sqrt 2)

lemma ons_sq_identity (β : ℝ) :
    Real.cosh (2*β)^2 - 2 * Real.sinh (2*β) = (Real.sinh (2*β) - 1)^2 := by
  have h := Real.cosh_sq_sub_sinh_sq (2*β)
  nlinarith [h]

lemma ons_gInt_zero (β : ℝ) :
    ons_gInt β 0 0 = (Real.sinh (2*β) - 1)^2 := by
  unfold ons_gInt
  rw [Real.cos_zero]
  have h := ons_sq_identity β
  nlinarith [h]

lemma ons_gInt_nonneg_at_zero (β : ℝ) : 0 ≤ ons_gInt β 0 0 := by
  rw [ons_gInt_zero]
  exact sq_nonneg _

lemma ons_gInt_min (β k₁ k₂ : ℝ) (hβ : 0 ≤ β) :
    ons_gInt β 0 0 ≤ ons_gInt β k₁ k₂ := by
  unfold ons_gInt
  have hsinh : 0 ≤ Real.sinh (2*β) := by
    rw [Real.sinh_nonneg_iff]; linarith
  have hc1 : Real.cos k₁ ≤ 1 := Real.cos_le_one k₁
  have hc2 : Real.cos k₂ ≤ 1 := Real.cos_le_one k₂
  rw [Real.cos_zero]
  have : Real.sinh (2*β) * (Real.cos k₁ + Real.cos k₂)
      ≤ Real.sinh (2*β) * (1 + 1) := by
    apply mul_le_mul_of_nonneg_left _ hsinh
    linarith
  linarith

lemma ons_gInt_zero_eq_zero_iff (β : ℝ) :
    ons_gInt β 0 0 = 0 ↔ Real.sinh (2*β) = 1 := by
  rw [ons_gInt_zero, sq_eq_zero_iff, sub_eq_zero]

/-! ## B. The critical inverse temperature -/

/-- **Kramers-Wannier critical point.** `sinh 2β_c = 1` (H. A. Kramers and G. H. Wannier,
*Statistics of the two-dimensional ferromagnet. Part I*, 1941). -/
theorem ons_betaC_sinh : Real.sinh (2 * ons_betaC) = 1 := by
  have h2mul : 2 * ons_betaC = Real.log (1 + Real.sqrt 2) := by
    unfold ons_betaC; ring
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hspos : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hpos : (0:ℝ) < 1 + Real.sqrt 2 := by linarith
  have hprod : (1 + Real.sqrt 2) * (Real.sqrt 2 - 1) = 1 := by nlinarith [hs]
  have hinv : (1 + Real.sqrt 2)⁻¹ = Real.sqrt 2 - 1 :=
    inv_eq_of_mul_eq_one_right hprod
  rw [h2mul, Real.sinh_log hpos, hinv]
  ring

lemma ons_betaC_pos : 0 < ons_betaC := by
  unfold ons_betaC
  have hspos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hlog : 0 < Real.log (1 + Real.sqrt 2) := Real.log_pos (by linarith)
  linarith

/-- `β_c` is the unique positive inverse temperature with `sinh 2β = 1`, the self-dual point of the
Kramers-Wannier duality. -/
lemma ons_betaC_unique (β : ℝ) (_hβ : 0 < β) :
    Real.sinh (2*β) = 1 ↔ β = ons_betaC := by
  constructor
  · intro h
    have hc := ons_betaC_sinh
    have heq : Real.sinh (2*β) = Real.sinh (2 * ons_betaC) := by rw [h, hc]
    have := Real.sinh_injective heq
    linarith
  · intro h
    rw [h]
    exact ons_betaC_sinh

end StatMech.Onsager
