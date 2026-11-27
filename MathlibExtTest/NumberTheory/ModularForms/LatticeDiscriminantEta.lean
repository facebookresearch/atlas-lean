/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModularForms.LatticeDiscriminantEta
import Mathlib.Tactic.Positivity

open MetaMathlibExt
open scoped Real UpperHalfPlane

-- On the square lattice the invariant combination is nonzero.
example :
    (60 * ∑' v : Fin 2 → ℤ, (((v 0 : ℂ) * Complex.I + v 1) ^ 4)⁻¹) ^ 3 -
      27 * (140 * ∑' v : Fin 2 → ℤ, (((v 0 : ℂ) * Complex.I + v 1) ^ 6)⁻¹) ^ 2 ≠ 0 := by
  let τ : ℍ := ⟨Complex.I, by simp⟩
  have h := (lattice_discriminant_eq_eta_product (τ := τ)).1
  change _ = (2 * π : ℂ) ^ 12 * ModularForm.eta Complex.I ^ 24 at h
  rw [h]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (by norm_num) hπ))
    (pow_ne_zero _ (ModularForm.eta_ne_zero τ.2))
