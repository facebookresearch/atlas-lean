/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RootsOfUnityProduct
import Mathlib.Tactic.Ring

open Polynomial MetaMathlibExt

-- With no nontrivial rotations, the witnesses specialize to 1 and f.
example (f : ℤ[X]) (r : ℕ) (hf : f.degree = r) :
    ∃ G T : ℤ[X], G = 1 ∧ T = f ∧ T.natDegree = r := by
  obtain ⟨G, T, hG, hd, hT⟩ := rootsOfUnity_product_mul_eq_comp_pow f r 1 (by decide) hf
  have h₁ : G = 1 := by
    apply map_injective (Int.castRingHom ℂ) Int.cast_injective
    simpa using hG
  exact ⟨G, T, h₁, by simpa [h₁] using hT.symm, hd⟩

-- The nontrivial square root of unity sends the nonmonic polynomial 2X to -2X.
example : ∃ T : ℤ[X], T.natDegree = 1 ∧ T.comp (X ^ 2) = -(C 4 * X ^ 2) := by
  obtain ⟨G, T, hG, hd, hT⟩ := rootsOfUnity_product_mul_eq_comp_pow (C 2 * X) 1 2
    (by decide) (degree_C_mul_X (by decide))
  have hζ : Complex.exp (2 * Real.pi * Complex.I / 2) = -1 := by
    rw [show (2 : ℂ) * Real.pi * Complex.I / 2 = Real.pi * Complex.I by ring,
      Complex.exp_pi_mul_I]
  have hrot : G = -(C 2 * X) := by
    apply map_injective (Int.castRingHom ℂ) Int.cast_injective
    simpa [show Finset.Ico 1 2 = {1} by decide, hζ, mul_comp] using hG
  refine ⟨T, hd, ?_⟩
  rw [← hT, hrot, show (4 : ℤ) = 2 * 2 by decide, map_mul]
  ring
