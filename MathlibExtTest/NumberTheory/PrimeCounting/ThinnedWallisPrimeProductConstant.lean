/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.ThinnedWallisPrimeProductConstant
import Mathlib.Tactic.NormNum

/-! # Tests for the constant in the thinned Wallis-type prime product asymptotic -/

open Filter Topology MetaMathlibExt

private noncomputable def firstProduct (a : ZMod 4) (x : ℝ) : ℝ :=
  Real.log x ^ (1 / (Nat.totient 4 : ℝ)) *
    ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ZMod 4) = a),
      (1 - 1 / (p : ℝ))

private noncomputable def secondProduct (a : ZMod 4) (x : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ZMod 4) = a),
    (1 - 1 / (p : ℝ) ^ 2)

private noncomputable def wallisProduct (S : Finset (ZMod 4)) (x : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ZMod 4) ∈ S),
    ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4))

-- The class `3` has character `-1`, so it inverts its constant and contributes a factor `log x`.
example (C D : ZMod 4 → ℝ) (hC : Tendsto (firstProduct 3) atTop (𝓝 (C 3)))
    (hD : Tendsto (secondProduct 3) atTop (𝓝 (D 3))) :
    Tendsto (fun x => wallisProduct {3} x / ((C 3 ^ 2 / D 3)⁻¹ * Real.log x)) atTop (𝓝 1) := by
  have h := (thinned_wallis_prime_product_constant 2 le_rfl {3} (by decide) C D
    (by
      intro a ha
      obtain rfl := Finset.mem_singleton.mp ha
      exact hC)
    (by
      intro a ha
      obtain rfl := Finset.mem_singleton.mp ha
      exact hD)).1
  change Tendsto (fun x => wallisProduct {3} x /
      ((∏ a ∈ ({3} : Finset (ZMod 4)), (C a ^ 2 / D a) ^ ZMod.χ₄ (a.val : ZMod 4)) *
        Real.log x ^ (-2 * ((∑ a ∈ ({3} : Finset (ZMod 4)),
          ZMod.χ₄ (a.val : ZMod 4) : ℤ) : ℝ) / (Nat.totient 4 : ℝ)))) atTop (𝓝 1) at h
  simpa [show ZMod.χ₄ ((3 : ZMod 4).val : ZMod 4) = -1 by decide,
    show Nat.totient 4 = 2 by decide, show -2 * (-1 : ℝ) / 2 = 1 by norm_num] using h

-- The classes `1` and `3` cancel the exponent and leave a positive-class factor and its opposite.
example (C D : ZMod 4 → ℝ)
    (hC : ∀ a ∈ ({1, 3} : Finset (ZMod 4)), Tendsto (firstProduct a) atTop (𝓝 (C a)))
    (hD : ∀ a ∈ ({1, 3} : Finset (ZMod 4)), Tendsto (secondProduct a) atTop (𝓝 (D a))) :
    Tendsto (wallisProduct {1, 3}) atTop (𝓝 ((C 1 ^ 2 / D 1) * (C 3 ^ 2 / D 3)⁻¹)) := by
  have h := (thinned_wallis_prime_product_constant 2 le_rfl {1, 3} (by decide) C D hC hD).2
    (by decide)
  change Tendsto (wallisProduct {1, 3}) atTop
    (𝓝 (∏ a ∈ ({1, 3} : Finset (ZMod 4)), (C a ^ 2 / D a) ^ ZMod.χ₄ (a.val : ZMod 4))) at h
  simpa [Finset.prod_insert (by decide : (1 : ZMod 4) ∉ ({3} : Finset (ZMod 4))),
    show ZMod.χ₄ ((1 : ZMod 4).val : ZMod 4) = 1 by decide,
    show ZMod.χ₄ ((3 : ZMod 4).val : ZMod 4) = -1 by decide] using h

-- No class-limit hypotheses are needed for the empty choice of residues.
example : Tendsto (wallisProduct ∅) atTop (𝓝 1) := by
  have h := (thinned_wallis_prime_product_constant 2 le_rfl ∅ (by simp)
    (fun _ => 0) (fun _ => 0) (by simp) (by simp)).2 (by simp)
  change Tendsto (wallisProduct ∅) atTop
    (𝓝 (∏ a ∈ (∅ : Finset (ZMod 4)), ((0 : ℝ) ^ 2 / 0) ^ ZMod.χ₄ (a.val : ZMod 4))) at h
  simpa only [Finset.prod_empty] using h
