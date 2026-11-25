/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.FreeProbability.CentralLimit

/-!
# Odd and fourth moments in the free central limit theorem
-/

open Filter Topology NoncrossingPartition
open scoped ComplexOrder
open MathlibExt.Probability.FreeProbability MathlibExt.Probability.FreeProbabilityWanted

namespace MathlibExtTest.Probability.FreeProbability.CentralLimit

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1)
  (htrace : ∀ x y, φ (x * y) = φ (y * x)) (hpos : ∀ x, 0 ≤ φ (star x * x))
  (a : ℕ → A) (hfree : AreFree φ hφ a) (hsa : ∀ i, IsSelfAdjoint (a i))
  (hmean : ∀ i, φ (a i) = 0) (hvar : ∀ i, φ (a i ^ 2) = 1)
  (hbdd : ∀ k : ℕ, ∃ C : ℝ, ∀ i, ‖φ (a i ^ k)‖ ≤ C)

private noncomputable def normalizedSum (N : ℕ) : A :=
  (((Real.sqrt N)⁻¹ : ℝ) : ℂ) • ∑ i ∈ Finset.range N, a i

include hφ htrace hpos hfree hsa hmean hvar hbdd

example (k : ℕ) : Tendsto (fun N => φ (normalizedSum a N ^ (2 * k + 1))) atTop (𝓝 0) := by
  simpa only [normalizedSum, card_noncrossing_pairPartition_two_mul_add_one, Nat.cast_zero] using
    free_central_limit φ hφ htrace hpos a hfree hsa hmean hvar hbdd (2 * k + 1)

example : Tendsto (fun N => φ (normalizedSum a N ^ 4)) atTop (𝓝 2) := by
  have h := free_central_limit φ hφ htrace hpos a hfree hsa hmean hvar hbdd (2 * 2)
  rwa [card_noncrossing_pairPartition_two_mul, catalan_two, Nat.cast_ofNat] at h

end MathlibExtTest.Probability.FreeProbability.CentralLimit
