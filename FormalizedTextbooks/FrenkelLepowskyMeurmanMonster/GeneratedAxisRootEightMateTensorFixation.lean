/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorCertificate

/-! Unconditional tensor fixation by the genuine original corrected mate, including every zero. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Every original spin address and phase is certified without a fixation premise. -/
theorem generatedRootEight_mate_tensor_address_actual (n : Fin 4096) :
    generatedRootEightMateTensorAddressCondition n := by
  let b : Fin 16 := ⟨n.val / 256, by omega⟩
  let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : (⟨b.val * 256 + u.val, by omega⟩ : Fin 4096) = n := by
    apply Fin.ext
    dsimp only [b, u]
    omega
  have h := generatedRootEight_mate_tensor_addresses_blocks b u
  rw [he] at h
  exact h

/-- The entire actual canonical tensor is fixed by the genuine corrected mate. -/
theorem generatedRootEight_mate_corrected_canonical_tensor (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation generatedRootEightMateCorrectedFiber
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 t i =
        (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 t i := by
  rw [generatedRootEight_mate_tensor_coordinate generatedRootEight_mate_tensor_address_actual]
  rw [generatedRootEight_canonical_tensor_raw_actual,
    generatedRootEight_canonical_tensor_raw_actual, nortonUIntegerLabel_coeff]
  have hc := generatedRootEight_mate_tensor_cache_actual (nortonUIntegerLabel t) i
  unfold generatedRootEightMateTensorCacheCondition at hc
  have hr := congrArg (fun z : ℤ => (z : ℝ) / (16 * Real.sqrt 2)) hc
  simpa only [Int.cast_mul, Int.cast_neg, mul_div_assoc] using hr

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
