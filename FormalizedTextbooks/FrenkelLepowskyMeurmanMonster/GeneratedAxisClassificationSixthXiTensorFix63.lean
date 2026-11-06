/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiLiteralFix63

/-! Exact original signed Gaussian checks cover a bounded portion of the complete tensor support. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every nonzero original tensor coordinate in this interval has the exact preferred Xi
numerator. -/
theorem generatedSixth_xi_tensor_fix63 : ∀ a : Fin 64, ∀ i : Fin 24,
    let n : Fin 4096 := ⟨63 * 64 + a.val, by omega⟩
    generatedSixthTensorFastExecutable n i ≠ 0 →
      generatedSixthXiCachedTensor n i = 16 * generatedSixthTensorFastExecutable n i :=
  generatedSixth_xi_literal_fix63

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
