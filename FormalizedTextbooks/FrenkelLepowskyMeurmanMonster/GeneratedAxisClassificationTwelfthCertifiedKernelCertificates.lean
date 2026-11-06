/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedKernelData

/-! Complete candidate physical matrices and all original root-kernel word coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 8000000 in
-- Compare every entry of all nine complete physical candidate matrices.
/-- Every actual candidate numerator retains its exact complete original monomial form. -/
theorem generatedTwelfth_certified_kernel_matrix_entries : ∀ (g : Fin 9) (i j : Fin 24),
    generatedTwelfthCertifiedNumerator (generatedTwelfthCertifiedKernelIndex g) i j =
      nortonUIntegerSign (generatedTwelfthCertifiedKernelLetterSign g i) *
        if generatedTwelfthCertifiedKernelLetterBackward g i = j then 1 else 0 := by
  unfold generatedTwelfthCertifiedKernelIndex generatedTwelfthCertifiedKernelLetterSign
    generatedTwelfthCertifiedKernelLetterBackward
  decide +kernel

/-- Every original monomial candidate has exactly denominator one. -/
theorem generatedTwelfth_certified_kernel_denominators : ∀ g : Fin 9,
    generatedTwelfthCertifiedDenominator (generatedTwelfthCertifiedKernelIndex g) = 1 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Compare every complete sign word on every original physical coordinate.
/-- All thirty-two original sign words retain every actual signed physical coordinate. -/
theorem generatedTwelfth_certified_kernel_sign_words : ∀ (a : Fin 32) (i : Fin 24),
    generatedTwelfthCertifiedKernelWordData (generatedTwelfthCertifiedKernelSignWord a) i =
      ((sourceGeneratedSignCode (generatedTwelfthRootKernelTotalLabel false a)).val i, i) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Compare every complete permutation word on every original physical coordinate.
/-- All sixteen original pure permutation words retain their complete actual pullback. -/
theorem generatedTwelfth_certified_kernel_permutation_words : ∀ (p : Fin 16) (i : Fin 24),
    generatedTwelfthCertifiedKernelWordData (generatedTwelfthCertifiedKernelPermutationWord p) i =
      (0, generatedTwelfthRootKernelPermutationBackward p i) := by
  decide +kernel

/-- The genuine all-ones code bit reverses every original complete physical sign coordinate. -/
theorem generatedTwelfth_certified_kernel_total_sign : ∀ (a : Fin 32) (i : Fin 24),
    (sourceGeneratedSignCode (generatedTwelfthRootKernelTotalLabel true a)).val i =
      1 + (sourceGeneratedSignCode (generatedTwelfthRootKernelTotalLabel false a)).val i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
