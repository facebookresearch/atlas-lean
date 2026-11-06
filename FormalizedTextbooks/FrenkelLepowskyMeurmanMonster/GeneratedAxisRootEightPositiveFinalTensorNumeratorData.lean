/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingPositiveTensorNumeratorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightShortCache

/-! Every complete final integer tensor numerator retains both original XYZ contributions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The full final numerator uses the complete original odd-short and incoming tensor values. -/
def generatedRootEightPositiveFinalTensorNumerator (n : Fin 4096) (i : Fin 24) : ℤ :=
  let t := golayLabelCoefficients n
  let d := spinDictionaryCode t
  let s : ℤ := if (golayEncodedMask d.val).testBit i.val then -1 else 1
  8 * nortonUIntegerSign (t 11) * s *
      generatedFifthRootEightShortCachedCoefficient (Sum.inr (Sum.inr (d, i))) +
    nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) * s *
      (generatedRootEightIncomingPositiveTensorNumerator ⟨d.val, by omega⟩ i -
        generatedRootEightIncomingPositiveTensorNumerator ⟨d.val + 2048, by omega⟩ i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
