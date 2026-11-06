/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTriality

/-! Complete odd-short coordinates skip the original weight phase only for an exactly zero input sum. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The genuine original odd-short triality coefficient with an exact zero sum guard. -/
def generatedAxisGlobalRationalOddShortZeroGuard (a : GeneratedAxisGlobalRationalPacket)
    (d : Fin 2048) (j : Fin 24) : ℚ :=
  let c := a.2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) j +
    a.2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) j
  if c = 0 then 0 else
    (generatedAxisGlobalIntSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) : ℚ) * c / 2

/-- The guard preserves the full original rational source operator at every odd-short coordinate. -/
theorem generatedAxisGlobalRationalOddShortZeroGuard_actual (a : GeneratedAxisGlobalRationalPacket)
    (d : Fin 2048) (j : Fin 24) :
    generatedAxisGlobalRationalOddShortZeroGuard a d j =
      (generatedAxisGlobalRationalTriality a).2.1 (Sum.inr (Sum.inr (d, j))) := by
  simp only [generatedAxisGlobalRationalOddShortZeroGuard, generatedAxisGlobalRationalTriality,
    generatedAxisGlobalTrialityShortQ]
  split_ifs with hc
  · simp only [hc, mul_zero, zero_div]
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
