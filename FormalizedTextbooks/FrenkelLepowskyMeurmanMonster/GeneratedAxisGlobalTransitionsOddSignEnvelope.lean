/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSpinEnvelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddTensorSignFactors

/-! Exact four-input dictionary support proves every omitted original source sign output is zero. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem physical_label_low_high (n : Fin 4096) :
    n = generatedAxisGlobalTensorLowLabel (generatedAxisGlobalSpinLabelLow n) ∨
      n = generatedAxisGlobalTensorHighLabel (generatedAxisGlobalSpinLabelLow n) := by
  by_cases hn : n.val < 2048
  · left
    apply Fin.ext
    change n.val = n.val % 2048
    omega
  · right
    apply Fin.ext
    change n.val = n.val % 2048 + 2048
    omega

/-- A genuine original source sign output is zero outside the complete envelope of its four actual input labels. -/
theorem generatedAxisGlobalOddSignSpin_zero_outside
    (a : Fin 2048) (u : Fin 4096 → ℤ) (E : Fin 4096 → Bool)
    (hc : ∀ e : Fin 2048,
      (u (generatedAxisGlobalTensorLowLabel e) ≠ 0 ∨
        u (generatedAxisGlobalTensorHighLabel e) ≠ 0 ∨
        u (generatedAxisGlobalTensorLowLabel
          (generatedAxisGlobalSignInputCode (generatedAxisGlobalSignLowCode a) e)) ≠ 0 ∨
        u (generatedAxisGlobalTensorHighLabel
          (generatedAxisGlobalSignInputCode (generatedAxisGlobalSignLowCode a) e)) ≠ 0) →
      E (generatedAxisGlobalTensorLowLabel e) = true ∧
        E (generatedAxisGlobalTensorHighLabel e) = true)
    (n : Fin 4096) (hn : E n = false) :
    generatedAxisGlobalOddSignSpinInteger a u n = 0 := by
  let e := generatedAxisGlobalSpinLabelLow n
  let d := generatedAxisGlobalSignInputCode (generatedAxisGlobalSignLowCode a) e
  have hz : ¬ (u (generatedAxisGlobalTensorLowLabel e) ≠ 0 ∨
      u (generatedAxisGlobalTensorHighLabel e) ≠ 0 ∨
      u (generatedAxisGlobalTensorLowLabel d) ≠ 0 ∨
      u (generatedAxisGlobalTensorHighLabel d) ≠ 0) := by
    intro hi
    have he := hc e hi
    rcases physical_label_low_high n with hl | hh
    · have h := he.1
      change E (generatedAxisGlobalTensorLowLabel (generatedAxisGlobalSpinLabelLow n)) = true at h
      rw [← hl, hn] at h
      contradiction
    · have h := he.2
      change E (generatedAxisGlobalTensorHighLabel (generatedAxisGlobalSpinLabelLow n)) = true at h
      rw [← hh, hn] at h
      contradiction
  push Not at hz
  rcases hz with ⟨hL, hH, hDL, hDH⟩
  simp only [generatedAxisGlobalOddSignSpinInteger]
  change _ * _ * (u (generatedAxisGlobalTensorLowLabel d) -
      u (generatedAxisGlobalTensorHighLabel d)) +
    _ * _ * (u (generatedAxisGlobalTensorLowLabel e) + u (generatedAxisGlobalTensorHighLabel e)) = 0
  rw [hL, hH, hDL, hDH]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
