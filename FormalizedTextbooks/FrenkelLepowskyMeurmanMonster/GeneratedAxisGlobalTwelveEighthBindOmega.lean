/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthPhase

/-! One identification each for Eighth roots 6 and 28.

The numeric self-transports `E6+` and `E28+` of goctad have the form
`sExtra (h · v₈) = (M ++ T) · v₈`, where `T` is the identification word of the representative
coset `h` itself and `M` is an Xi-free prefix. The Q-phase fold of `M` fixes the Ω mask (checked
here), so `M` lies in the actual local Ω stabilizer, and the identification also gives the inverse
image at `h` (gforest's `sixthPhase_of_forward_identity`). Each root is then bound by one
identification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Letters allowed in an Ω-stabilizer prefix: no Xi, and source signs with phase `0`. -/
def eighthBindOmegaLetter : IdentLetter → Bool
  | .xi => false
  | .sign _ ε => ε == 0
  | _ => true

/-- An admissible prefix has only source-phase letters and no Xi. -/
theorem eighthBindOmega_letters {M : List IdentLetter}
    (h : M.all eighthBindOmegaLetter = true) :
    (∀ l ∈ M, SixthPhaseLetter l) ∧ ∀ l ∈ M, l ≠ IdentLetter.xi := by
  rw [List.all_eq_true] at h
  constructor
  · intro l hl
    have hl' := h l hl
    cases l with
    | xi => exact True.intro
    | sign a ε =>
      change ε = 0
      simpa [eighthBindOmegaLetter] using hl'
    | mono m => exact True.intro
    | qel g => exact True.intro
  · intro l hl he
    subst he
    have hl' := h _ hl
    simp [eighthBindOmegaLetter] at hl'

/-- The Ω-fixing prefix of the self-transport `E6+`. -/
def generatedAxisGlobalTwelveEighthBindOmegaPre6 : List IdentLetter :=
  [IdentLetter.qel (qCentral 0 * generatedAxisGlobalQMask 7766936), IdentLetter.sign 436 0,
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, true), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, true), IdentLetter.mono (0, false),
    IdentLetter.mono (1, true), IdentLetter.mono (0, true), IdentLetter.mono (1, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true)]

set_option maxRecDepth 100000 in
/-- The Q-phase fold of the prefix of `E6+` fixes the Ω mask. -/
theorem generatedAxisGlobalTwelveEighthBindOmegaPre6_phase :
    qmWord (generatedAxisGlobalTwelveEighthBindOmegaPre6.map sixthPhaseData) (2048, false) =
      (2048, false) := by
  decide +kernel

/-- The prefix of `E6+` is admissible. -/
theorem generatedAxisGlobalTwelveEighthBindOmegaPre6_admissible :
    generatedAxisGlobalTwelveEighthBindOmegaPre6.all eighthBindOmegaLetter = true := by
  decide

/-- The prefix of `E6+` lies in the actual local Ω stabilizer. -/
theorem generatedAxisGlobalTwelveEighthBindOmegaPre6_mem :
    identWordLocal generatedAxisGlobalTwelveEighthBindOmegaPre6 ∈ localOmegaStabilizer :=
  sixthPhase_mem _
    (eighthBindOmega_letters generatedAxisGlobalTwelveEighthBindOmegaPre6_admissible).1
    generatedAxisGlobalTwelveEighthBindOmegaPre6_phase

/-- Eighth root 6 from the single self-transport `E6+`, whose prefix fixes Ω. -/
theorem generatedAxisGlobalTwelveEighthBind_root6_omega
    (hid : sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset6 generatedEighthAxis) =
      rhoLocal (identWordLocal (generatedAxisGlobalTwelveEighthBindOmegaPre6 ++
        generatedAxisGlobalTwelveEighthBindWord6.map eighthBindIdent)) generatedEighthAxis) :
    GeneratedAxisGlobalTwelveEighthRootBound 6 := by
  obtain ⟨hl, hx⟩ :=
    eighthBindOmega_letters generatedAxisGlobalTwelveEighthBindOmegaPre6_admissible
  have hneg := (sixthPhase_of_forward_identity 7 generatedAxisGlobalTwelveEighthBindCoset6
    generatedAxisGlobalTwelveEighthBindOmegaPre6
    (generatedAxisGlobalTwelveEighthBindWord6.map eighthBindIdent) hl hx
    generatedEighthAxis hid).1 generatedAxisGlobalTwelveEighthBindOmegaPre6_phase
  exact eighthBind_rootBound 6 [] (by decide) generatedAxisGlobalTwelveEighthBindWord6 (by decide)
    [12, 12, 14, 14, 5, 14, 6] (by decide +kernel)
    (generatedAxisGlobalTwelve_mem_of_transport 7 _ hid) hneg

/-- The Ω-fixing prefix of the self-transport `E28+`. -/
def generatedAxisGlobalTwelveEighthBindOmegaPre28 : List IdentLetter :=
  [IdentLetter.qel (qCentral 1 * generatedAxisGlobalQMask 4030716), IdentLetter.sign 1815 0]

set_option maxRecDepth 100000 in
/-- The Q-phase fold of the prefix of `E28+` fixes the Ω mask. -/
theorem generatedAxisGlobalTwelveEighthBindOmegaPre28_phase :
    qmWord (generatedAxisGlobalTwelveEighthBindOmegaPre28.map sixthPhaseData) (2048, false) =
      (2048, false) := by
  decide +kernel

/-- The prefix of `E28+` is admissible. -/
theorem generatedAxisGlobalTwelveEighthBindOmegaPre28_admissible :
    generatedAxisGlobalTwelveEighthBindOmegaPre28.all eighthBindOmegaLetter = true := by
  decide

/-- The prefix of `E28+` lies in the actual local Ω stabilizer. -/
theorem generatedAxisGlobalTwelveEighthBindOmegaPre28_mem :
    identWordLocal generatedAxisGlobalTwelveEighthBindOmegaPre28 ∈ localOmegaStabilizer :=
  sixthPhase_mem _
    (eighthBindOmega_letters generatedAxisGlobalTwelveEighthBindOmegaPre28_admissible).1
    generatedAxisGlobalTwelveEighthBindOmegaPre28_phase

/-- Eighth root 28 from the single self-transport `E28+`, whose prefix fixes Ω. -/
theorem generatedAxisGlobalTwelveEighthBind_root28_omega
    (hid : sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset28 generatedEighthAxis) =
      rhoLocal (identWordLocal (generatedAxisGlobalTwelveEighthBindOmegaPre28 ++
        generatedAxisGlobalTwelveEighthBindWord28.map eighthBindIdent)) generatedEighthAxis) :
    GeneratedAxisGlobalTwelveEighthRootBound 28 := by
  obtain ⟨hl, hx⟩ :=
    eighthBindOmega_letters generatedAxisGlobalTwelveEighthBindOmegaPre28_admissible
  have hneg := (sixthPhase_of_forward_identity 7 generatedAxisGlobalTwelveEighthBindCoset28
    generatedAxisGlobalTwelveEighthBindOmegaPre28
    (generatedAxisGlobalTwelveEighthBindWord28.map eighthBindIdent) hl hx
    generatedEighthAxis hid).1 generatedAxisGlobalTwelveEighthBindOmegaPre28_phase
  exact eighthBind_rootBound 28 [] (by decide) generatedAxisGlobalTwelveEighthBindWord28 (by decide)
    [12, 14, 14, 12, 0] (by decide +kernel)
    (generatedAxisGlobalTwelve_mem_of_transport 7 _ hid) hneg

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
