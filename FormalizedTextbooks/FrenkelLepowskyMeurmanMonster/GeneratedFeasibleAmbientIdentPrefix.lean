/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthIdent
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBind

/-! # Admissible identification prefixes

The binding wrappers for a vertex reached behind a prefix (`twelfthRoot_of_target_forward` and
`twelfthRoot_of_target_inverse` of worker gtwelfth, `sixthPhase_of_forward_identity` and
`sixthPhase_of_inverse_identity` of worker gforest) need the prefix letters to be phase letters
without Xi. Both facts follow from one Boolean check,
`M.all generatedAxisGlobalTwelveTenthPrefixLetter` (worker gtenth's admissible prefix letters),
which is decided for each concrete prefix. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- A prefix of admissible letters consists of phase letters without Xi. -/
theorem fbIdentPrefix_letters {M : List IdentLetter}
    (h : M.all generatedAxisGlobalTwelveTenthPrefixLetter = true) :
    (∀ l ∈ M, SixthPhaseLetter l) ∧ ∀ l ∈ M, l ≠ IdentLetter.xi := by
  rw [List.all_eq_true] at h
  constructor
  · intro l hl
    have hl' := h l hl
    cases l with
    | xi => exact True.intro
    | sign a ε =>
      change ε = 0
      simpa [generatedAxisGlobalTwelveTenthPrefixLetter] using hl'
    | mono m => exact True.intro
    | qel g => exact True.intro
  · intro l hl he
    subst he
    have hl' := h _ hl
    simp [generatedAxisGlobalTwelveTenthPrefixLetter] at hl'

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
