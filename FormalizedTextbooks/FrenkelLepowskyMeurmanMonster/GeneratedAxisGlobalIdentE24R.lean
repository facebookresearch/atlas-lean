/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE24p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE24m

/-! # Eighth root 24 closed from two cross-family identifications

Positive image: `e24p_ident` (E24+, Sixth target); inverse image: `e24m_ident` (E24-,
Seventh target); goctad's wrapper `generatedAxisGlobalTwelveEighthBind_root24` (explicit identifications only). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Eighth root 24: both triality images at its representative coset lie in the union of the twelve
local orbits (explicit identifications). -/
theorem e24_root : GeneratedAxisGlobalTwelveEighthRootBound 24 :=
  e24p_root_of_neg ⟨6, identWordLocal e24mW, by rw [e24m_coset]; exact e24m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
