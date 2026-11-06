/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE13p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE13m

/-! # Eighth root 13 closed from two cross-family identifications

Positive image: `e13p_ident` (E13+, Tenth target); inverse image: `e13m_ident` (E13-,
Seventh target); goctad's wrapper `generatedAxisGlobalTwelveEighthBind_root13` (explicit identifications only). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Eighth root 13: both triality images at its representative coset lie in the union of the twelve
local orbits (explicit identifications). -/
theorem e13_root : GeneratedAxisGlobalTwelveEighthRootBound 13 :=
  e13p_root_of_neg ⟨6, identWordLocal e13mW, by rw [e13m_coset]; exact e13m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
