/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE16p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE16m

/-! # Eighth root 16 closed from two cross-family identifications

Positive image: `e16p_ident` (E16+, Root8 target); inverse image: `e16m_ident` (E16-,
Root8 target); goctad's wrapper `generatedAxisGlobalTwelveEighthBind_root16` (explicit identifications only). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Eighth root 16: both triality images at its representative coset lie in the union of the twelve
local orbits (explicit identifications). -/
theorem e16_root : GeneratedAxisGlobalTwelveEighthRootBound 16 :=
  e16p_root_of_neg ⟨9, identWordLocal e16mW, by rw [e16m_coset]; exact e16m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
