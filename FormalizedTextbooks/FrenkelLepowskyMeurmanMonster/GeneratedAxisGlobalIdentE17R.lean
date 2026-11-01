/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE17p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE17m

/-! # Eighth root 17 closed from two cross-family identifications

Positive image: `e17p_ident` (E17+, Twelfth target); inverse image: `e17m_ident` (E17-,
Root8 target); goctad's wrapper `generatedAxisGlobalTwelveEighthBind_root17` (explicit identifications only). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Eighth root 17: both triality images at its representative coset lie in the union of the twelve
local orbits (explicit identifications). -/
theorem e17_root : GeneratedAxisGlobalTwelveEighthRootBound 17 :=
  e17p_root_of_neg ⟨9, identWordLocal e17mW, by rw [e17m_coset]; exact e17m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
