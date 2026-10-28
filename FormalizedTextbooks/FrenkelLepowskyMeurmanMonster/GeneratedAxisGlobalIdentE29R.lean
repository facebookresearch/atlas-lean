/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE29p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE29m

/-! # Eighth root 29 closed from two cross-family identifications

Positive image: `e29p_ident` (E29+, Twelfth target); inverse image: `e29m_ident` (E29-,
Twelfth target); goctad's wrapper `generatedAxisGlobalTwelveEighthBind_root29` (explicit identifications only). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Eighth root 29: both triality images at its representative coset lie in the union of the twelve
local orbits (explicit identifications). -/
theorem e29_root : GeneratedAxisGlobalTwelveEighthRootBound 29 :=
  e29p_root_of_neg ⟨10, identWordLocal e29mW, by rw [e29m_coset]; exact e29m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
