/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE23p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE23m

/-! # Eighth root 23 closed from two cross-family identifications

Positive image: `e23p_ident` (E23+, Tenth target); inverse image: `e23m_ident` (E23-,
Root8 target); goctad's wrapper `generatedAxisGlobalTwelveEighthBind_root23` (explicit identifications only). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Eighth root 23: both triality images at its representative coset lie in the union of the twelve
local orbits (explicit identifications). -/
theorem e23_root : GeneratedAxisGlobalTwelveEighthRootBound 23 :=
  e23p_root_of_neg ⟨9, identWordLocal e23mW, by rw [e23m_coset]; exact e23m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
