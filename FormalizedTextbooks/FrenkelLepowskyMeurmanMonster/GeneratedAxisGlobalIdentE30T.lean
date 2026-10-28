/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE11x

/-! # Eighth root 30 from the identifications at the coset of Eighth root 11 (triangle)

The positive image at the coset of root 11 is exactly the coset of root 30: the record word `e11P` is
goctad's `generatedAxisGlobalTwelveEighthBindPre30` followed by the letters of
`generatedAxisGlobalTwelveEighthBindWord30` (`e30_coset`, by `rfl`), so `e11p_ident` is the transport
hypothesis `htr` of goctad's wrapper `generatedAxisGlobalTwelveEighthBind_root30`; the inverse image at the coset of
root 11 is `e11x_ident` (Twelfth target).  Explicit identifications only. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The representative coset of Eighth root 30 is the target word of the positive image at root 11. -/
theorem e30_coset : generatedAxisGlobalTwelveEighthBindCoset30 = identWordLocal e11P := rfl

/-- Eighth root 30: both triality images at its representative coset lie in the union of the twelve
local orbits. -/
theorem e30_root : GeneratedAxisGlobalTwelveEighthRootBound 30 :=
  generatedAxisGlobalTwelveEighthBind_root30
    (by rw [e11_coset, e30_coset]; exact e11p_ident)
    ⟨10, identWordLocal e11xW, by rw [e11_coset]; exact e11x_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
