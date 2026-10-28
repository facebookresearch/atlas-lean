/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE12x

/-! # Eighth root 18 from the identifications at the coset of Eighth root 12 (triangle)

The positive image at the coset of root 12 is exactly the coset of root 18: the record word `e12P` is
goctad's `generatedAxisGlobalTwelveEighthBindPre18` followed by the letters of
`generatedAxisGlobalTwelveEighthBindWord18` (`e18_coset`, by `rfl`), so `e12p_ident` is the transport
hypothesis `htr` of goctad's wrapper `generatedAxisGlobalTwelveEighthBind_root18`; the inverse image at the coset of
root 12 is `e12x_ident` (Tenth target).  Explicit identifications only. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The representative coset of Eighth root 18 is the target word of the positive image at root 12. -/
theorem e18_coset : generatedAxisGlobalTwelveEighthBindCoset18 = identWordLocal e12P := rfl

/-- Eighth root 18: both triality images at its representative coset lie in the union of the twelve
local orbits. -/
theorem e18_root : GeneratedAxisGlobalTwelveEighthRootBound 18 :=
  generatedAxisGlobalTwelveEighthBind_root18
    (by rw [e12_coset, e18_coset]; exact e12p_ident)
    ⟨11, identWordLocal e12xW, by rw [e12_coset]; exact e12x_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
