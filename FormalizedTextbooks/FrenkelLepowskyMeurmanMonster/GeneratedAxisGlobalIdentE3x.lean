/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE3xA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE3xB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF

/-! # Dense identification E3+: the Sixth image at Eighth root 3; Eighth root 3 closed

`h` = the representative coset of Eighth root 3 (`e3H`); the positive triality image of
`h v₈` is identified with an H-image of the Sixth representative (exact packed pairing `128`, `pairTriGZT`).
With the other image (`e3m_ident`, Eighth target, `GeneratedAxisGlobalIdentE3`) this closes Eighth
root 3 through goctad's wrapper `generatedAxisGlobalTwelveEighthBind_root3` (explicit identifications only). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e3x_pair : pairTriGZT 64 64 true e3VH e3xVW e3XH e3xXW e3EH e3xEW = 128 := by
  rw [pairTriGZT_parts e3x_octOk e3x_partM e3x_partP e3x_partO e3x_partA e3x_partB e3x_partC,
    show e3xVW.sden = 1 / 32 from rfl, show e3VH.sden = 1 / 32 from e8SrcVecS_sden, e3x_EH, e3x_EW]
  norm_num

/-- Positive triality: `sExtra (h v₈) = W v` (E3+, Sixth target). -/
theorem e3x_ident : sExtra (rhoLocal (identWordLocal e3H) (generatedAxisGlobalTwelveRepresentative 7)) =
    rhoLocal (identWordLocal e3xW) (generatedAxisGlobalTwelveRepresentative 5) :=
  ident_forward_GZT 7 5 _ _ e3VH e3xVW e3VH_ok e3xVW_ok e3VH_ten e3xVW_ten e3XH_bnd (by norm_num)
    e3VH_actual e3xVW_actual e3x_pair

/-- Eighth root 3: both triality images at its representative coset lie in the union of the twelve
local orbits (explicit identifications). -/
theorem e3_root : GeneratedAxisGlobalTwelveEighthRootBound 3 :=
  generatedAxisGlobalTwelveEighthBind_root3
    ⟨5, identWordLocal e3xW, by rw [e3_coset]; exact e3x_ident⟩
    ⟨7, identWordLocal e3M, by rw [e3_coset]; exact e3m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
