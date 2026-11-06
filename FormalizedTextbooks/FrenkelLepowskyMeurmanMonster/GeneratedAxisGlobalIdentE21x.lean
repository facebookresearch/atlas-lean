/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE21xA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE21xB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE21
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh

/-! # Dense identification E21+: the Seventh image at Eighth root 21

`h` = the representative coset of Eighth root 21 (`e21H`); the positive triality image of
`h v₈` is identified with an H-image of the Seventh representative (exact packed pairing `128`, `pairTriGZT`).
With the other image (`e21m_ident`, Eighth target, `GeneratedAxisGlobalIdentE21`) this closes Eighth
root 21 through goctad's wrapper `generatedAxisGlobalTwelveEighthBind_root21` (explicit identifications only). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e21x_pair : pairTriGZT 32 64 true e21VH e21xVW e21XH e21xXW e21EH e21xEW = 128 := by
  rw [pairTriGZT_parts e21x_octOk e21x_partM e21x_partP e21x_partO e21x_partA e21x_partB e21x_partC,
    show e21xVW.sden = (1 / 32) from rfl, show e21VH.sden = 1 / 32 from e8SrcVecS_sden, e21x_EH, e21x_EW]
  norm_num

/-- Positive triality: `sExtra (h v₈) = W v` (E21+, Seventh target). -/
theorem e21x_ident : sExtra (rhoLocal (identWordLocal e21H) (generatedAxisGlobalTwelveRepresentative 7)) =
    rhoLocal (identWordLocal e21xW) (generatedAxisGlobalTwelveRepresentative 6) :=
  ident_forward_GZT 7 6 _ _ e21VH e21xVW e21VH_ok e21xVW_ok e21VH_ten e21xVW_ten e21XH_bnd (by norm_num)
    e21VH_actual e21xVW_actual e21x_pair

/-- Eighth root 21: both triality images at its representative coset lie in the union of the twelve
local orbits (explicit identifications). -/
theorem e21_root : GeneratedAxisGlobalTwelveEighthRootBound 21 :=
  generatedAxisGlobalTwelveEighthBind_root21
    ⟨6, identWordLocal e21xW, by rw [e21_coset]; exact e21x_ident⟩
    ⟨7, identWordLocal e21M, by rw [e21_coset]; exact e21m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
