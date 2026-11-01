/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE25xA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE25xB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE25
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ

/-! # Dense identification E25-: the Fifth image at Eighth root 25; Eighth root 25 closed

`h` = the representative coset of Eighth root 25 (`e25H`); the inverse triality image of
`h v₈` is identified with an H-image of the Fifth representative (exact packed pairing `128`, `pairTriGZT`).
With the other image (`e25p_ident`, Eighth target, `GeneratedAxisGlobalIdentE25`) this closes Eighth
root 25 through goctad's wrapper `generatedAxisGlobalTwelveEighthBind_root25` (explicit identifications only). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e25x_pair : pairTriGZT 32 64 false e25VH e25xVW e25XH e25xXW e25EH e25xEW = 128 := by
  rw [pairTriGZT_parts e25x_octOk e25x_partM e25x_partP e25x_partO e25x_partA e25x_partB e25x_partC,
    show e25xVW.sden = 1 / 16 from rfl, show e25VH.sden = 1 / 32 from e8SrcVecS_sden, e25x_EH, e25x_EW]
  norm_num

/-- Inverse triality: `sExtra⁻¹ (h v₈) = W v` (E25-, Fifth target). -/
theorem e25x_ident :
    sExtra.symm (rhoLocal (identWordLocal e25H) (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal e25xW) (generatedAxisGlobalTwelveRepresentative 4) :=
  ident_inverse_GZT 7 4 _ _ e25VH e25xVW e25VH_ok e25xVW_ok e25VH_ten e25xVW_ten e25XH_bnd (by norm_num)
    e25VH_actual e25xVW_actual e25x_pair

/-- Eighth root 25: both triality images at its representative coset lie in the union of the twelve
local orbits (explicit identifications). -/
theorem e25_root : GeneratedAxisGlobalTwelveEighthRootBound 25 :=
  generatedAxisGlobalTwelveEighthBind_root25
    ⟨7, identWordLocal e25P, by rw [e25_coset]; exact e25p_ident⟩
    ⟨4, identWordLocal e25xW, by rw [e25_coset]; exact e25x_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
