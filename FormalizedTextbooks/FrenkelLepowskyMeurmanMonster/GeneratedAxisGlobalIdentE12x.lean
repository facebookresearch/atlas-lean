/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE12xA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE12xB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Dense identification E12-: the Tenth image at Eighth root 12

`h` = the representative coset of Eighth root 12 (`e12H`); the inverse triality image of
`h v₈` is identified with an H-image of the Tenth representative (exact packed pairing `128`, `pairTriGZT`).
With the other image (`e12p_ident`, Eighth target, `GeneratedAxisGlobalIdentE12`) this closes Eighth
root 12 through goctad's wrapper `generatedAxisGlobalTwelveEighthBind_root12` (explicit identifications only). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e12x_pair : pairTriGZT 64 64 false e12VH e12xVW e12XH e12xXW e12EH e12xEW = 128 := by
  rw [pairTriGZT_parts e12x_octOk e12x_partM e12x_partP e12x_partO e12x_partA e12x_partB e12x_partC,
    show e12xVW.sden = (1 / 128) from rfl, show e12VH.sden = 1 / 32 from e8SrcVecS_sden, e12x_EH, e12x_EW]
  norm_num

/-- Inverse triality: `sExtra⁻¹ (h v₈) = W v` (E12-, Tenth target). -/
theorem e12x_ident :
    sExtra.symm (rhoLocal (identWordLocal e12H) (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal e12xW) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_inverse_GZT 7 11 _ _ e12VH e12xVW e12VH_ok e12xVW_ok e12VH_ten e12xVW_ten e12XH_bnd (by norm_num)
    e12VH_actual e12xVW_actual e12x_pair

/-- Eighth root 12: both triality images at its representative coset lie in the union of the twelve
local orbits (explicit identifications). -/
theorem e12_root : GeneratedAxisGlobalTwelveEighthRootBound 12 :=
  generatedAxisGlobalTwelveEighthBind_root12
    ⟨7, identWordLocal e12P, by rw [e12_coset]; exact e12p_ident⟩
    ⟨11, identWordLocal e12xW, by rw [e12_coset]; exact e12x_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
