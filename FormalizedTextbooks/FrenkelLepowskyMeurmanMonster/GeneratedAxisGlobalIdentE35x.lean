/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE35xA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE35xB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE35
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification E35-: the Root8 image at Eighth root 35

`h` = the representative coset of Eighth root 35 (`e35H`); the inverse triality image of
`h v₈` is identified with an H-image of the Root8 representative (exact packed pairing `128`, `pairTriGZT`).
With the other image (`e35p_ident`, Eighth target, `GeneratedAxisGlobalIdentE35`) this closes Eighth
root 35 through goctad's wrapper `generatedAxisGlobalTwelveEighthBind_root35` (explicit identifications only). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e35x_pair : pairTriGZT 64 64 false e35VH e35xVW e35XH e35xXW e35EH e35xEW = 128 := by
  rw [pairTriGZT_parts e35x_octOk e35x_partM e35x_partP e35x_partO e35x_partA e35x_partB e35x_partC,
    show e35xVW.sden = (1 / 128) from rfl, show e35VH.sden = 1 / 32 from e8SrcVecS_sden, e35x_EH, e35x_EW]
  norm_num

/-- Inverse triality: `sExtra⁻¹ (h v₈) = W v` (E35-, Root8 target). -/
theorem e35x_ident :
    sExtra.symm (rhoLocal (identWordLocal e35H) (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal e35xW) (generatedAxisGlobalTwelveRepresentative 9) :=
  ident_inverse_GZT 7 9 _ _ e35VH e35xVW e35VH_ok e35xVW_ok e35VH_ten e35xVW_ten e35XH_bnd (by norm_num)
    e35VH_actual e35xVW_actual e35x_pair

/-- Eighth root 35: both triality images at its representative coset lie in the union of the twelve
local orbits (explicit identifications). -/
theorem e35_root : GeneratedAxisGlobalTwelveEighthRootBound 35 :=
  generatedAxisGlobalTwelveEighthBind_root35
    ⟨7, identWordLocal e35P, by rw [e35_coset]; exact e35p_ident⟩
    ⟨9, identWordLocal e35xW, by rw [e35_coset]; exact e35x_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
