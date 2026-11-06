/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE11xA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE11xB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification E11-: the Twelfth image at Eighth root 11

`h` = the representative coset of Eighth root 11 (`e11H`); the inverse triality image of
`h v₈` is identified with an H-image of the Twelfth representative (exact packed pairing `128`, `pairTriGZT`).
With the other image (`e11p_ident`, Eighth target, `GeneratedAxisGlobalIdentE11`) this closes Eighth
root 11 through goctad's wrapper `generatedAxisGlobalTwelveEighthBind_root11` (explicit identifications only). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e11x_pair : pairTriGZT 32 64 false e11VH e11xVW e11XH e11xXW e11EH e11xEW = 128 := by
  rw [pairTriGZT_parts e11x_octOk e11x_partM e11x_partP e11x_partO e11x_partA e11x_partB e11x_partC,
    show e11xVW.sden = (1 / 128) from rfl, show e11VH.sden = 1 / 32 from e8SrcVecS_sden, e11x_EH, e11x_EW]
  norm_num

/-- Inverse triality: `sExtra⁻¹ (h v₈) = W v` (E11-, Twelfth target). -/
theorem e11x_ident :
    sExtra.symm (rhoLocal (identWordLocal e11H) (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal e11xW) (generatedAxisGlobalTwelveRepresentative 10) :=
  ident_inverse_GZT 7 10 _ _ e11VH e11xVW e11VH_ok e11xVW_ok e11VH_ten e11xVW_ten e11XH_bnd (by norm_num)
    e11VH_actual e11xVW_actual e11x_pair

/-- Eighth root 11: both triality images at its representative coset lie in the union of the twelve
local orbits (explicit identifications). -/
theorem e11_root : GeneratedAxisGlobalTwelveEighthRootBound 11 :=
  generatedAxisGlobalTwelveEighthBind_root11
    ⟨7, identWordLocal e11P, by rw [e11_coset]; exact e11p_ident⟩
    ⟨10, identWordLocal e11xW, by rw [e11_coset]; exact e11x_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
