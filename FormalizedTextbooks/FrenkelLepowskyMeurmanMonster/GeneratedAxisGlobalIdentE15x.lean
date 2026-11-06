/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE15xA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE15xB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification E15+: the Root8 image at Eighth root 15

`h` = the representative coset of Eighth root 15 (`e15H`); the positive triality image of
`h v₈` is identified with an H-image of the Root8 representative (exact packed pairing `128`, `pairTriGZT`).
With the other image (`e15m_ident`, Eighth target, `GeneratedAxisGlobalIdentE15`) this closes Eighth
root 15 through goctad's wrapper `generatedAxisGlobalTwelveEighthBind_root15` (explicit identifications only). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e15x_pair : pairTriGZT 64 64 true e15VH e15xVW e15XH e15xXW e15EH e15xEW = 128 := by
  rw [pairTriGZT_parts e15x_octOk e15x_partM e15x_partP e15x_partO e15x_partA e15x_partB e15x_partC,
    show e15xVW.sden = (1 / 128) from rfl, show e15VH.sden = 1 / 32 from e8SrcVecS_sden, e15x_EH, e15x_EW]
  norm_num

/-- Positive triality: `sExtra (h v₈) = W v` (E15+, Root8 target). -/
theorem e15x_ident : sExtra (rhoLocal (identWordLocal e15H) (generatedAxisGlobalTwelveRepresentative 7)) =
    rhoLocal (identWordLocal e15xW) (generatedAxisGlobalTwelveRepresentative 9) :=
  ident_forward_GZT 7 9 _ _ e15VH e15xVW e15VH_ok e15xVW_ok e15VH_ten e15xVW_ten e15XH_bnd (by norm_num)
    e15VH_actual e15xVW_actual e15x_pair

/-- Eighth root 15: both triality images at its representative coset lie in the union of the twelve
local orbits (explicit identifications). -/
theorem e15_root : GeneratedAxisGlobalTwelveEighthRootBound 15 :=
  generatedAxisGlobalTwelveEighthBind_root15
    ⟨9, identWordLocal e15xW, by rw [e15_coset]; exact e15x_ident⟩
    ⟨7, identWordLocal e15M, by rw [e15_coset]; exact e15m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
