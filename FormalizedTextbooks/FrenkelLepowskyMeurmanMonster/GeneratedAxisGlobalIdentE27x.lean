/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE27xA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE27xB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE27
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamFourth

/-! # Dense identification E27+: the Fourth image at Eighth root 27

`h` = the representative coset of Eighth root 27 (`e27H`); the positive triality image of
`h v₈` is identified with an H-image of the Fourth representative (exact packed pairing `128`, `pairTriGZT`).
With the other image (`e27m_ident`, Eighth target, `GeneratedAxisGlobalIdentE27`) this closes Eighth
root 27 through goctad's wrapper `generatedAxisGlobalTwelveEighthBind_root27` (explicit identifications only). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e27x_pair : pairTriGZT 32 64 true e27VH e27xVW e27XH e27xXW e27EH e27xEW = 128 := by
  rw [pairTriGZT_parts e27x_octOk e27x_partM e27x_partP e27x_partO e27x_partA e27x_partB e27x_partC,
    show e27xVW.sden = 1 / 8 from rfl, show e27VH.sden = 1 / 32 from e8SrcVecS_sden, e27x_EH, e27x_EW]
  norm_num

/-- Positive triality: `sExtra (h v₈) = W v` (E27+, Fourth target). -/
theorem e27x_ident : sExtra (rhoLocal (identWordLocal e27H) (generatedAxisGlobalTwelveRepresentative 7)) =
    rhoLocal (identWordLocal e27xW) (generatedAxisGlobalTwelveRepresentative 3) :=
  ident_forward_GZT 7 3 _ _ e27VH e27xVW e27VH_ok e27xVW_ok e27VH_ten e27xVW_ten e27XH_bnd (by norm_num)
    e27VH_actual e27xVW_actual e27x_pair

/-- Eighth root 27: both triality images at its representative coset lie in the union of the twelve
local orbits (explicit identifications). -/
theorem e27_root : GeneratedAxisGlobalTwelveEighthRootBound 27 :=
  generatedAxisGlobalTwelveEighthBind_root27
    ⟨3, identWordLocal e27xW, by rw [e27_coset]; exact e27x_ident⟩
    ⟨7, identWordLocal e27M, by rw [e27_coset]; exact e27m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
