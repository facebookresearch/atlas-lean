/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE29pA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE29pB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification E29+: the Twelfth image at Eighth root 29

`h` = the representative coset of Eighth root 29 (`e29H`); the positive triality image of
`h v₈` is identified with an H-image of the Twelfth representative (exact packed pairing `128`, `pairTriGZT`).
The root lemma `e29p_root_of_neg` is conditional on the other image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e29p_pair : pairTriGZT 32 64 true e29VH e29pVW e29XH e29pXW e29EH e29pEW = 128 := by
  rw [pairTriGZT_parts e29p_octOk e29p_partM e29p_partP e29p_partO e29p_partA e29p_partB e29p_partC,
    show e29pVW.sden = (1 / 128) from rfl, show e29VH.sden = 1 / 32 from e8SrcVecS_sden, e29p_EH, e29p_EW]
  norm_num

/-- Positive triality: `sExtra (h v₈) = W v` (E29+, Twelfth target). -/
theorem e29p_ident : sExtra (rhoLocal (identWordLocal e29H) (generatedAxisGlobalTwelveRepresentative 7)) =
    rhoLocal (identWordLocal e29pW) (generatedAxisGlobalTwelveRepresentative 10) :=
  ident_forward_GZT 7 10 _ _ e29VH e29pVW e29VH_ok e29pVW_ok e29VH_ten e29pVW_ten e29XH_bnd (by norm_num)
    e29VH_actual e29pVW_actual e29p_pair

/-- The representative coset of Eighth root 29 is the word `h`. -/
theorem e29p_coset : generatedAxisGlobalTwelveEighthBindCoset29 = identWordLocal e29H := rfl

/-- Eighth root 29 from the other image (CONDITIONAL on it; this image is `e29p_ident`). -/
theorem e29p_root_of_neg (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset29 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 29 :=
  generatedAxisGlobalTwelveEighthBind_root29
    ⟨10, identWordLocal e29pW, by rw [e29p_coset]; exact e29p_ident⟩
    hneg

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
