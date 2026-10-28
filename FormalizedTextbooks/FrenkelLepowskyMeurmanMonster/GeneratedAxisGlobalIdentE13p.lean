/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE13pA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE13pB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Dense identification E13+: the Tenth image at Eighth root 13

`h` = the representative coset of Eighth root 13 (`e13H`); the positive triality image of
`h v₈` is identified with an H-image of the Tenth representative (exact packed pairing `128`, `pairTriGZT`).
The root lemma `e13p_root_of_neg` is conditional on the other image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e13p_pair : pairTriGZT 64 64 true e13VH e13pVW e13XH e13pXW e13EH e13pEW = 128 := by
  rw [pairTriGZT_parts e13p_octOk e13p_partM e13p_partP e13p_partO e13p_partA e13p_partB e13p_partC,
    show e13pVW.sden = (1 / 128) from rfl, show e13VH.sden = 1 / 32 from e8SrcVecS_sden, e13p_EH, e13p_EW]
  norm_num

/-- Positive triality: `sExtra (h v₈) = W v` (E13+, Tenth target). -/
theorem e13p_ident : sExtra (rhoLocal (identWordLocal e13H) (generatedAxisGlobalTwelveRepresentative 7)) =
    rhoLocal (identWordLocal e13pW) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_forward_GZT 7 11 _ _ e13VH e13pVW e13VH_ok e13pVW_ok e13VH_ten e13pVW_ten e13XH_bnd (by norm_num)
    e13VH_actual e13pVW_actual e13p_pair

/-- The representative coset of Eighth root 13 is the word `h`. -/
theorem e13p_coset : generatedAxisGlobalTwelveEighthBindCoset13 = identWordLocal e13H := rfl

/-- Eighth root 13 from the other image (CONDITIONAL on it; this image is `e13p_ident`). -/
theorem e13p_root_of_neg (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset13 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 13 :=
  generatedAxisGlobalTwelveEighthBind_root13
    ⟨11, identWordLocal e13pW, by rw [e13p_coset]; exact e13p_ident⟩
    hneg

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
