/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE13mA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE13mB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh

/-! # Dense identification E13-: the Seventh image at Eighth root 13

`h` = the representative coset of Eighth root 13 (`e13H`); the inverse triality image of
`h v₈` is identified with an H-image of the Seventh representative (exact packed pairing `128`, `pairTriGZT`).
The root lemma `e13m_root_of_pos` is conditional on the other image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e13m_pair : pairTriGZT 32 64 false e13VH e13mVW e13XH e13mXW e13EH e13mEW = 128 := by
  rw [pairTriGZT_parts e13m_octOk e13m_partM e13m_partP e13m_partO e13m_partA e13m_partB e13m_partC,
    show e13mVW.sden = (1 / 32) from rfl, show e13VH.sden = 1 / 32 from e8SrcVecS_sden, e13m_EH, e13m_EW]
  norm_num

/-- Inverse triality: `sExtra⁻¹ (h v₈) = W v` (E13-, Seventh target). -/
theorem e13m_ident :
    sExtra.symm (rhoLocal (identWordLocal e13H) (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal e13mW) (generatedAxisGlobalTwelveRepresentative 6) :=
  ident_inverse_GZT 7 6 _ _ e13VH e13mVW e13VH_ok e13mVW_ok e13VH_ten e13mVW_ten e13XH_bnd (by norm_num)
    e13VH_actual e13mVW_actual e13m_pair

/-- The representative coset of Eighth root 13 is the word `h`. -/
theorem e13m_coset : generatedAxisGlobalTwelveEighthBindCoset13 = identWordLocal e13H := rfl

/-- Eighth root 13 from the other image (CONDITIONAL on it; this image is `e13m_ident`). -/
theorem e13m_root_of_pos (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset13 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 13 :=
  generatedAxisGlobalTwelveEighthBind_root13
    hpos
    ⟨6, identWordLocal e13mW, by rw [e13m_coset]; exact e13m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
