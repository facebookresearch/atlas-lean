/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE29mA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE29mB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification E29-: the Twelfth image at Eighth root 29

`h` = the representative coset of Eighth root 29 (`e29H`); the inverse triality image of
`h v₈` is identified with an H-image of the Twelfth representative (exact packed pairing `128`, `pairTriGZT`).
The root lemma `e29m_root_of_pos` is conditional on the other image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e29m_pair : pairTriGZT 32 64 false e29VH e29mVW e29XH e29mXW e29EH e29mEW = 128 := by
  rw [pairTriGZT_parts e29m_octOk e29m_partM e29m_partP e29m_partO e29m_partA e29m_partB e29m_partC,
    show e29mVW.sden = (1 / 128) from rfl, show e29VH.sden = 1 / 32 from e8SrcVecS_sden, e29m_EH, e29m_EW]
  norm_num

/-- Inverse triality: `sExtra⁻¹ (h v₈) = W v` (E29-, Twelfth target). -/
theorem e29m_ident :
    sExtra.symm (rhoLocal (identWordLocal e29H) (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal e29mW) (generatedAxisGlobalTwelveRepresentative 10) :=
  ident_inverse_GZT 7 10 _ _ e29VH e29mVW e29VH_ok e29mVW_ok e29VH_ten e29mVW_ten e29XH_bnd (by norm_num)
    e29VH_actual e29mVW_actual e29m_pair

/-- The representative coset of Eighth root 29 is the word `h`. -/
theorem e29m_coset : generatedAxisGlobalTwelveEighthBindCoset29 = identWordLocal e29H := rfl

/-- Eighth root 29 from the other image (CONDITIONAL on it; this image is `e29m_ident`). -/
theorem e29m_root_of_pos (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset29 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 29 :=
  generatedAxisGlobalTwelveEighthBind_root29
    hpos
    ⟨10, identWordLocal e29mW, by rw [e29m_coset]; exact e29m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
