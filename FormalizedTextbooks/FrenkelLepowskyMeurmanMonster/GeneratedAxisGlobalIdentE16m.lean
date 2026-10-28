/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE16mA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE16mB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification E16-: the Root8 image at Eighth root 16

`h` = the representative coset of Eighth root 16 (`e16H`); the inverse triality image of
`h v₈` is identified with an H-image of the Root8 representative (exact packed pairing `128`, `pairTriGZT`).
The root lemma `e16m_root_of_pos` is conditional on the other image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e16m_pair : pairTriGZT 64 64 false e16VH e16mVW e16XH e16mXW e16EH e16mEW = 128 := by
  rw [pairTriGZT_parts e16m_octOk e16m_partM e16m_partP e16m_partO e16m_partA e16m_partB e16m_partC,
    show e16mVW.sden = (1 / 128) from rfl, show e16VH.sden = 1 / 32 from e8SrcVecS_sden, e16m_EH, e16m_EW]
  norm_num

/-- Inverse triality: `sExtra⁻¹ (h v₈) = W v` (E16-, Root8 target). -/
theorem e16m_ident :
    sExtra.symm (rhoLocal (identWordLocal e16H) (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal e16mW) (generatedAxisGlobalTwelveRepresentative 9) :=
  ident_inverse_GZT 7 9 _ _ e16VH e16mVW e16VH_ok e16mVW_ok e16VH_ten e16mVW_ten e16XH_bnd (by norm_num)
    e16VH_actual e16mVW_actual e16m_pair

/-- The representative coset of Eighth root 16 is the word `h`. -/
theorem e16m_coset : generatedAxisGlobalTwelveEighthBindCoset16 = identWordLocal e16H := rfl

/-- Eighth root 16 from the other image (CONDITIONAL on it; this image is `e16m_ident`). -/
theorem e16m_root_of_pos (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset16 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 16 :=
  generatedAxisGlobalTwelveEighthBind_root16
    hpos
    ⟨9, identWordLocal e16mW, by rw [e16m_coset]; exact e16m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
