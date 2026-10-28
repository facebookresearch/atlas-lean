/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE23mA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE23mB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification E23-: the Root8 image at Eighth root 23

`h` = the representative coset of Eighth root 23 (`e23H`); the inverse triality image of
`h v₈` is identified with an H-image of the Root8 representative (exact packed pairing `128`, `pairTriGZT`).
The root lemma `e23m_root_of_pos` is conditional on the other image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e23m_pair : pairTriGZT 64 64 false e23VH e23mVW e23XH e23mXW e23EH e23mEW = 128 := by
  rw [pairTriGZT_parts e23m_octOk e23m_partM e23m_partP e23m_partO e23m_partA e23m_partB e23m_partC,
    show e23mVW.sden = (1 / 128) from rfl, show e23VH.sden = 1 / 32 from e8SrcVecS_sden, e23m_EH, e23m_EW]
  norm_num

/-- Inverse triality: `sExtra⁻¹ (h v₈) = W v` (E23-, Root8 target). -/
theorem e23m_ident :
    sExtra.symm (rhoLocal (identWordLocal e23H) (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal e23mW) (generatedAxisGlobalTwelveRepresentative 9) :=
  ident_inverse_GZT 7 9 _ _ e23VH e23mVW e23VH_ok e23mVW_ok e23VH_ten e23mVW_ten e23XH_bnd (by norm_num)
    e23VH_actual e23mVW_actual e23m_pair

/-- The representative coset of Eighth root 23 is the word `h`. -/
theorem e23m_coset : generatedAxisGlobalTwelveEighthBindCoset23 = identWordLocal e23H := rfl

/-- Eighth root 23 from the other image (CONDITIONAL on it; this image is `e23m_ident`). -/
theorem e23m_root_of_pos (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset23 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 23 :=
  generatedAxisGlobalTwelveEighthBind_root23
    hpos
    ⟨9, identWordLocal e23mW, by rw [e23m_coset]; exact e23m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
