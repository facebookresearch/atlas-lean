/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE17mA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE17mB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification E17-: the Root8 image at Eighth root 17

`h` = the representative coset of Eighth root 17 (`e17H`); the inverse triality image of
`h v₈` is identified with an H-image of the Root8 representative (exact packed pairing `128`, `pairTriGZT`).
The root lemma `e17m_root_of_pos` is conditional on the other image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e17m_pair : pairTriGZT 64 64 false e17VH e17mVW e17XH e17mXW e17EH e17mEW = 128 := by
  rw [pairTriGZT_parts e17m_octOk e17m_partM e17m_partP e17m_partO e17m_partA e17m_partB e17m_partC,
    show e17mVW.sden = (1 / 128) from rfl, show e17VH.sden = 1 / 32 from e8SrcVecS_sden, e17m_EH, e17m_EW]
  norm_num

/-- Inverse triality: `sExtra⁻¹ (h v₈) = W v` (E17-, Root8 target). -/
theorem e17m_ident :
    sExtra.symm (rhoLocal (identWordLocal e17H) (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal e17mW) (generatedAxisGlobalTwelveRepresentative 9) :=
  ident_inverse_GZT 7 9 _ _ e17VH e17mVW e17VH_ok e17mVW_ok e17VH_ten e17mVW_ten e17XH_bnd (by norm_num)
    e17VH_actual e17mVW_actual e17m_pair

/-- The representative coset of Eighth root 17 is the word `h`. -/
theorem e17m_coset : generatedAxisGlobalTwelveEighthBindCoset17 = identWordLocal e17H := rfl

/-- Eighth root 17 from the other image (CONDITIONAL on it; this image is `e17m_ident`). -/
theorem e17m_root_of_pos (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset17 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 17 :=
  generatedAxisGlobalTwelveEighthBind_root17
    hpos
    ⟨9, identWordLocal e17mW, by rw [e17m_coset]; exact e17m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
