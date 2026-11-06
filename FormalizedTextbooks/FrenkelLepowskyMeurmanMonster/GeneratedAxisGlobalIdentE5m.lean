/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE5mA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE5mB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification E5-: the Twelfth image at Eighth root 5

`h` = the representative coset of Eighth root 5 (`e5H`); the inverse triality image of
`h v₈` is identified with an H-image of the Twelfth representative (exact packed pairing `128`, `pairTriGZT`).
The root lemma `e5m_root_of_pos` is conditional on the other image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e5m_pair : pairTriGZT 32 64 false e5VH e5mVW e5XH e5mXW e5EH e5mEW = 128 := by
  rw [pairTriGZT_parts e5m_octOk e5m_partM e5m_partP e5m_partO e5m_partA e5m_partB e5m_partC,
    show e5mVW.sden = (1 / 128) from rfl, show e5VH.sden = 1 / 32 from e8SrcVecS_sden, e5m_EH, e5m_EW]
  norm_num

/-- Inverse triality: `sExtra⁻¹ (h v₈) = W v` (E5-, Twelfth target). -/
theorem e5m_ident :
    sExtra.symm (rhoLocal (identWordLocal e5H) (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal e5mW) (generatedAxisGlobalTwelveRepresentative 10) :=
  ident_inverse_GZT 7 10 _ _ e5VH e5mVW e5VH_ok e5mVW_ok e5VH_ten e5mVW_ten e5XH_bnd (by norm_num)
    e5VH_actual e5mVW_actual e5m_pair

/-- The representative coset of Eighth root 5 is the word `h`. -/
theorem e5m_coset : generatedAxisGlobalTwelveEighthBindCoset5 = identWordLocal e5H := rfl

/-- Eighth root 5 from the other image (CONDITIONAL on it; this image is `e5m_ident`). -/
theorem e5m_root_of_pos (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset5 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 5 :=
  generatedAxisGlobalTwelveEighthBind_root5
    hpos
    ⟨10, identWordLocal e5mW, by rw [e5m_coset]; exact e5m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
