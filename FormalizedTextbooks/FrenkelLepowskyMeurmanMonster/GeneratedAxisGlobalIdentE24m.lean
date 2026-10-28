/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE24mA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE24mB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh

/-! # Dense identification E24-: the Seventh image at Eighth root 24

`h` = the representative coset of Eighth root 24 (`e24H`); the inverse triality image of
`h v₈` is identified with an H-image of the Seventh representative (exact packed pairing `128`, `pairTriGZT`).
The root lemma `e24m_root_of_pos` is conditional on the other image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e24m_pair : pairTriGZT 32 64 false e24VH e24mVW e24XH e24mXW e24EH e24mEW = 128 := by
  rw [pairTriGZT_parts e24m_octOk e24m_partM e24m_partP e24m_partO e24m_partA e24m_partB e24m_partC,
    show e24mVW.sden = (1 / 32) from rfl, show e24VH.sden = 1 / 32 from e8SrcVecS_sden, e24m_EH, e24m_EW]
  norm_num

/-- Inverse triality: `sExtra⁻¹ (h v₈) = W v` (E24-, Seventh target). -/
theorem e24m_ident :
    sExtra.symm (rhoLocal (identWordLocal e24H) (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal e24mW) (generatedAxisGlobalTwelveRepresentative 6) :=
  ident_inverse_GZT 7 6 _ _ e24VH e24mVW e24VH_ok e24mVW_ok e24VH_ten e24mVW_ten e24XH_bnd (by norm_num)
    e24VH_actual e24mVW_actual e24m_pair

/-- The representative coset of Eighth root 24 is the word `h`. -/
theorem e24m_coset : generatedAxisGlobalTwelveEighthBindCoset24 = identWordLocal e24H := rfl

/-- Eighth root 24 from the other image (CONDITIONAL on it; this image is `e24m_ident`). -/
theorem e24m_root_of_pos (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset24 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 24 :=
  generatedAxisGlobalTwelveEighthBind_root24
    hpos
    ⟨6, identWordLocal e24mW, by rw [e24m_coset]; exact e24m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
