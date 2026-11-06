/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE16pA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE16pB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification E16+: the Root8 image at Eighth root 16

`h` = the representative coset of Eighth root 16 (`e16H`); the positive triality image of
`h v₈` is identified with an H-image of the Root8 representative (exact packed pairing `128`, `pairTriGZT`).
The root lemma `e16p_root_of_neg` is conditional on the other image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e16p_pair : pairTriGZT 64 64 true e16VH e16pVW e16XH e16pXW e16EH e16pEW = 128 := by
  rw [pairTriGZT_parts e16p_octOk e16p_partM e16p_partP e16p_partO e16p_partA e16p_partB e16p_partC,
    show e16pVW.sden = (1 / 128) from rfl, show e16VH.sden = 1 / 32 from e8SrcVecS_sden, e16p_EH, e16p_EW]
  norm_num

/-- Positive triality: `sExtra (h v₈) = W v` (E16+, Root8 target). -/
theorem e16p_ident : sExtra (rhoLocal (identWordLocal e16H) (generatedAxisGlobalTwelveRepresentative 7)) =
    rhoLocal (identWordLocal e16pW) (generatedAxisGlobalTwelveRepresentative 9) :=
  ident_forward_GZT 7 9 _ _ e16VH e16pVW e16VH_ok e16pVW_ok e16VH_ten e16pVW_ten e16XH_bnd (by norm_num)
    e16VH_actual e16pVW_actual e16p_pair

/-- The representative coset of Eighth root 16 is the word `h`. -/
theorem e16p_coset : generatedAxisGlobalTwelveEighthBindCoset16 = identWordLocal e16H := rfl

/-- Eighth root 16 from the other image (CONDITIONAL on it; this image is `e16p_ident`). -/
theorem e16p_root_of_neg (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset16 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 16 :=
  generatedAxisGlobalTwelveEighthBind_root16
    ⟨9, identWordLocal e16pW, by rw [e16p_coset]; exact e16p_ident⟩
    hneg

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
