/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE23pA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE23pB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Dense identification E23+: the Tenth image at Eighth root 23

`h` = the representative coset of Eighth root 23 (`e23H`); the positive triality image of
`h v₈` is identified with an H-image of the Tenth representative (exact packed pairing `128`, `pairTriGZT`).
The root lemma `e23p_root_of_neg` is conditional on the other image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e23p_pair : pairTriGZT 64 64 true e23VH e23pVW e23XH e23pXW e23EH e23pEW = 128 := by
  rw [pairTriGZT_parts e23p_octOk e23p_partM e23p_partP e23p_partO e23p_partA e23p_partB e23p_partC,
    show e23pVW.sden = (1 / 128) from rfl, show e23VH.sden = 1 / 32 from e8SrcVecS_sden, e23p_EH, e23p_EW]
  norm_num

/-- Positive triality: `sExtra (h v₈) = W v` (E23+, Tenth target). -/
theorem e23p_ident : sExtra (rhoLocal (identWordLocal e23H) (generatedAxisGlobalTwelveRepresentative 7)) =
    rhoLocal (identWordLocal e23pW) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_forward_GZT 7 11 _ _ e23VH e23pVW e23VH_ok e23pVW_ok e23VH_ten e23pVW_ten e23XH_bnd (by norm_num)
    e23VH_actual e23pVW_actual e23p_pair

/-- The representative coset of Eighth root 23 is the word `h`. -/
theorem e23p_coset : generatedAxisGlobalTwelveEighthBindCoset23 = identWordLocal e23H := rfl

/-- Eighth root 23 from the other image (CONDITIONAL on it; this image is `e23p_ident`). -/
theorem e23p_root_of_neg (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset23 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 23 :=
  generatedAxisGlobalTwelveEighthBind_root23
    ⟨11, identWordLocal e23pW, by rw [e23p_coset]; exact e23p_ident⟩
    hneg

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
