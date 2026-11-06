/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE24pA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE24pB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF

/-! # Dense identification E24+: the Sixth image at Eighth root 24

`h` = the representative coset of Eighth root 24 (`e24H`); the positive triality image of
`h v₈` is identified with an H-image of the Sixth representative (exact packed pairing `128`, `pairTriGZT`).
The root lemma `e24p_root_of_neg` is conditional on the other image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e24p_pair : pairTriGZT 64 64 true e24VH e24pVW e24XH e24pXW e24EH e24pEW = 128 := by
  rw [pairTriGZT_parts e24p_octOk e24p_partM e24p_partP e24p_partO e24p_partA e24p_partB e24p_partC,
    show e24pVW.sden = 1 / 32 from rfl, show e24VH.sden = 1 / 32 from e8SrcVecS_sden, e24p_EH, e24p_EW]
  norm_num

/-- Positive triality: `sExtra (h v₈) = W v` (E24+, Sixth target). -/
theorem e24p_ident : sExtra (rhoLocal (identWordLocal e24H) (generatedAxisGlobalTwelveRepresentative 7)) =
    rhoLocal (identWordLocal e24pW) (generatedAxisGlobalTwelveRepresentative 5) :=
  ident_forward_GZT 7 5 _ _ e24VH e24pVW e24VH_ok e24pVW_ok e24VH_ten e24pVW_ten e24XH_bnd (by norm_num)
    e24VH_actual e24pVW_actual e24p_pair

/-- The representative coset of Eighth root 24 is the word `h`. -/
theorem e24p_coset : generatedAxisGlobalTwelveEighthBindCoset24 = identWordLocal e24H := rfl

/-- Eighth root 24 from the other image (CONDITIONAL on it; this image is `e24p_ident`). -/
theorem e24p_root_of_neg (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset24 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 24 :=
  generatedAxisGlobalTwelveEighthBind_root24
    ⟨5, identWordLocal e24pW, by rw [e24p_coset]; exact e24p_ident⟩
    hneg

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
