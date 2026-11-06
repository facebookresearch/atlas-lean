/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE17pA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE17pB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification E17+: the Twelfth image at Eighth root 17

`h` = the representative coset of Eighth root 17 (`e17H`); the positive triality image of
`h v₈` is identified with an H-image of the Twelfth representative (exact packed pairing `128`, `pairTriGZT`).
The root lemma `e17p_root_of_neg` is conditional on the other image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e17p_pair : pairTriGZT 32 64 true e17VH e17pVW e17XH e17pXW e17EH e17pEW = 128 := by
  rw [pairTriGZT_parts e17p_octOk e17p_partM e17p_partP e17p_partO e17p_partA e17p_partB e17p_partC,
    show e17pVW.sden = (1 / 128) from rfl, show e17VH.sden = 1 / 32 from e8SrcVecS_sden, e17p_EH, e17p_EW]
  norm_num

/-- Positive triality: `sExtra (h v₈) = W v` (E17+, Twelfth target). -/
theorem e17p_ident : sExtra (rhoLocal (identWordLocal e17H) (generatedAxisGlobalTwelveRepresentative 7)) =
    rhoLocal (identWordLocal e17pW) (generatedAxisGlobalTwelveRepresentative 10) :=
  ident_forward_GZT 7 10 _ _ e17VH e17pVW e17VH_ok e17pVW_ok e17VH_ten e17pVW_ten e17XH_bnd (by norm_num)
    e17VH_actual e17pVW_actual e17p_pair

/-- The representative coset of Eighth root 17 is the word `h`. -/
theorem e17p_coset : generatedAxisGlobalTwelveEighthBindCoset17 = identWordLocal e17H := rfl

/-- Eighth root 17 from the other image (CONDITIONAL on it; this image is `e17p_ident`). -/
theorem e17p_root_of_neg (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset17 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 17 :=
  generatedAxisGlobalTwelveEighthBind_root17
    ⟨10, identWordLocal e17pW, by rw [e17p_coset]; exact e17p_ident⟩
    hneg

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
