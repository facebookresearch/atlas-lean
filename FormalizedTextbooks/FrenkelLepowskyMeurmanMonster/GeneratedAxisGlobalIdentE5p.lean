/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE5pA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE5pB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification E5+: the Twelfth image at Eighth root 5

`h` = the representative coset of Eighth root 5 (`e5H`); the positive triality image of
`h v₈` is identified with an H-image of the Twelfth representative (exact packed pairing `128`, `pairTriGZT`).
The root lemma `e5p_root_of_neg` is conditional on the other image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false

/-- The exact pairing is `128`. -/
theorem e5p_pair : pairTriGZT 32 64 true e5VH e5pVW e5XH e5pXW e5EH e5pEW = 128 := by
  rw [pairTriGZT_parts e5p_octOk e5p_partM e5p_partP e5p_partO e5p_partA e5p_partB e5p_partC,
    show e5pVW.sden = (1 / 128) from rfl, show e5VH.sden = 1 / 32 from e8SrcVecS_sden, e5p_EH, e5p_EW]
  norm_num

/-- Positive triality: `sExtra (h v₈) = W v` (E5+, Twelfth target). -/
theorem e5p_ident : sExtra (rhoLocal (identWordLocal e5H) (generatedAxisGlobalTwelveRepresentative 7)) =
    rhoLocal (identWordLocal e5pW) (generatedAxisGlobalTwelveRepresentative 10) :=
  ident_forward_GZT 7 10 _ _ e5VH e5pVW e5VH_ok e5pVW_ok e5VH_ten e5pVW_ten e5XH_bnd (by norm_num)
    e5VH_actual e5pVW_actual e5p_pair

/-- The representative coset of Eighth root 5 is the word `h`. -/
theorem e5p_coset : generatedAxisGlobalTwelveEighthBindCoset5 = identWordLocal e5H := rfl

/-- Eighth root 5 from the other image (CONDITIONAL on it; this image is `e5p_ident`). -/
theorem e5p_root_of_neg (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset5 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 5 :=
  generatedAxisGlobalTwelveEighthBind_root5
    ⟨10, identWordLocal e5pW, by rw [e5p_coset]; exact e5p_ident⟩
    hneg

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
