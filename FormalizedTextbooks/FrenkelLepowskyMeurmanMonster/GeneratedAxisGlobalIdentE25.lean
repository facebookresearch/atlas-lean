/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE25PA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE25PB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots

/-! # Dense identifications E25+: Eighth root 25

`h` = the representative coset of Eighth root 25; the triality images of `h v₈` (`v₈` the Eighth
representative) are identified with H-images of `v₈` (exact packed pairings `128`, dense vectors with
43676 short terms, `pairTriGZT`).  Result: `e25p_ident` and the conditional `e25_root_of_neg`, through goctad's wrapper
`generatedAxisGlobalTwelveEighthBind_root25`; explicit identifications only. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing of the positive triality image of `h v₈` with `P v₈` is `128`. -/
theorem e25p_pair : pairTriGZT 32 64 true e25VH e25VP e25XH e25XP e25EH e25EP = 128 := by
  rw [pairTriGZT_parts e25p_octOk e25p_partM e25p_partP e25p_partO e25p_partA
    e25p_partB e25p_partC, show e25VP.sden = 1 / 32 from e8SrcVecS_sden,
    show e25VH.sden = 1 / 32 from e8SrcVecS_sden, e25p_EH, e25p_EP]
  norm_num

/-- Positive triality: `sExtra (h v₈) = P v₈` (E25+). -/
theorem e25p_ident : sExtra (rhoLocal (identWordLocal e25H) (generatedAxisGlobalTwelveRepresentative 7)) =
    rhoLocal (identWordLocal e25P) (generatedAxisGlobalTwelveRepresentative 7) :=
  ident_forward_GZT 7 7 _ _ e25VH e25VP e25VH_ok e25VP_ok e25VH_ten e25VP_ten e25XH_bnd (by norm_num)
    e25VH_actual e25VP_actual e25p_pair

/-- The representative coset of Eighth root 25 is the word `h`. -/
theorem e25_coset : generatedAxisGlobalTwelveEighthBindCoset25 = identWordLocal e25H := rfl

/-- Eighth root 25 from the inverse image (CONDITIONAL on `hneg`; the positive image is `e25p_ident`). -/
theorem e25_root_of_neg (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset25 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 25 :=
  generatedAxisGlobalTwelveEighthBind_root25
    ⟨7, identWordLocal e25P, by rw [e25_coset]; exact e25p_ident⟩
    hneg

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
