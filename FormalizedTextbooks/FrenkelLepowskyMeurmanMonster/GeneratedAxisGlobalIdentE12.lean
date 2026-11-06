/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE12PA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE12PB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots

/-! # Dense identifications E12+: Eighth root 12

`h` = the representative coset of Eighth root 12; the triality images of `h v₈` (`v₈` the Eighth
representative) are identified with H-images of `v₈` (exact packed pairings `128`, dense vectors with
43676 short terms, `pairTriGZT`).  Result: `e12p_ident` and the conditional `e12_root_of_neg`, through goctad's wrapper
`generatedAxisGlobalTwelveEighthBind_root12`; explicit identifications only. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing of the positive triality image of `h v₈` with `P v₈` is `128`. -/
theorem e12p_pair : pairTriGZT 32 64 true e12VH e12VP e12XH e12XP e12EH e12EP = 128 := by
  rw [pairTriGZT_parts e12p_octOk e12p_partM e12p_partP e12p_partO e12p_partA
    e12p_partB e12p_partC, show e12VP.sden = 1 / 32 from e8SrcVecS_sden,
    show e12VH.sden = 1 / 32 from e8SrcVecS_sden, e12p_EH, e12p_EP]
  norm_num

/-- Positive triality: `sExtra (h v₈) = P v₈` (E12+). -/
theorem e12p_ident : sExtra (rhoLocal (identWordLocal e12H) (generatedAxisGlobalTwelveRepresentative 7)) =
    rhoLocal (identWordLocal e12P) (generatedAxisGlobalTwelveRepresentative 7) :=
  ident_forward_GZT 7 7 _ _ e12VH e12VP e12VH_ok e12VP_ok e12VH_ten e12VP_ten e12XH_bnd (by norm_num)
    e12VH_actual e12VP_actual e12p_pair

/-- The representative coset of Eighth root 12 is the word `h`. -/
theorem e12_coset : generatedAxisGlobalTwelveEighthBindCoset12 = identWordLocal e12H := rfl

/-- Eighth root 12 from the inverse image (CONDITIONAL on `hneg`; the positive image is `e12p_ident`). -/
theorem e12_root_of_neg (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset12 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 12 :=
  generatedAxisGlobalTwelveEighthBind_root12
    ⟨7, identWordLocal e12P, by rw [e12_coset]; exact e12p_ident⟩
    hneg

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
