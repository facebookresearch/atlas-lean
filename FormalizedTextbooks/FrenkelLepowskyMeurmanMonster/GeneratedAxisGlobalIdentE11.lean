/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE11PA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE11PB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots

/-! # Dense identifications E11+: Eighth root 11

`h` = the representative coset of Eighth root 11; the triality images of `h v₈` (`v₈` the Eighth
representative) are identified with H-images of `v₈` (exact packed pairings `128`, dense vectors with
43676 short terms, `pairTriGZT`).  Result: `e11p_ident` and the conditional `e11_root_of_neg`, through goctad's wrapper
`generatedAxisGlobalTwelveEighthBind_root11`; explicit identifications only. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing of the positive triality image of `h v₈` with `P v₈` is `128`. -/
theorem e11p_pair : pairTriGZT 32 64 true e11VH e11VP e11XH e11XP e11EH e11EP = 128 := by
  rw [pairTriGZT_parts e11p_octOk e11p_partM e11p_partP e11p_partO e11p_partA
    e11p_partB e11p_partC, show e11VP.sden = 1 / 32 from e8SrcVecS_sden,
    show e11VH.sden = 1 / 32 from e8SrcVecS_sden, e11p_EH, e11p_EP]
  norm_num

/-- Positive triality: `sExtra (h v₈) = P v₈` (E11+). -/
theorem e11p_ident : sExtra (rhoLocal (identWordLocal e11H) (generatedAxisGlobalTwelveRepresentative 7)) =
    rhoLocal (identWordLocal e11P) (generatedAxisGlobalTwelveRepresentative 7) :=
  ident_forward_GZT 7 7 _ _ e11VH e11VP e11VH_ok e11VP_ok e11VH_ten e11VP_ten e11XH_bnd (by norm_num)
    e11VH_actual e11VP_actual e11p_pair

/-- The representative coset of Eighth root 11 is the word `h`. -/
theorem e11_coset : generatedAxisGlobalTwelveEighthBindCoset11 = identWordLocal e11H := rfl

/-- Eighth root 11 from the inverse image (CONDITIONAL on `hneg`; the positive image is `e11p_ident`). -/
theorem e11_root_of_neg (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset11 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 11 :=
  generatedAxisGlobalTwelveEighthBind_root11
    ⟨7, identWordLocal e11P, by rw [e11_coset]; exact e11p_ident⟩
    hneg

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
