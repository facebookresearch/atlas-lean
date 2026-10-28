/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE35PA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE35PB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots

/-! # Dense identifications E35+: Eighth root 35

`h` = the representative coset of Eighth root 35; the triality images of `h v₈` (`v₈` the Eighth
representative) are identified with H-images of `v₈` (exact packed pairings `128`, dense vectors with
43676 short terms, `pairTriGZT`).  Result: `e35p_ident` and the conditional `e35_root_of_neg`, through goctad's wrapper
`generatedAxisGlobalTwelveEighthBind_root35`; explicit identifications only. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing of the positive triality image of `h v₈` with `P v₈` is `128`. -/
theorem e35p_pair : pairTriGZT 32 64 true e35VH e35VP e35XH e35XP e35EH e35EP = 128 := by
  rw [pairTriGZT_parts e35p_octOk e35p_partM e35p_partP e35p_partO e35p_partA
    e35p_partB e35p_partC, show e35VP.sden = 1 / 32 from e8SrcVecS_sden,
    show e35VH.sden = 1 / 32 from e8SrcVecS_sden, e35p_EH, e35p_EP]
  norm_num

/-- Positive triality: `sExtra (h v₈) = P v₈` (E35+). -/
theorem e35p_ident : sExtra (rhoLocal (identWordLocal e35H) (generatedAxisGlobalTwelveRepresentative 7)) =
    rhoLocal (identWordLocal e35P) (generatedAxisGlobalTwelveRepresentative 7) :=
  ident_forward_GZT 7 7 _ _ e35VH e35VP e35VH_ok e35VP_ok e35VH_ten e35VP_ten e35XH_bnd (by norm_num)
    e35VH_actual e35VP_actual e35p_pair

/-- The representative coset of Eighth root 35 is the word `h`. -/
theorem e35_coset : generatedAxisGlobalTwelveEighthBindCoset35 = identWordLocal e35H := rfl

/-- Eighth root 35 from the inverse image (CONDITIONAL on `hneg`; the positive image is `e35p_ident`). -/
theorem e35_root_of_neg (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset35 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 35 :=
  generatedAxisGlobalTwelveEighthBind_root35
    ⟨7, identWordLocal e35P, by rw [e35_coset]; exact e35p_ident⟩
    hneg

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
