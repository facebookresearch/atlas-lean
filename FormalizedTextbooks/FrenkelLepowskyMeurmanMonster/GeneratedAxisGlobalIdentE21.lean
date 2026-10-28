/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE21MA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE21MB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots

/-! # Dense identifications E21-: Eighth root 21

`h` = the representative coset of Eighth root 21; the triality images of `h v₈` (`v₈` the Eighth
representative) are identified with H-images of `v₈` (exact packed pairings `128`, dense vectors with
43676 short terms, `pairTriGZT`).  Result: `e21m_ident` and the conditional `e21_root_of_pos`, through goctad's wrapper
`generatedAxisGlobalTwelveEighthBind_root21`; explicit identifications only. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing of the inverse triality image of `h v₈` with `M v₈` is `128`. -/
theorem e21m_pair : pairTriGZT 32 64 false e21VH e21VM e21XH e21XM e21EH e21EM = 128 := by
  rw [pairTriGZT_parts e21m_octOk e21m_partM e21m_partP e21m_partO e21m_partA
    e21m_partB e21m_partC, show e21VM.sden = 1 / 32 from e8SrcVecS_sden,
    show e21VH.sden = 1 / 32 from e8SrcVecS_sden, e21m_EH, e21m_EM]
  norm_num

/-- Inverse triality: `sExtra⁻¹ (h v₈) = M v₈` (E21-). -/
theorem e21m_ident :
    sExtra.symm (rhoLocal (identWordLocal e21H) (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal e21M) (generatedAxisGlobalTwelveRepresentative 7) :=
  ident_inverse_GZT 7 7 _ _ e21VH e21VM e21VH_ok e21VM_ok e21VH_ten e21VM_ten e21XH_bnd (by norm_num)
    e21VH_actual e21VM_actual e21m_pair

/-- The representative coset of Eighth root 21 is the word `h`. -/
theorem e21_coset : generatedAxisGlobalTwelveEighthBindCoset21 = identWordLocal e21H := rfl

/-- Eighth root 21 from the positive image (CONDITIONAL on `hpos`; the inverse image is `e21m_ident`). -/
theorem e21_root_of_pos (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset21 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 21 :=
  generatedAxisGlobalTwelveEighthBind_root21
    hpos
    ⟨7, identWordLocal e21M, by rw [e21_coset]; exact e21m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
