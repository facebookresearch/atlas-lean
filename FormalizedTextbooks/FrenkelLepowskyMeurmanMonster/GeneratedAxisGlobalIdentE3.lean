/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE3MA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE3MB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots

/-! # Dense identifications E3-: Eighth root 3

`h` = the representative coset of Eighth root 3; the triality images of `h v₈` (`v₈` the Eighth
representative) are identified with H-images of `v₈` (exact packed pairings `128`, dense vectors with
43676 short terms, `pairTriGZT`).  Result: `e3m_ident` and the conditional `e3_root_of_pos`, through goctad's wrapper
`generatedAxisGlobalTwelveEighthBind_root3`; explicit identifications only. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing of the inverse triality image of `h v₈` with `M v₈` is `128`. -/
theorem e3m_pair : pairTriGZT 32 64 false e3VH e3VM e3XH e3XM e3EH e3EM = 128 := by
  rw [pairTriGZT_parts e3m_octOk e3m_partM e3m_partP e3m_partO e3m_partA
    e3m_partB e3m_partC, show e3VM.sden = 1 / 32 from e8SrcVecS_sden,
    show e3VH.sden = 1 / 32 from e8SrcVecS_sden, e3m_EH, e3m_EM]
  norm_num

/-- Inverse triality: `sExtra⁻¹ (h v₈) = M v₈` (E3-). -/
theorem e3m_ident :
    sExtra.symm (rhoLocal (identWordLocal e3H) (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal e3M) (generatedAxisGlobalTwelveRepresentative 7) :=
  ident_inverse_GZT 7 7 _ _ e3VH e3VM e3VH_ok e3VM_ok e3VH_ten e3VM_ten e3XH_bnd (by norm_num)
    e3VH_actual e3VM_actual e3m_pair

/-- The representative coset of Eighth root 3 is the word `h`. -/
theorem e3_coset : generatedAxisGlobalTwelveEighthBindCoset3 = identWordLocal e3H := rfl

/-- Eighth root 3 from the positive image (CONDITIONAL on `hpos`; the inverse image is `e3m_ident`). -/
theorem e3_root_of_pos (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset3 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 3 :=
  generatedAxisGlobalTwelveEighthBind_root3
    hpos
    ⟨7, identWordLocal e3M, by rw [e3_coset]; exact e3m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
