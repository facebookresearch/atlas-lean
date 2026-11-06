/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE15MA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE15MB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots

/-! # Dense identifications E15-: Eighth root 15

`h` = the representative coset of Eighth root 15; the triality images of `h v₈` (`v₈` the Eighth
representative) are identified with H-images of `v₈` (exact packed pairings `128`, dense vectors with
43676 short terms, `pairTriGZT`).  Result: `e15m_ident` and the conditional `e15_root_of_pos`, through goctad's wrapper
`generatedAxisGlobalTwelveEighthBind_root15`; explicit identifications only. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing of the inverse triality image of `h v₈` with `M v₈` is `128`. -/
theorem e15m_pair : pairTriGZT 32 64 false e15VH e15VM e15XH e15XM e15EH e15EM = 128 := by
  rw [pairTriGZT_parts e15m_octOk e15m_partM e15m_partP e15m_partO e15m_partA
    e15m_partB e15m_partC, show e15VM.sden = 1 / 32 from e8SrcVecS_sden,
    show e15VH.sden = 1 / 32 from e8SrcVecS_sden, e15m_EH, e15m_EM]
  norm_num

/-- Inverse triality: `sExtra⁻¹ (h v₈) = M v₈` (E15-). -/
theorem e15m_ident :
    sExtra.symm (rhoLocal (identWordLocal e15H) (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal e15M) (generatedAxisGlobalTwelveRepresentative 7) :=
  ident_inverse_GZT 7 7 _ _ e15VH e15VM e15VH_ok e15VM_ok e15VH_ten e15VM_ten e15XH_bnd (by norm_num)
    e15VH_actual e15VM_actual e15m_pair

/-- The representative coset of Eighth root 15 is the word `h`. -/
theorem e15_coset : generatedAxisGlobalTwelveEighthBindCoset15 = identWordLocal e15H := rfl

/-- Eighth root 15 from the positive image (CONDITIONAL on `hpos`; the inverse image is `e15m_ident`). -/
theorem e15_root_of_pos (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset15 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 15 :=
  generatedAxisGlobalTwelveEighthBind_root15
    hpos
    ⟨7, identWordLocal e15M, by rw [e15_coset]; exact e15m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
