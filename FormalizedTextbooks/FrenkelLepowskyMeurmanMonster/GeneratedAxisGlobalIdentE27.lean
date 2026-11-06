/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE27MA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE27MB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots

/-! # Dense identifications E27-: Eighth root 27

`h` = the representative coset of Eighth root 27; the triality images of `h v₈` (`v₈` the Eighth
representative) are identified with H-images of `v₈` (exact packed pairings `128`, dense vectors with
43676 short terms, `pairTriGZT`).  Result: `e27m_ident` and the conditional `e27_root_of_pos`, through goctad's wrapper
`generatedAxisGlobalTwelveEighthBind_root27`; explicit identifications only. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing of the inverse triality image of `h v₈` with `M v₈` is `128`. -/
theorem e27m_pair : pairTriGZT 32 64 false e27VH e27VM e27XH e27XM e27EH e27EM = 128 := by
  rw [pairTriGZT_parts e27m_octOk e27m_partM e27m_partP e27m_partO e27m_partA
    e27m_partB e27m_partC, show e27VM.sden = 1 / 32 from e8SrcVecS_sden,
    show e27VH.sden = 1 / 32 from e8SrcVecS_sden, e27m_EH, e27m_EM]
  norm_num

/-- Inverse triality: `sExtra⁻¹ (h v₈) = M v₈` (E27-). -/
theorem e27m_ident :
    sExtra.symm (rhoLocal (identWordLocal e27H) (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal e27M) (generatedAxisGlobalTwelveRepresentative 7) :=
  ident_inverse_GZT 7 7 _ _ e27VH e27VM e27VH_ok e27VM_ok e27VH_ten e27VM_ten e27XH_bnd (by norm_num)
    e27VH_actual e27VM_actual e27m_pair

/-- The representative coset of Eighth root 27 is the word `h`. -/
theorem e27_coset : generatedAxisGlobalTwelveEighthBindCoset27 = identWordLocal e27H := rfl

/-- Eighth root 27 from the positive image (CONDITIONAL on `hpos`; the inverse image is `e27m_ident`). -/
theorem e27_root_of_pos (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset27 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 27 :=
  generatedAxisGlobalTwelveEighthBind_root27
    hpos
    ⟨7, identWordLocal e27M, by rw [e27_coset]; exact e27m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
