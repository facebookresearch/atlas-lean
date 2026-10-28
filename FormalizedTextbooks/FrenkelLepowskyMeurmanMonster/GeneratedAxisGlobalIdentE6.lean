/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE6PA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE6PB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE6MA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE6MB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots

/-! # Dense identifications E6+, E6-: Eighth root 6

`h` = the representative coset of Eighth root 6; the triality images of `h v₈` (`v₈` the Eighth
representative) are identified with H-images of `v₈` (exact packed pairings `128`, dense vectors with
43676 short terms, `pairTriGZT`).  Result: `e6_root : GeneratedAxisGlobalTwelveEighthRootBound 6`, through goctad's wrapper
`generatedAxisGlobalTwelveEighthBind_root6`; explicit identifications only. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing of the positive triality image of `h v₈` with `P v₈` is `128`. -/
theorem e6p_pair : pairTriGZT 32 64 true e6VH e6VP e6XH e6XP e6EH e6EP = 128 := by
  rw [pairTriGZT_parts e6p_octOk e6p_partM e6p_partP e6p_partO e6p_partA
    e6p_partB e6p_partC, show e6VP.sden = 1 / 32 from e8SrcVecS_sden,
    show e6VH.sden = 1 / 32 from e8SrcVecS_sden, e6p_EH, e6p_EP]
  norm_num

/-- Positive triality: `sExtra (h v₈) = P v₈` (E6+). -/
theorem e6p_ident : sExtra (rhoLocal (identWordLocal e6H) (generatedAxisGlobalTwelveRepresentative 7)) =
    rhoLocal (identWordLocal e6P) (generatedAxisGlobalTwelveRepresentative 7) :=
  ident_forward_GZT 7 7 _ _ e6VH e6VP e6VH_ok e6VP_ok e6VH_ten e6VP_ten e6XH_bnd (by norm_num)
    e6VH_actual e6VP_actual e6p_pair

/-- The exact pairing of the inverse triality image of `h v₈` with `M v₈` is `128`. -/
theorem e6m_pair : pairTriGZT 32 64 false e6VH e6VM e6XH e6XM e6EH e6EM = 128 := by
  rw [pairTriGZT_parts e6m_octOk e6m_partM e6m_partP e6m_partO e6m_partA
    e6m_partB e6m_partC, show e6VM.sden = 1 / 32 from e8SrcVecS_sden,
    show e6VH.sden = 1 / 32 from e8SrcVecS_sden, e6m_EH, e6m_EM]
  norm_num

/-- Inverse triality: `sExtra⁻¹ (h v₈) = M v₈` (E6-). -/
theorem e6m_ident :
    sExtra.symm (rhoLocal (identWordLocal e6H) (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal e6M) (generatedAxisGlobalTwelveRepresentative 7) :=
  ident_inverse_GZT 7 7 _ _ e6VH e6VM e6VH_ok e6VM_ok e6VH_ten e6VM_ten e6XH_bnd (by norm_num)
    e6VH_actual e6VM_actual e6m_pair

/-- The representative coset of Eighth root 6 is the word `h`. -/
theorem e6_coset : generatedAxisGlobalTwelveEighthBindCoset6 = identWordLocal e6H := rfl

/-- Eighth root 6: both triality images at its representative coset lie in the union of the
twelve local orbits (explicit identifications with H-images of the Eighth representative). -/
theorem e6_root : GeneratedAxisGlobalTwelveEighthRootBound 6 :=
  generatedAxisGlobalTwelveEighthBind_root6
    ⟨7, identWordLocal e6P, by rw [e6_coset]; exact e6p_ident⟩
    ⟨7, identWordLocal e6M, by rw [e6_coset]; exact e6m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
