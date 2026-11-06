/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2FamilyTransitions

/-! The genuine root-line stabilizer is transitive on all original neighboring short labels. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Composition of genuine root-line short-label transporters. -/
theorem leechRootedA2_transporter_compose (r s t : GriessShortIndex)
    (e f : leechIsomSubgroup) (he : leechRootedA2PreservesRootLine e)
    (hf : leechRootedA2PreservesRootLine f) (hre : griessShortPermutation e r = s)
    (hsf : griessShortPermutation f s = t) :
    ∃ g : leechIsomSubgroup, leechRootedA2PreservesRootLine g ∧
      griessShortPermutation g r = t := by
  refine ⟨f * e, leechRootedA2PreservesRootLine_mul f e hf he, ?_⟩
  rw [map_mul, Equiv.Perm.mul_apply, hre, hsf]

/-- The inverse of a genuine root-line transporter returns its target. -/
theorem leechRootedA2_transporter_inverse (r s : GriessShortIndex)
    (e : leechIsomSubgroup) (he : leechRootedA2PreservesRootLine e)
    (hre : griessShortPermutation e r = s) :
    leechRootedA2PreservesRootLine e⁻¹ ∧ griessShortPermutation e⁻¹ s = r := by
  refine ⟨leechRootedA2PreservesRootLine_inv e he, ?_⟩
  rw [← hre, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

/-- All genuine neighboring labels reach one actual pair-family anchor. -/
theorem leechRootedA2Neighbor_common_anchor :
    ∃ a : leechRootedA2NeighborAddress, ∀ r : leechRootedA2NeighborAddress,
      ∃ e : leechIsomSubgroup, leechRootedA2PreservesRootLine e ∧
        griessShortPermutation e r.val = a.val := by
  obtain ⟨a0, a1, e, he, hea, ha0, ha1⟩ := leechRootedA2_pair_octad_transition
  obtain ⟨b1, b2, f, hf, hfb, hb1, hb2⟩ := leechRootedA2_octad_odd_transition
  obtain ⟨m, _, hm, hmb⟩ := leechRootedA2Neighbor_same_family_transitive b1 a1
    (hb1.trans ha1.symm)
  have hei := leechRootedA2_transporter_inverse _ _ e he hea
  have hfi := leechRootedA2_transporter_inverse _ _ f hf hfb
  obtain ⟨n, hn, hnb⟩ := leechRootedA2_transporter_compose b2.val b1.val a1.val
    f⁻¹ m hfi.1 hm hfi.2 hmb
  obtain ⟨q, hq, hqb⟩ := leechRootedA2_transporter_compose b2.val a1.val a0.val
    n e⁻¹ hn hei.1 hnb hei.2
  refine ⟨a0, ?_⟩
  intro r
  have htags : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide +kernel
  rcases htags (leechRootedA2NeighborFamily r.val) with hr | hr | hr
  · obtain ⟨g, _, hg, hgr⟩ := leechRootedA2Neighbor_same_family_transitive r a0
      (hr.trans ha0.symm)
    exact ⟨g, hg, hgr⟩
  · obtain ⟨g, _, hg, hgr⟩ := leechRootedA2Neighbor_same_family_transitive r a1
      (hr.trans ha1.symm)
    exact leechRootedA2_transporter_compose r.val a1.val a0.val g e⁻¹ hg hei.1 hgr hei.2
  · obtain ⟨g, _, hg, hgr⟩ := leechRootedA2Neighbor_same_family_transitive r b2
      (hr.trans hb2.symm)
    exact leechRootedA2_transporter_compose r.val b2.val a0.val g q hg hq hgr hqb

/-- The actual root-line stabilizer acts transitively on all4600 neighboring short labels. -/
theorem leechRootedA2Neighbor_transitive (r s : leechRootedA2NeighborAddress) :
    ∃ e : leechIsomSubgroup, leechRootedA2PreservesRootLine e ∧
      griessShortPermutation e r.val = s.val := by
  obtain ⟨a, ha⟩ := leechRootedA2Neighbor_common_anchor
  obtain ⟨e, he, her⟩ := ha r
  obtain ⟨f, hf, hfs⟩ := ha s
  have hfi := leechRootedA2_transporter_inverse _ _ f hf hfs
  exact leechRootedA2_transporter_compose r.val a.val s.val e f⁻¹ he hfi.1 her hfi.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
