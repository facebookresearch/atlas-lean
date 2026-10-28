/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayDodecadStabilizer

/-! Actual simultaneous transitivity on a Golay dodecad and a coordinate outside it. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every genuine dodecad/outside-point flag is an image of the checked initial flag. -/
theorem golayDodecadFlag_reaches (d : Fin 4096) (i : Fin 24)
    (hd : d ∈ golayDodecadsOutside i) :
    ∃ p : golayAutomorphismSubgroup,
      p • (golayDodecadOrbitCodeLabel 0, (0 : Fin 24)) = (d, i) := by
  obtain ⟨q, hq⟩ := golayPointStabilizer_reaches (0 : Fin 7) i (by
    change 0 ≤ i.val
    exact Nat.zero_le _)
  let p : golayAutomorphismSubgroup := q.val
  have hp : p.val 0 = i := hq
  have hpi : p.val.symm i = 0 := p.val.symm_apply_eq.mpr hp.symm
  let d' : Fin 4096 := p⁻¹ • d
  have hd' : d' ∈ golayDodecadsOutside 0 := by
    have h := (golayLabelPermutation_dodecad_outside p⁻¹ d i).mpr hd
    change d' ∈ golayDodecadsOutside (p.val.symm i) at h
    rwa [hpi] at h
  obtain ⟨r, hr0, hr⟩ := golayDodecadsOutside_zero_reaches d' hd'
  have hrl : r • golayDodecadOrbitCodeLabel 0 = d' := by
    apply golayLabelCoefficients_injective
    apply golayEncoder_injective
    change golayEncoder (golayLabelCoefficients
      (golayLabelPermutation r (golayDodecadOrbitCodeLabel 0))) = _
    rw [golayLabelPermutation_word]
    exact hr
  refine ⟨p * r, ?_⟩
  apply Prod.ext
  · change (p * r) • golayDodecadOrbitCodeLabel 0 = d
    rw [mul_smul, hrl]
    exact smul_inv_smul p d
  · change p.val (r.val 0) = i
    rw [hr0, hp]

/-- The actual dodecad/outside-point stabilizer is the ordinary pair-action stabilizer. -/
theorem golayDodecadOutsideZeroStabilizer_eq_pair_stabilizer :
    golayDodecadOutsideZeroStabilizer =
      MulAction.stabilizer golayAutomorphismSubgroup
        (golayDodecadOrbitCodeLabel 0, (0 : Fin 24)) := by
  ext p
  rw [golayDodecadOutsideZeroStabilizer, Subgroup.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    apply MulAction.mem_stabilizer_iff.mpr
    apply Prod.ext
    · exact MulAction.mem_stabilizer_iff.mp hq
    · exact (golayPointStabilizer_one_iff q.val).mp q.property
  · intro hp
    have he := MulAction.mem_stabilizer_iff.mp hp
    have h0 : p.val 0 = 0 := congrArg Prod.snd he
    let q : golayPointStabilizer 1 := ⟨p, (golayPointStabilizer_one_iff p).mpr h0⟩
    refine ⟨q, ?_, rfl⟩
    exact MulAction.mem_stabilizer_iff.mpr (congrArg Prod.fst he)

/-- Every actual dodecad together with a specified outside coordinate has stabilizer order 7920. -/
theorem golayDodecadFlag_stabilizer_card (d : Fin 4096) (i : Fin 24)
    (hd : d ∈ golayDodecadsOutside i) :
    Nat.card (MulAction.stabilizer golayAutomorphismSubgroup (d, i)) = 7920 := by
  obtain ⟨p, hp⟩ := golayDodecadFlag_reaches d i hd
  rw [← Nat.card_congr (MulAction.stabilizerEquivStabilizer hp.symm).toEquiv,
    ← golayDodecadOutsideZeroStabilizer_eq_pair_stabilizer,
    golayDodecadOutsideZeroStabilizer_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
