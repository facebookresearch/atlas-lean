/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOutsideOctadStabilizerProjection

/-! Exact genuine extraspecial kernel in the outside first-axis and whole-octad stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The actual first-root phase restricted to the actual full-octad Q stabilizer. -/
def generatedFeasibleOutsideOctadQFirstPhase :
    generatedOctadAxisQStabilizer 0 0 →* Multiplicative (ZMod 2) :=
  (localAxisQPhase (Sum.inl (0, generatedFeasiblePhysicalRootPair))).comp
    (generatedOctadAxisQStabilizer 0 0).subtype

/-- The genuine whole-octad fixer with first phase one makes that actual phase map surjective. -/
theorem generatedFeasibleOutsideOctadQFirstPhase_surjective :
    Function.Surjective generatedFeasibleOutsideOctadQFirstPhase := by
  intro a
  have hb : toAdd a = 0 ∨ toAdd a = 1 := by
    have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
    exact h (toAdd a)
  rcases hb with ha | ha
  · refine ⟨1, ?_⟩
    rw [map_one]
    exact toAdd.injective ha.symm
  · let q : generatedOctadAxisQStabilizer 0 0 :=
      ⟨generatedFeasibleOutsideOctadPhaseQ,
        generatedOctad_phase_kernel_le_axis_stabilizer 0 0
          generatedFeasibleOutsideOctad_phase_kernel⟩
    refine ⟨q, toAdd.injective ?_⟩
    change toAdd (localAxisQPhase (Sum.inl (0, generatedFeasiblePhysicalRootPair))
      generatedFeasibleOutsideOctadPhaseQ) = toAdd a
    rw [generatedFeasibleOutsideOctad_phase_first, ha]

/-- Exactly2^16 actual Q elements fix the first axis and the entire outside octad axis. -/
theorem generatedFeasibleOutsideOctadQFirstPhase_kernel_card :
    Nat.card generatedFeasibleOutsideOctadQFirstPhase.ker = 2 ^ 16 := by
  have h := generatedFeasibleOutsideOctadQFirstPhase.ker.card_mul_index
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr generatedFeasibleOutsideOctadQFirstPhase_surjective,
    Subgroup.card_top, generatedOctadAxisQStabilizer_card] at h
  have hc : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  rw [hc] at h
  norm_num only [Nat.reducePow] at h ⊢
  omega

/-- Each actual zero-first-phase whole-octad Q element fixes both entire original axes. -/
theorem generatedFeasibleOutsideOctad_phase_inclusion_mem
    (q : generatedFeasibleOutsideOctadQFirstPhase.ker) :
    inclQ q.val.val ∈ localAxisStabilizer generatedFeasiblePhysicalRootPair ∧
      rhoLocal (inclQ q.val.val) generatedFeasibleOutsideOctadDestination =
        generatedFeasibleOutsideOctadDestination := by
  have hp : q.val.val ∈ (localAxisQPhase
      (Sum.inl (0, generatedFeasiblePhysicalRootPair))).ker := q.property
  have hfirst : inclQ q.val.val ∈ localAxisStabilizer generatedFeasiblePhysicalRootPair := by
    rw [← localAxisStabilizer_comap_inclQ] at hp
    exact hp
  refine ⟨hfirst, ?_⟩
  rw [generatedFeasibleOutsideOctad_destination_eq_old]
  exact q.val.property

/-- The original Q inclusion restricted to the actual simultaneous full-axis phase kernel. -/
def generatedFeasibleOutsideOctadPhaseInclusion :
    generatedFeasibleOutsideOctadQFirstPhase.ker →* generatedFeasibleOutsideOctadStabilizer where
  toFun q := ⟨⟨inclQ q.val.val, (generatedFeasibleOutsideOctad_phase_inclusion_mem q).1⟩,
    (generatedFeasibleOutsideOctad_phase_inclusion_mem q).2⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_one inclQ
  map_mul' q k := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul inclQ q.val.val k.val.val

/-- This genuine original Q inclusion is injective. -/
theorem generatedFeasibleOutsideOctadPhaseInclusion_injective :
    Function.Injective generatedFeasibleOutsideOctadPhaseInclusion := by
  intro q k h
  apply Subtype.ext
  apply Subtype.ext
  apply inclQ_injective
  exact congrArg (fun h : generatedFeasibleOutsideOctadStabilizer => h.val.val) h

/-- The actual projected full-axis kernel is exactly the image of the genuine Q phase kernel. -/
theorem generatedFeasibleOutsideOctadPhaseInclusion_range :
    generatedFeasibleOutsideOctadPhaseInclusion.range =
      generatedFeasibleOutsideOctadProjection.ker := by
  ext h
  constructor
  · rintro ⟨q, rfl⟩
    rw [generatedFeasibleOutsideOctadProjection_mem_ker_iff]
    exact projH_inclQ q.val.val
  · intro hh
    have hk := (generatedFeasibleOutsideOctadProjection_mem_ker_iff h).mp hh
    have hker : h.val.val ∈ projH.ker := hk
    rw [← inclQ_range_eq_projH_ker] at hker
    obtain ⟨q, hq⟩ := hker
    have hwhole : q ∈ generatedOctadAxisQStabilizer 0 0 := by
      change rhoLocal (inclQ q) (generatedOctadLocalAxis 0 0) = generatedOctadLocalAxis 0 0
      rw [hq, ← generatedFeasibleOutsideOctad_destination_eq_old]
      exact h.property
    let qold : generatedOctadAxisQStabilizer 0 0 := ⟨q, hwhole⟩
    have hfirst : q ∈ (localAxisQPhase
        (Sum.inl (0, generatedFeasiblePhysicalRootPair))).ker := by
      rw [← localAxisStabilizer_comap_inclQ]
      change inclQ q ∈ localAxisStabilizer generatedFeasiblePhysicalRootPair
      rw [hq]
      exact h.val.property
    have hphase : qold ∈ generatedFeasibleOutsideOctadQFirstPhase.ker := hfirst
    let qs : generatedFeasibleOutsideOctadQFirstPhase.ker := ⟨qold, hphase⟩
    exact ⟨qs, Subtype.ext (Subtype.ext hq)⟩

/-- The genuine whole-axis projection has exactly2^16 kernel elements. -/
theorem generatedFeasibleOutsideOctadProjection_kernel_card :
    Nat.card generatedFeasibleOutsideOctadProjection.ker = 2 ^ 16 := by
  rw [← generatedFeasibleOutsideOctadPhaseInclusion_range]
  have h := Nat.card_congr
    (MonoidHom.ofInjective generatedFeasibleOutsideOctadPhaseInclusion_injective).toEquiv
  rw [← h]
  exact generatedFeasibleOutsideOctadQFirstPhase_kernel_card

/-- The actual simultaneous first-axis and full outside-octad stabilizer has exact order. -/
theorem generatedFeasibleOutsideOctadStabilizer_card :
    Nat.card generatedFeasibleOutsideOctadStabilizer = 2705829396480 := by
  have h := generatedFeasibleOutsideOctadProjection.ker.card_mul_index
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr generatedFeasibleOutsideOctadProjection_surjective,
    Subgroup.card_top, generatedFeasibleOutsideOctadProjection_kernel_card,
    generatedAxisE8Orthogonal_co1_flag_card] at h
  norm_num at h
  exact h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
