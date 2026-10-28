/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8OrthogonalShortFlagStabilizer

/-! Whole outside-octad axis stabilizers project onto their genuine orthogonal section flag. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The actual full first-axis stabilizer of the actual outside destination. -/
def generatedFeasibleOutsideOctadStabilizer :
    Subgroup (localAxisStabilizer generatedFeasiblePhysicalRootPair) :=
  MulAction.stabilizer (localAxisStabilizer generatedFeasiblePhysicalRootPair)
    generatedFeasibleOutsideOctadDestination

/-- The actual source destination equals the original globally counted old octad axis. -/
theorem generatedFeasibleOutsideOctad_destination_eq_old :
    generatedFeasibleOutsideOctadDestination = generatedOctadLocalAxis 0 0 := rfl

/-- The genuine Co1 image of the original section together with its actual orthogonal first root. -/
abbrev generatedFeasibleOutsideOctadFlag :=
  generatedAxisE8Co1ShortFlagStabilizer generatedOctadBasisOctad
    (Sum.inl (0, generatedFeasiblePhysicalRootPair))

private theorem phase_bit (c : ZMod 2) : c = 0 ∨ c = 1 := by
  have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
  exact h c

private theorem phase_double (c : ZMod 2) : c + c = 0 := by
  have h : ∀ c : ZMod 2, c + c = 0 := by decide +kernel
  exact h c

/-- An actual full-octad Q fixer corrects any first phase while retaining whole-axis fixation. -/
theorem generatedFeasibleOutsideOctad_first_phase_correct (f : localFiberSubgroup)
    (hfix : rhoLocal (localFiberIntoH f) (generatedOctadLocalAxis 0 0) =
      generatedOctadLocalAxis 0 0)
    (hp : griessShortPermutation f.val.2 (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      Sum.inl (0, generatedFeasiblePhysicalRootPair)) :
    ∃ k : localFiberSubgroup, k.val.2 = f.val.2 ∧
      localFiberIntoH k ∈ localAxisStabilizer generatedFeasiblePhysicalRootPair ∧
      rhoLocal (localFiberIntoH k) (generatedOctadLocalAxis 0 0) =
        generatedOctadLocalAxis 0 0 := by
  let c := localShortPhase f (Sum.inl (0, generatedFeasiblePhysicalRootPair))
  let q : Q := if c = 0 then 1 else generatedFeasibleOutsideOctadPhaseQ
  have hqphase : localShortPhase (localFiberIncl q)
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = c := by
    rw [localAxisQPhase_eq_short_phase]
    rcases phase_bit c with hc | hc
    · simp only [q, hc, ite_true, map_one]
      rfl
    · simp only [q, hc, one_ne_zero, ite_false]
      exact generatedFeasibleOutsideOctad_phase_first
  have hqfix : rhoLocal (inclQ q) (generatedOctadLocalAxis 0 0) =
      generatedOctadLocalAxis 0 0 := by
    by_cases hc : c = 0
    · simp [q, hc]
    · simpa only [q, hc, ite_false] using generatedFeasibleOutsideOctad_phase_whole_axis
  refine ⟨localFiberIncl q * f, ?_, ?_, ?_⟩
  · change 1 * f.val.2 = f.val.2
    exact one_mul _
  · rw [localAxisStabilizer_mk_iff]
    constructor
    · change griessShortPermutation (1 * f.val.2) _ = _
      rw [one_mul]
      exact hp
    · rw [localShortPhase_mul, hp, hqphase]
      exact phase_double c
  · rw [map_mul, map_mul, LinearEquiv.mul_apply, hfix]
    exact hqfix

/-- Every actual whole-axis first fixer projects into the actual section/orthogonal-root flag. -/
theorem generatedFeasibleOutsideOctad_projection_mem
    (h : generatedFeasibleOutsideOctadStabilizer) :
    projH h.val.val ∈ generatedFeasibleOutsideOctadFlag := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val.val
  change localFiberIntoH f = h.val.val at hf
  have hfix : rhoLocal (localFiberIntoH f) (generatedOctadLocalAxis 0 0) =
      generatedOctadLocalAxis 0 0 := by
    rw [hf, ← generatedFeasibleOutsideOctad_destination_eq_old]
    exact h.property
  have hfirst := h.val.property
  rw [← hf] at hfirst
  have hp := (localAxis_fiber_fixed_iff f generatedFeasiblePhysicalRootPair).mp hfirst
  have hs := generatedOctad_axis_stabilizer_spatial 0 0 f hfix
  refine ⟨f.val.2, ?_, ?_⟩
  · exact (generatedAxisE8ShortFlagStabilizer_mem _ _ f.val.2).mpr
      ⟨(generatedAxisE8SectionStabilizer_mem _ _).mp hs, hp.1⟩
  · change QuotientGroup.mk' signsSubgroup f.val.2 = projH h.val.val
    rw [← hf]
    rfl

/-- Restriction of the original H projection to the actual outside whole-axis stabilizer. -/
def generatedFeasibleOutsideOctadProjection :
    generatedFeasibleOutsideOctadStabilizer →* generatedFeasibleOutsideOctadFlag :=
  (projH.comp ((localAxisStabilizer generatedFeasiblePhysicalRootPair).subtype.comp
    generatedFeasibleOutsideOctadStabilizer.subtype)).codRestrict _
      generatedFeasibleOutsideOctad_projection_mem

/-- The restricted projection has exactly the original H projection as its underlying value. -/
theorem generatedFeasibleOutsideOctadProjection_val (h : generatedFeasibleOutsideOctadStabilizer) :
    (generatedFeasibleOutsideOctadProjection h).val = projH h.val.val := rfl

/-- Its kernel is exactly the actual original projection equation. -/
theorem generatedFeasibleOutsideOctadProjection_mem_ker_iff
    (h : generatedFeasibleOutsideOctadStabilizer) :
    h ∈ generatedFeasibleOutsideOctadProjection.ker ↔ projH h.val.val = 1 := by
  change generatedFeasibleOutsideOctadProjection h = 1 ↔ _
  constructor
  · exact fun hh => congrArg Subtype.val hh
  · exact fun hh => Subtype.ext hh

/-- Every genuine orthogonal flag lifts to a fixer of the entire octad and first axes. -/
theorem generatedFeasibleOutsideOctadProjection_surjective :
    Function.Surjective generatedFeasibleOutsideOctadProjection := by
  intro a
  obtain ⟨g, hg, hga⟩ := a.property
  have hp := (generatedAxisE8ShortFlagStabilizer_mem _ _ g).mp hg
  obtain ⟨f, hfg, hfix⟩ := generatedOctad_projected_stabilizer_lift 0 0 g hp.1
  obtain ⟨k, hkf, hkfirst, hkfix⟩ := generatedFeasibleOutsideOctad_first_phase_correct f hfix
    (by rw [hfg]; exact hp.2)
  have hkaxis : rhoLocal (localFiberIntoH k) generatedFeasibleOutsideOctadDestination =
      generatedFeasibleOutsideOctadDestination := by
    rw [generatedFeasibleOutsideOctad_destination_eq_old]
    exact hkfix
  refine ⟨⟨⟨localFiberIntoH k, hkfirst⟩, hkaxis⟩, Subtype.ext ?_⟩
  change QuotientGroup.mk' signsSubgroup k.val.2 = a.val
  rw [hkf, hfg]
  exact hga

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
