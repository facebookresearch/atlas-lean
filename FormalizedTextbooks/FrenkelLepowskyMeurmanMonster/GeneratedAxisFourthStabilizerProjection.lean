/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQFixedCriteria

/-! The actual fourth-axis stabilizer projects into the genuine Co1 flag stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The full actual Q intersection of the fourth-axis stabilizer. -/
def generatedFourthAxisQStabilizer : Subgroup Q :=
  (MulAction.stabilizer H generatedFourthAxis).comap inclQ

/-- The actual Q criterion retains every supported phase and every physical spin column. -/
theorem generatedFourthAxisQStabilizer_mem_iff (q : Q) :
    q ∈ generatedFourthAxisQStabilizer ↔
      (∀ r, (griessConwayEncode generatedFourthAxis).2.1 r ≠ 0 →
        localAxisQPhase r q = 1) ∧
      ∀ j, spinRepresentation q
          (fun t => (griessConwayEncode generatedFourthAxis).2.2 t j) =
        fun t => (griessConwayEncode generatedFourthAxis).2.2 t j :=
  generatedFourthQ_full_fixed_iff q generatedFourthAxis

/-- The genuine stabilizer inside actual H of the original fourth-image representative. -/
def generatedFourthLocalAxisStabilizer : Subgroup H :=
  MulAction.stabilizer H generatedFourthAxis

/-- Every axis-fixing local lift preserves the genuine physical E8 section-short-line flag. -/
theorem generatedFourth_axis_stabilizer_spatial (f : localFiberSubgroup)
    (hf : rhoLocal (localFiberIntoH f) generatedFourthAxis = generatedFourthAxis) :
    f.val.2 ∈ generatedAxisE8ShortFlagStabilizer
      generatedFourthFlagOctad generatedFourthFlagShort := by
  have h := congrArg (fun x : GriessSpace => (griessConwayEncode x).1) hf
  change (griessConwayEncode (localGriessRepresentation f _)).1 = _ at h
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply] at h
  exact (generatedFourth_matrix_stabilizer_iff f.val.2).mp h

/-- The genuine restricted H projection takes values in the actual Co1 flag-stabilizer image. -/
def generatedFourthLocalAxisProjection :
    generatedFourthLocalAxisStabilizer →*
      generatedAxisE8Co1ShortFlagStabilizer generatedFourthFlagOctad generatedFourthFlagShort :=
  (projH.comp generatedFourthLocalAxisStabilizer.subtype).codRestrict _ (by
    intro h
    obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
    change localFiberIntoH f = h.val at hf
    have hfix : rhoLocal (localFiberIntoH f) generatedFourthAxis = generatedFourthAxis := by
      rw [hf]
      exact h.property
    refine ⟨f.val.2, generatedFourth_axis_stabilizer_spatial f hfix, ?_⟩
    change QuotientGroup.mk' signsSubgroup f.val.2 = projH h.val
    rw [← hf]
    rfl)

/-- The genuine Q intersection embeds in the genuine H axis stabilizer. -/
def generatedFourthAxisPhaseInclusion :
    generatedFourthAxisQStabilizer →* generatedFourthLocalAxisStabilizer :=
  (inclQ.comp generatedFourthAxisQStabilizer.subtype).codRestrict _ (by
    intro q
    exact q.property)

theorem generatedFourthAxisPhaseInclusion_injective :
    Function.Injective generatedFourthAxisPhaseInclusion := by
  intro q r h
  apply Subtype.ext
  apply inclQ_injective
  exact congrArg Subtype.val h

/-- The restricted projection kernel is exactly the actual Q axis stabilizer. -/
theorem generatedFourthAxisPhaseInclusion_range :
    generatedFourthAxisPhaseInclusion.range = generatedFourthLocalAxisProjection.ker := by
  ext h
  constructor
  · rintro ⟨q, rfl⟩
    apply Subtype.ext
    change projH (inclQ q.val) = 1
    have hq : inclQ q.val ∈ projH.ker := by
      rw [← inclQ_range_eq_projH_ker]
      exact ⟨q.val, rfl⟩
    exact hq
  · intro hk
    have hker : h.val ∈ projH.ker := congrArg Subtype.val hk
    rw [← inclQ_range_eq_projH_ker] at hker
    obtain ⟨q, hq⟩ := hker
    have hphase : q ∈ generatedFourthAxisQStabilizer := by
      change inclQ q ∈ generatedFourthLocalAxisStabilizer
      rw [hq]
      exact h.property
    exact ⟨⟨q, hphase⟩, Subtype.ext hq⟩

/-- The projection kernel has exactly the size of the genuine full-axis Q stabilizer. -/
theorem generatedFourthLocalAxisProjection_kernel_card :
    Nat.card generatedFourthLocalAxisProjection.ker = Nat.card generatedFourthAxisQStabilizer := by
  rw [← generatedFourthAxisPhaseInclusion_range]
  have h := Nat.card_congr
    (MonoidHom.ofInjective generatedFourthAxisPhaseInclusion_injective).toEquiv
  rw [← h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
