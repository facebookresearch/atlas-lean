/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedForwardQProjection

/-! Genuine local lifts and Conway projections of arbitrary even Q triality conjugates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Even modulation is precisely the needed actual commutation with Ω. -/
theorem generatedEvenQ_commute_omega (q : Q) (he : spinModulation q 11 = 0) :
    q * sourceOmegaQ = sourceOmegaQ * q := by
  apply (q_mul_comm_iff _ _).mpr
  rw [qBeta_spin_coordinates, qBeta_spin_coordinates,
    sourceOmegaQ_translation, sourceOmegaQ_modulation]
  simp [spinDot, Pi.single_apply, he]

/-- Forward triality conjugation of any even Q element belongs to the genuine local range. -/
theorem generatedForwardQ_local_exists (q : Q) (he : spinModulation q 11 = 0) :
    ∃ h : H, localIntoGenerated h =
      extraIntoGenerated * qIntoGenerated q * extraIntoGenerated⁻¹ := by
  have hq : qIntoGenerated q ∈ generatedAxisTransitionNormalizer := by
    rw [generatedAxisTransitionNormalizer_eq_local_omega]
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    · exact ⟨inclQ q, rfl⟩
    · rw [← map_mul, ← map_mul, generatedEvenQ_commute_omega q he]
  have hh := generatedAxisTransitionNormalizer_triality _ hq
  rw [generatedAxisTransitionNormalizer_eq_local_omega] at hh
  exact hh.1

/-- A chosen actual local lift of the forward conjugate of an arbitrary even Q element. -/
def generatedForwardQLocal (q : Q) (he : spinModulation q 11 = 0) : H :=
  Classical.choose (generatedForwardQ_local_exists q he)

/-- The chosen lift is the exact original forward triality word. -/
theorem generatedForwardQLocal_generated (q : Q) (he : spinModulation q 11 = 0) :
    localIntoGenerated (generatedForwardQLocal q he) =
      extraIntoGenerated * qIntoGenerated q * extraIntoGenerated⁻¹ :=
  Classical.choose_spec (generatedForwardQ_local_exists q he)

/-- Its full Griess operator is forward triality, actual Q, then inverse triality. -/
theorem generatedForwardQLocal_action (q : Q) (he : spinModulation q 11 = 0) :
    rhoLocal (generatedForwardQLocal q he) =
      sExtra * rhoLocal (inclQ q) * sExtra⁻¹ :=
  congrArg Subtype.val (generatedForwardQLocal_generated q he)

/-- The actual Conway projection depends only on the encoded translation of the even Q input. -/
theorem generatedForwardQLocal_projection (q : Q) (he : spinModulation q 11 = 0)
    (d : Fin 4096) (hd : spinTranslation q = golayLabelCoefficients d) :
    projH (generatedForwardQLocal q he) =
      (QuotientGroup.mk (golaySignIsometry (sourceGeneratedSignCode d)) : Co1) := by
  apply projH_eq_of_matrix_action
  intro x
  rw [generatedForwardQLocal_action]
  exact generatedForwardQ_matrix q d hd he x

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
