/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityOmega

/-! The actual local intersection normalized by triality, used for axis transitions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual subgroup centralizing all three signs of the source Klein four. -/
noncomputable def generatedAxisTransitionNormalizer : Subgroup G :=
  Subgroup.centralizer (Set.range centralSignIntoGenerated)

private theorem signZero_eq :
    centralSignIntoGenerated 0 = qIntoGenerated qCentralInvolution := by
  apply Subtype.ext
  exact localCentralGriess_eq_trialityCentralSign.symm

private theorem signZero_mul_two :
    centralSignIntoGenerated 0 * centralSignIntoGenerated 2 =
      centralSignIntoGenerated 1 := by
  apply Subtype.ext
  change trialityCentralSign 0 * trialityCentralSign 2 = trialityCentralSign 1
  rw [← trialityCentralSign_zero_mul_one, ← mul_assoc,
    trialityCentralSign_square, one_mul]

private theorem sign_conjugate (k : Fin 3) :
    extraIntoGenerated * centralSignIntoGenerated k * extraIntoGenerated⁻¹ =
      centralSignIntoGenerated (trialityCycle k) := by
  apply Subtype.ext
  exact trialityCentralSign_conjugate k

/-- Membership is precisely commutation with each actual sign. -/
theorem generatedAxisTransitionNormalizer_mem_iff (g : G) :
    g ∈ generatedAxisTransitionNormalizer ↔
      ∀ k, g * centralSignIntoGenerated k = centralSignIntoGenerated k * g := by
  simp only [generatedAxisTransitionNormalizer, Subgroup.mem_centralizer_iff,
    Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  exact ⟨fun h k => (h k).symm, fun h k => (h k).symm⟩

/-- The transition subgroup is the actual local group intersected with the
centralizer of the actual source Ω element. -/
theorem generatedAxisTransitionNormalizer_eq_local_omega :
    generatedAxisTransitionNormalizer = localIntoGenerated.range ⊓
      Subgroup.centralizer {qIntoGenerated sourceOmegaQ} := by
  ext g
  rw [generatedAxisTransitionNormalizer_mem_iff, Subgroup.mem_inf,
    ← generatedCentralizer_eq_local_range, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, qIntoGenerated_sourceOmegaQ,
    ← signZero_eq]
  constructor
  · intro hg
    exact ⟨hg 0, hg 2⟩
  · rintro ⟨hzero, htwo⟩ k
    fin_cases k
    · exact hzero
    · change g * centralSignIntoGenerated 1 = centralSignIntoGenerated 1 * g
      rw [← signZero_mul_two]
      calc
        g * (centralSignIntoGenerated 0 * centralSignIntoGenerated 2) =
            (g * centralSignIntoGenerated 0) * centralSignIntoGenerated 2 :=
          (mul_assoc _ _ _).symm
        _ = (centralSignIntoGenerated 0 * g) * centralSignIntoGenerated 2 := by rw [hzero]
        _ = centralSignIntoGenerated 0 * (g * centralSignIntoGenerated 2) := mul_assoc _ _ _
        _ = centralSignIntoGenerated 0 * (centralSignIntoGenerated 2 * g) := by rw [htwo]
        _ = (centralSignIntoGenerated 0 * centralSignIntoGenerated 2) * g :=
          (mul_assoc _ _ _).symm
    · exact htwo

/-- Actual triality conjugation preserves the transition subgroup. -/
theorem generatedAxisTransitionNormalizer_triality (g : G)
    (hg : g ∈ generatedAxisTransitionNormalizer) :
    extraIntoGenerated * g * extraIntoGenerated⁻¹ ∈ generatedAxisTransitionNormalizer := by
  rw [generatedAxisTransitionNormalizer_mem_iff] at hg ⊢
  intro k
  let j := trialityCycle.symm k
  have hs : extraIntoGenerated * centralSignIntoGenerated j * extraIntoGenerated⁻¹ =
      centralSignIntoGenerated k := by
    simpa only [j, Equiv.apply_symm_apply] using sign_conjugate j
  calc
    (extraIntoGenerated * g * extraIntoGenerated⁻¹) * centralSignIntoGenerated k =
        extraIntoGenerated * (g * centralSignIntoGenerated j) * extraIntoGenerated⁻¹ := by
      rw [← hs]
      group
    _ = extraIntoGenerated * (centralSignIntoGenerated j * g) * extraIntoGenerated⁻¹ := by
      rw [hg j]
    _ = centralSignIntoGenerated k * (extraIntoGenerated * g * extraIntoGenerated⁻¹) := by
      rw [← hs]
      group

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
