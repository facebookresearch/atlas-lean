/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionFeasibleCosets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityReflection

/-! The actual local stabilizer of the triality image of the opposite axis. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The second actual feasible representative, obtained by genuine triality. -/
noncomputable def generatedFeasibleSecondaryAxis (p : Fin 276) : GriessSpace :=
  sExtra (conwayShortAxis (Sum.inl (0, p)) 1)

/-- Inverse triality also preserves the genuine feasible transition subgroup. -/
theorem localFeasibleTransition_triality_inverse_conjugate (p : Fin 276)
    (n : localFeasibleTransitionSubgroup p) :
    ∃ k : localFeasibleTransitionSubgroup p,
      extraIntoGenerated⁻¹ * localIntoGenerated n.val.val * extraIntoGenerated =
        localIntoGenerated k.val.val := by
  obtain ⟨k, hk⟩ := localFeasibleTransition_triality_conjugate p n
  obtain ⟨l, hl⟩ := localFeasibleTransition_triality_conjugate p k
  have ht : extraIntoGenerated * extraIntoGenerated = extraIntoGenerated⁻¹ := by
    apply mul_right_cancel (b := extraIntoGenerated)
    simpa only [pow_succ, pow_zero, one_mul, mul_one, inv_mul_cancel]
      using extraIntoGenerated_pow_three
  refine ⟨l, ?_⟩
  calc
    _ = extraIntoGenerated *
        (extraIntoGenerated * localIntoGenerated n.val.val * extraIntoGenerated⁻¹) *
          extraIntoGenerated⁻¹ := by
      calc
        _ = (extraIntoGenerated * extraIntoGenerated) * localIntoGenerated n.val.val *
            (extraIntoGenerated⁻¹ * extraIntoGenerated⁻¹) := by
          rw [ht, extraIntoGenerated_inv_mul_inv]
        _ = _ := by group
    _ = _ := by rw [hk, hl]

/-- Every genuine feasible transition element fixes the second actual representative. -/
theorem localFeasibleTransition_fixes_secondary (p : Fin 276)
    (n : localFeasibleTransitionSubgroup p) :
    rhoLocal n.val.val (generatedFeasibleSecondaryAxis p) =
      generatedFeasibleSecondaryAxis p := by
  obtain ⟨k, hk⟩ := localFeasibleTransition_triality_inverse_conjugate p n
  have hw : localIntoGenerated n.val.val * extraIntoGenerated =
      extraIntoGenerated * localIntoGenerated k.val.val := by
    calc
      _ = extraIntoGenerated *
          (extraIntoGenerated⁻¹ * localIntoGenerated n.val.val * extraIntoGenerated) := by group
      _ = _ := by rw [hk]
  have he := congrArg (fun g : G => g.val (conwayShortAxis (Sum.inl (0, p)) 1)) hw
  change rhoLocal n.val.val (generatedFeasibleSecondaryAxis p) =
    sExtra (rhoLocal k.val.val (conwayShortAxis (Sum.inl (0, p)) 1)) at he
  rw [localAxisStabilizer_signedAxis_fixed k.val.val p k.val.property 1] at he
  exact he

/-- Fixing the first axis and the second representative forces membership in the
actual Ω centralizer, using the proved transposition polynomial and full centralizer. -/
theorem localAxisStabilizer_secondary_fixes_omega (p : Fin 276)
    (h : localAxisStabilizer p)
    (hf : rhoLocal h.val (generatedFeasibleSecondaryAxis p) =
      generatedFeasibleSecondaryAxis p) : h.val ∈ localOmegaStabilizer := by
  let g := localIntoGenerated h.val
  let g' := extraIntoGenerated⁻¹ * g * extraIntoGenerated
  have ha : g'.val (conwayShortAxis (Sum.inl (0, p)) 0) =
      conwayShortAxis (Sum.inl (0, p)) 0 := by
    rw [conwayShortAxis_pair_zero]
    change sExtra.symm (rhoLocal h.val (sExtra (conwayAxis p))) = conwayAxis p
    rw [conwayAxis_triality, h.property]
    exact sExtra.symm_apply_eq.mpr (conwayAxis_triality p).symm
  have hb : g'.val (conwayShortAxis (Sum.inl (0, p)) 1) =
      conwayShortAxis (Sum.inl (0, p)) 1 := by
    change sExtra.symm (rhoLocal h.val (generatedFeasibleSecondaryAxis p)) = _
    rw [hf]
    exact sExtra.symm_apply_apply _
  have hc : Commute g' (qIntoGenerated qCentralInvolution) :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (generated_fix_shortAxis_pair_centralizes g' (Sum.inl (0, p)) ha hb)
  have hc' := hc.conj extraIntoGenerated
  have hg : extraIntoGenerated * g' * extraIntoGenerated⁻¹ = g := by
    dsimp [g']
    group
  have hs1 : extraIntoGenerated * qIntoGenerated qCentralInvolution *
      extraIntoGenerated⁻¹ = centralSignIntoGenerated 1 := by
    apply Subtype.ext
    exact localCentralGriess_conjugate
  rw [hg, hs1] at hc'
  have hz : g ∈ generatedCentralizer := by
    change g ∈ Subgroup.centralizer {qIntoGenerated qCentralInvolution}
    rw [generatedCentralizer_eq_local_range]
    exact ⟨h.val, rfl⟩
  have hc0 : Commute g (centralSignIntoGenerated 0) := by
    have hs0 : qIntoGenerated qCentralInvolution = centralSignIntoGenerated 0 := by
      apply Subtype.ext
      exact localCentralGriess_eq_trialityCentralSign
    rw [← hs0]
    exact Subgroup.mem_centralizer_singleton_iff.mp hz
  have hs2 : centralSignIntoGenerated 0 * centralSignIntoGenerated 1 =
      centralSignIntoGenerated 2 := by
    apply Subtype.ext
    exact trialityCentralSign_zero_mul_one
  have hn : g ∈ generatedAxisTransitionNormalizer := by
    rw [generatedAxisTransitionNormalizer_mem_iff]
    intro k
    fin_cases k
    · exact hc0
    · exact hc'
    · change g * centralSignIntoGenerated 2 = centralSignIntoGenerated 2 * g
      exact hs2 ▸ hc0.mul_right hc'
  rw [← generatedAxisTransitionNormalizer_comap_local]
  exact hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
