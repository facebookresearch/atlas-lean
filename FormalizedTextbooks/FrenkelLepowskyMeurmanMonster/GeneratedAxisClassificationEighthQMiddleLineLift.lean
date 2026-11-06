/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQMiddleNormalizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddLineLifts

/-! Actual spatial preservation of the signed middle vector lifts to full middle-axis fixation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine real norm-eight direction of the original middle axis. -/
def generatedEighthMiddleUnit : Fin 24 → ℝ :=
  generatedEighthLocalFiber.val.2.val (Pi.single 0 1)

/-- Preserving the middle direction gives a full-axis lift with the original spatial map. -/
theorem generatedEighth_middle_line_lift (g : leechIsomSubgroup)
    (hg : g.val generatedEighthMiddleUnit = generatedEighthMiddleUnit) :
    ∃ f : localFiberSubgroup, f.val.2 = g ∧
      rhoLocal (localFiberIntoH f) generatedEighthMiddleAxis = generatedEighthMiddleAxis := by
  let a : leechIsomSubgroup :=
    generatedEighthLocalFiber.val.2⁻¹ * g * generatedEighthLocalFiber.val.2
  have ha : a.val (Pi.single 0 1) = Pi.single 0 1 := by
    change generatedEighthLocalFiber.val.2.val.symm
      (g.val (generatedEighthLocalFiber.val.2.val (Pi.single 0 1))) = _
    change generatedEighthLocalFiber.val.2.val.symm (g.val generatedEighthMiddleUnit) = _
    rw [hg]
    exact LinearEquiv.symm_apply_apply _ _
  have hl : a ∈ generatedNormEightLineStabilizer :=
    generatedAxisGlobalOdd_signed_unit_line a 0 (by simpa only [qSign_zero, one_smul] using ha)
  obtain ⟨f, hs, hf⟩ := generatedOddAxis_projected_stabilizer_lift a hl
  let k := generatedEighthLocalFiber * f * generatedEighthLocalFiber⁻¹
  refine ⟨k, ?_, ?_⟩
  · change generatedEighthLocalFiber.val.2 * f.val.2 * generatedEighthLocalFiber.val.2⁻¹ = g
    rw [hs]
    dsimp only [a]
    group
  · change rhoLocal (localFiberIntoH
      (generatedEighthLocalFiber * f * generatedEighthLocalFiber⁻¹))
      (rhoLocal (localFiberIntoH generatedEighthLocalFiber) generatedOddAxis) = _
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
    simp only [LinearEquiv.mul_apply]
    change rhoLocal (localFiberIntoH generatedEighthLocalFiber)
      (rhoLocal (localFiberIntoH f)
        ((rhoLocal (localFiberIntoH generatedEighthLocalFiber)).symm
          (rhoLocal (localFiberIntoH generatedEighthLocalFiber) generatedOddAxis))) = _
    rw [LinearEquiv.symm_apply_apply, hf]
    rfl

/-- A middle monomial direction fixer has a full middle lift centralizing actual omega. -/
theorem generatedEighth_middle_monomial_line_lift (g : leechIsomSubgroup)
    (hm : g ∈ golayMonomialSubgroup)
    (hg : g.val generatedEighthMiddleUnit = generatedEighthMiddleUnit) :
    ∃ f : localFiberSubgroup, f.val.2 = g ∧
      rhoLocal (localFiberIntoH f) generatedEighthMiddleAxis = generatedEighthMiddleAxis ∧
      spinConjugation f.val.1 sourceOmegaQ = sourceOmegaQ := by
  obtain ⟨f, hs, hf⟩ := generatedEighth_middle_line_lift g hg
  obtain ⟨k, hk, hfix, ho⟩ := generatedEighth_middle_monomial_omega_correct f (hs ▸ hm) hf
  exact ⟨k, hk.trans hs, hfix, ho⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
