/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerRecognition
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightRepresentative

/-! Genuine source fixers centralizing the transported involution give full local axis fixers. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A genuine source-axis fixer centralizing the transported central involution has an actual
local conjugate fixing the entire transported axis. -/
theorem generatedAxis_fixer_local_of_transported_centralizer (w g : G) (x : GriessSpace)
    (hfix : g.val x = x)
    (hcomm : g * (w⁻¹ * qIntoGenerated qCentralInvolution * w) =
      (w⁻¹ * qIntoGenerated qCentralInvolution * w) * g) :
    ∃ h : H, localIntoGenerated h = w * g * w⁻¹ ∧
      rhoLocal h (w.val x) = w.val x := by
  have hc : w * g * w⁻¹ ∈ Subgroup.centralizer {qIntoGenerated qCentralInvolution} := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have he : a = qIntoGenerated qCentralInvolution := Set.mem_singleton_iff.mp ha
    subst a
    calc
      _ = w * ((w⁻¹ * qIntoGenerated qCentralInvolution * w) * g) * w⁻¹ := by group
      _ = w * (g * (w⁻¹ * qIntoGenerated qCentralInvolution * w)) * w⁻¹ := by rw [hcomm]
      _ = _ := by group
  rw [generatedCentralizer_eq_local_range] at hc
  obtain ⟨h, hh⟩ := hc
  refine ⟨h, hh, ?_⟩
  have he := congrArg Subtype.val hh
  change rhoLocal h = w.val * g.val * w.val⁻¹ at he
  rw [he]
  simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv,
    LinearEquiv.symm_apply_apply, hfix]

/-- Actual source fixers centralizing the original root-eight transported involution produce
entire original root-eight local fixers. -/
theorem generatedFifthRootEight_fixer_local_of_source_centralizer (g : G)
    (hfix : g.val (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0) =
      conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)
    (hcomm : g * (generatedFifthRootEightAxisWord⁻¹ * qIntoGenerated qCentralInvolution *
        generatedFifthRootEightAxisWord) =
      (generatedFifthRootEightAxisWord⁻¹ * qIntoGenerated qCentralInvolution *
        generatedFifthRootEightAxisWord) * g) :
    ∃ h : H, localIntoGenerated h = generatedFifthRootEightAxisWord * g *
        generatedFifthRootEightAxisWord⁻¹ ∧
      rhoLocal h generatedFifthRootEightAxis = generatedFifthRootEightAxis := by
  exact generatedAxis_fixer_local_of_transported_centralizer
    generatedFifthRootEightAxisWord g _ hfix hcomm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
