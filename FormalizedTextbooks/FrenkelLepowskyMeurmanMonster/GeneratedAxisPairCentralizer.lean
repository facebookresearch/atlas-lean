/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ConwayAxisTranspositionGriess
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFiniteness

/-! The actual stabilizer of two opposite signed short axes lies in the actual local group. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Fixing an actual axis forces commutation with its actual local involution,
through the proved transposition polynomial rather than a supplied spectral rule. -/
theorem generated_fix_shortAxis_commutes (g : G) (r : GriessShortIndex) (c : ZMod 2)
    (hfix : g.val (conwayShortAxis r c) = conwayShortAxis r c) :
    g * qIntoGenerated (qCentral c * griessShortQ r) =
      qIntoGenerated (qCentral c * griessShortQ r) * g := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hp (a b : GriessSpace) :
      g.val (griessProd a b) = griessProd (g.val a) (g.val b) :=
    generated_group_preserves_griessProduct sExtra_preserves_griessProd g a b
  have hf : griessForm (conwayShortAxis r c) (g.val x) =
      griessForm (conwayShortAxis r c) x := by
    simpa only [hfix] using generated_group_preserves_griessForm g (conwayShortAxis r c) x
  have h := congrArg g.val (conwayShortAxis_transposition_polynomial r c x)
  simp only [map_smul, map_sub, map_add, hp, hfix] at h
  have ht := conwayShortAxis_transposition_polynomial r c (g.val x)
  rw [hf] at ht
  have he := h.trans ht.symm
  exact (smul_right_injective _ (by norm_num : (14 : ℝ) ≠ 0)) he

private theorem preferred_axis_involution_product (r : GriessShortIndex) :
    (qCentral 0 * griessShortQ r) * (qCentral 1 * griessShortQ r) = qCentralInvolution := by
  have hc : qCentral 1 ∈ centerQ := (q_mem_center_iff_base_eq_one _).mpr rfl
  have hs := (Subgroup.mem_center_iff.mp hc) (griessShortQ r)
  rw [show qCentral 0 = 1 from rfl, one_mul, ← mul_assoc, hs, mul_assoc,
    griessShortQ_square, mul_one]
  rfl

/-- Fixing both actual opposite signed axes centralizes their product, the
distinguished actual central Q involution. -/
theorem generated_fix_shortAxis_pair_centralizes (g : G) (r : GriessShortIndex)
    (h0 : g.val (conwayShortAxis r 0) = conwayShortAxis r 0)
    (h1 : g.val (conwayShortAxis r 1) = conwayShortAxis r 1) :
    g ∈ generatedCentralizer := by
  have hc0 : Commute g (qIntoGenerated (qCentral 0 * griessShortQ r)) :=
    generated_fix_shortAxis_commutes g r 0 h0
  have hc1 : Commute g (qIntoGenerated (qCentral 1 * griessShortQ r)) :=
    generated_fix_shortAxis_commutes g r 1 h1
  have hc := hc0.mul_right hc1
  rw [← map_mul, preferred_axis_involution_product] at hc
  exact Subgroup.mem_centralizer_singleton_iff.mpr hc

/-- The actual global stabilizer of this pair is contained in the actual local
H image, by the proved full centralizer recognition. -/
theorem generated_fix_shortAxis_pair_local (g : G) (r : GriessShortIndex)
    (h0 : g.val (conwayShortAxis r 0) = conwayShortAxis r 0)
    (h1 : g.val (conwayShortAxis r 1) = conwayShortAxis r 1) :
    g ∈ localIntoGenerated.range := by
  rw [← generatedCentralizer_eq_local_range]
  exact generated_fix_shortAxis_pair_centralizes g r h0 h1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
