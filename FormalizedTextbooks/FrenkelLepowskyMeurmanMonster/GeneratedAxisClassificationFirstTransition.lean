/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisEnumerationLocal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedSubgroups

/-! A concrete triality transition out of the first local axis orbit.
The original dictionary sends an odd-family short X coordinate to a Y
coordinate. This proves actual orbit separation without Atlas names or a
watermark classification. See Höhn–Seysen, arXiv:2508.01037, §3.1. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem signed_axis_Y_zero (r : GriessShortIndex) (c : ZMod 2) (k : Fin 49152) :
    (trialityBlocksEquiv (conwayShortAxis r c)).2.2.2 1 k = 0 := by
  simp [conwayShortAxis, griessConwayDecode, conwayShortAxisRaw]

/-- An actual odd-family axis contributes a nonzero original Y dictionary
coordinate after triality. -/
theorem generatedAxis_triality_odd_Y (d : Fin 2048) (i : Fin 24) (c : ZMod 2) :
    (trialityBlocksEquiv (sExtra (conwayShortAxis (Sum.inr (Sum.inr (d, i))) c))).2.2.2
      1 (finProdFinEquiv (d, i)) = -8 * qSign c := by
  simp only [sExtra, griessTriality, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  change trialityCycleAction 49152
    (trialityBlocksEquiv (conwayShortAxis (Sum.inr (Sum.inr (d, i))) c)).2.2.2
      1 (finProdFinEquiv (d, i)) = _
  have hc : trialityCycle.symm 1 = 0 := by decide
  simp only [trialityCycleAction, LinearEquiv.piCongrLeft'_apply, hc]
  simp [conwayShortAxis, griessConwayDecode, conwayShortAxisRaw]

/-- This concrete generated axis is outside the entire first local orbit. -/
theorem generatedAxis_triality_odd_not_signed (d : Fin 2048) (i : Fin 24) (c : ZMod 2) :
    sExtra (conwayShortAxis (Sum.inr (Sum.inr (d, i))) c) ∉ generatedSignedShortAxes := by
  rintro ⟨⟨r, e⟩, he⟩
  have hY := congrArg (fun x : GriessSpace =>
    (trialityBlocksEquiv x).2.2.2 1 (finProdFinEquiv (d, i))) he
  rw [signed_axis_Y_zero, generatedAxis_triality_odd_Y] at hY
  have hs := qSign_sq c
  nlinarith

/-- The separated axis really lies in the orbit of the original signed-short axis. -/
theorem generatedAxis_triality_odd_mem_orbit (r : GriessShortIndex) (c : ZMod 2)
    (d : Fin 2048) (i : Fin 24) (e : ZMod 2) :
    sExtra (conwayShortAxis (Sum.inr (Sum.inr (d, i))) e) ∈
      generatedVectorOrbit (conwayShortAxis r c) := by
  obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive r (Sum.inr (Sum.inr (d, i))) c e
  refine ⟨extraIntoGenerated * localIntoGenerated h, ?_⟩
  change sExtra (rhoLocal h (conwayShortAxis r c)) = _
  rw [hh]

/-- The first genuine H orbit does not exhaust the generated axis orbit. -/
theorem generatedAxis_globalOrbit_ne_first_local (r : GriessShortIndex) (c : ZMod 2) :
    generatedVectorOrbit (conwayShortAxis r c) ≠ generatedAxisLocalOrbit r c := by
  intro he
  have hm := generatedAxis_triality_odd_mem_orbit r c 0 0 0
  rw [he, generatedAxisLocalOrbit_eq_signed] at hm
  exact generatedAxis_triality_odd_not_signed 0 0 0 hm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
