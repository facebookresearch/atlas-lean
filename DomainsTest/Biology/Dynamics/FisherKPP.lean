/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Dynamics.FisherKPP
public import MathlibExt.Analysis.ODE.PlanarShooting.InvariantRegion

@[expose] public section

open Real Filter Topology
open MathlibExt.Biology.Dynamics.FisherKPP

namespace MathlibExtTest.Biology.Dynamics.FisherKPP

/-- Non-vacuity witness: the Ablowitz–Zeppetella front `(1 + e^{z/√6})⁻²` for `D = r = C = 1`. -/
example : IsFront 1 1 (azSpeed 1 1) (azWave 1 1 1) (azWaveDeriv 1 1 1) :=
  isFront_azWave one_pos one_pos one_pos

/-- With `D = r = 1` the Ablowitz–Zeppetella speed is `5/√6`. -/
example : azSpeed 1 1 = 5 / √6 := by
  rw [azSpeed, one_mul, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 6), Real.sqrt_one]
  ring

/-- It exceeds the minimal speed `2`. -/
example : 2 * √(1 * 1) < azSpeed 1 1 := two_mul_sqrt_lt_azSpeed one_pos one_pos

/-- At the midpoint `z = 0` the front with `C = 1` takes the value `1/4`. -/
example : azWave 1 1 1 0 = 1 / 4 := by
  norm_num [azWave]

/-- No front of speed `1` when `D = r = 1` (`1 < 4 = 4 r D`). -/
example (U U' : ℝ → ℝ) : ¬ IsFront 1 1 1 U U' :=
  not_isFront_of_sq_lt one_pos one_pos (by norm_num)

/-- No front of speed `0` (a standing wave), and none of negative speed below the threshold. -/
example (U U' : ℝ → ℝ) : ¬ IsFront 2 3 (-4) U U' :=
  not_isFront_of_sq_lt (by norm_num) (by norm_num) (by norm_num)

#print axioms not_eventually_pos_of_sq_lt
#print axioms isFront_azWave

end MathlibExtTest.Biology.Dynamics.FisherKPP

open Set MathlibExt.Analysis.ODE.PlanarShooting

namespace MathlibExtTest.Analysis.ODE.PlanarShooting.InvariantRegion

/-! ### A concrete trajectory: the Ablowitz–Zeppetella front -/

private lemma azWaveDeriv_neg (z : ℝ) : azWaveDeriv 1 1 1 z < 0 := by
  have hs : 0 < azRate 1 1 := by unfold azRate; positivity
  have h : azWaveDeriv 1 1 1 z = -(2 * azRate 1 1 * exp (azRate 1 1 * z) *
      (1 + 1 * exp (azRate 1 1 * z))⁻¹ ^ 3) := by
    unfold azWaveDeriv; ring
  rw [h, neg_lt_zero]
  positivity

private lemma tendsto_azWaveDeriv : Tendsto (azWaveDeriv 1 1 1) atBot (𝓝 0) := by
  have hs : 0 < azRate 1 1 := by unfold azRate; positivity
  have h0 : Tendsto (fun z => exp (azRate 1 1 * z)) atBot (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot hs)
  have h := (h0.const_mul (-2 * azRate 1 1 * 1)).mul
    (((tendsto_const_nhds (x := (1 : ℝ))).add (h0.const_mul 1)).inv₀ (by norm_num) |>.pow 3)
  simp only [mul_zero, zero_mul] at h
  refine h.congr fun z => ?_
  simp only [azWaveDeriv, mul_assoc]

/-- Non-vacuity of the conditional shooting theorem: the Ablowitz–Zeppetella wave (`D = r = 1`)
satisfies every hypothesis of `isFront_of_unstableBranch`, which then returns a strictly
decreasing front. -/
example : IsFront 1 1 (azSpeed 1 1) (azWave 1 1 1) (azWaveDeriv 1 1 1) ∧
    StrictAnti (azWave 1 1 1) := by
  obtain ⟨hW, hb, h1, -⟩ := isFront_azWave (D := 1) (r := 1) (C := 1) one_pos one_pos one_pos
  exact isFront_of_unstableBranch one_pos one_pos (two_mul_sqrt_lt_azSpeed one_pos one_pos).le
    hW (fun z _ => ⟨(hb z).1, (hb z).2, azWaveDeriv_neg z⟩) h1 tendsto_azWaveDeriv

/-- The packaged existence statement at the Ablowitz–Zeppetella speed. -/
example : ∃ U V : ℝ → ℝ, IsFront 1 1 (azSpeed 1 1) U V ∧ StrictAnti U := by
  obtain ⟨hW, hb, h1, -⟩ := isFront_azWave (D := 1) (r := 1) (C := 1) one_pos one_pos one_pos
  exact exists_isFront_of_global_unstableBranch one_pos one_pos
    (two_mul_sqrt_lt_azSpeed one_pos one_pos).le ⟨azWave 1 1 1, azWaveDeriv 1 1 1, hW,
      fun z _ => ⟨(hb z).1, (hb z).2, azWaveDeriv_neg z⟩, h1, tendsto_azWaveDeriv⟩

/-- The front enters the triangle, stays there on `[z₀, ∞)` (noncompact interval), is
equi-Lipschitz there for the speed bound `c₁ = 3`, and the speed-limit theorem applies to the
constant sequence. -/
example : ∃ z₀ : ℝ, (∀ t ∈ Ici z₀, (azWave 1 1 1 t, azWaveDeriv 1 1 1 t) ∈
      trappingTriangle 1 (azSpeed 1 1)) ∧
    |azWave 1 1 1 (z₀ + 1) - azWave 1 1 1 z₀| ≤ 3 / (2 * 1) * |z₀ + 1 - z₀| ∧
    ∀ s ∈ Ioo z₀ (z₀ + 1), HasDerivAt (azWave 1 1 1) (azWaveDeriv 1 1 1 s) s := by
  obtain ⟨hW, hb, h1, -⟩ := isFront_azWave (D := 1) (r := 1) (C := 1) one_pos one_pos one_pos
  have hc := (two_mul_sqrt_lt_azSpeed (D := 1) (r := 1) one_pos one_pos).le
  have hc0 := (pos_and_sq_of_two_sqrt_le one_pos one_pos hc).1
  have hc3 : azSpeed 1 1 ≤ 3 := by
    rw [azSpeed, one_mul, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 6), Real.sqrt_one]
    have h6 : (2 : ℝ) ≤ √6 := by
      rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq two_pos.le]]
      exact Real.sqrt_le_sqrt (by norm_num)
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨z₀, hz₀⟩ := (eventually_mem_trappingTriangle_atBot one_pos hc0
    (fun z _ => ⟨(hb z).2, azWaveDeriv_neg z⟩) h1 tendsto_azWaveDeriv).exists
  have hT := mapsTo_trappingTriangle_Ici one_pos one_pos hc (fun z _ => hW z) hz₀
  have hTI : ∀ z ∈ Icc z₀ (z₀ + 1), (azWave 1 1 1 z, azWaveDeriv 1 1 1 z) ∈
      trappingTriangle 1 (azSpeed 1 1) := fun z hz => hT z hz.1
  refine ⟨z₀, hT, (abs_sub_le_of_mapsTo_trappingTriangle one_pos one_pos hc0 hc3
    (fun z _ => hW z) hTI ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩).1, fun s hs => ?_⟩
  exact (hasDerivAt_of_tendsto_of_mapsTo_trappingTriangle (c₁ := 3) (cs := fun _ => azSpeed 1 1)
    (Us := fun _ => azWave 1 1 1) (Vs := fun _ => azWaveDeriv 1 1 1) one_pos one_pos
    (fun _ => hc0) (fun _ => hc3) tendsto_const_nhds (fun _ z _ => hW z) (fun _ => hTI)
    (fun _ _ => tendsto_const_nhds) (fun _ _ => tendsto_const_nhds) s hs).1

/-- The trapped front converges to the node `(0, 0)` on the noncompact interval. -/
example : Tendsto (azWave 1 1 1) atTop (𝓝 0) := by
  obtain ⟨hW, hb, h1, -⟩ := isFront_azWave (D := 1) (r := 1) (C := 1) one_pos one_pos one_pos
  have hc := (two_mul_sqrt_lt_azSpeed (D := 1) (r := 1) one_pos one_pos).le
  have hc0 := (pos_and_sq_of_two_sqrt_le one_pos one_pos hc).1
  obtain ⟨z₀, hz₀⟩ := (eventually_mem_trappingTriangle_atBot one_pos hc0
    (fun z _ => ⟨(hb z).2, azWaveDeriv_neg z⟩) h1 tendsto_azWaveDeriv).exists
  exact (tendsto_zero_of_mapsTo_trappingTriangle one_pos one_pos hc0 (fun z _ => hW z)
    (mapsTo_trappingTriangle_Ici one_pos one_pos hc (fun z _ => hW z) hz₀)).1

/-- Non-vacuity of the continuation theorem: the Ablowitz–Zeppetella wave restricted to `z < 0`
satisfies its hypotheses (which are the unstable-branch properties). -/
example : ∃ U V : ℝ → ℝ, IsFront 1 1 (azSpeed 1 1) U V ∧ StrictAnti U := by
  obtain ⟨hW, hb, h1, -⟩ := isFront_azWave (D := 1) (r := 1) (C := 1) one_pos one_pos one_pos
  exact exists_isFront_of_unstableBranch one_pos one_pos
    (two_mul_sqrt_lt_azSpeed one_pos one_pos).le ⟨azWave 1 1 1, azWaveDeriv 1 1 1,
      fun z _ => hW z, fun z _ => ⟨(hb z).1, (hb z).2, azWaveDeriv_neg z⟩, h1,
      tendsto_azWaveDeriv⟩

end MathlibExtTest.Analysis.ODE.PlanarShooting.InvariantRegion
