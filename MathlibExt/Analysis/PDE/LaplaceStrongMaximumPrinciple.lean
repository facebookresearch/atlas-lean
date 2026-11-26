/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import MathlibExt.Analysis.PDE.HeatKernel

/-!
# Strong maximum principle for harmonic functions

A real harmonic function attaining its maximum inside a bounded connected open set is constant
on its closure if it is continuous there. A translated Gaussian with positive Laplacian outside
a small ball shows that the maximum set is open.
-/

public section

namespace MathlibExt.Analysis.PDE.LaplaceMeanValueWanted

open InnerProductSpace Metric Set Filter Topology Laplacian
open MathlibExt.Analysis.PDE.HeatKernel MathlibExt.Analysis.PDE.LaplaceMaximumPrinciple

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A Gaussian centred at `a` decreases strictly with distance and has positive Laplacian
outside the ball of radius `r`. -/
private theorem exists_gaussian_barrier (a : E) {r : ℝ} (hr : 0 < r) :
    ∃ b : E → ℝ, ContDiff ℝ 2 b ∧ (∀ x, 0 < b x) ∧
      (∀ x y, b x ≤ b y ↔ dist y a ≤ dist x a) ∧ ∀ x, r ≤ dist x a → 0 < Δ b x := by
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 ≤ n := Nat.cast_nonneg _
  let t := r ^ 2 / (2 * (n + 1))
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hscale : 2 * t * (n + 1) = r ^ 2 := by
    dsimp [t]
    field_simp
  let b := fun x : E => heatKernel E t (x - a)
  have hb : ContDiff ℝ 2 b := by
    have hq : ContDiff ℝ 2 (fun x : E => ‖x - a‖ ^ 2) :=
      (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
    exact contDiff_const.mul (hq.neg.div_const _).exp
  have hbpos (x : E) : 0 < b x := heatKernel_pos ht _
  have hble (x y : E) : b x ≤ b y ↔ dist y a ≤ dist x a := by
    have hp : 0 < (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by positivity) _
    simp only [b, heatKernel, mul_le_mul_iff_right₀ hp, Real.exp_le_exp,
      div_le_div_iff_of_pos_right (show 0 < 4 * t by positivity), neg_le_neg_iff, ← dist_eq_norm]
    exact sq_le_sq₀ dist_nonneg dist_nonneg
  have hΔ (x : E) (hx : r ≤ dist x a) : 0 < Δ b x := by
    have htranslate : Δ b x = Δ (heatKernel E t) (x - a) := by
      simp only [b, laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_comp_sub]
    rw [htranslate, laplacian_heatKernel ht]
    apply mul_pos (heatKernel_pos ht _) (sub_pos.mpr _)
    rw [← dist_eq_norm, div_lt_div_iff₀ (by positivity) (by positivity)]
    have hs := (sq_le_sq₀ hr.le dist_nonneg).mpr hx
    change n * (4 * t ^ 2) < dist x a ^ 2 * (2 * t)
    nlinarith [mul_le_mul_of_nonneg_right (hscale.trans_le hs) ht.le]
  exact ⟨b, hb, hbpos, hble, hΔ⟩

/-- A ball contained in the domain and containing a maximum has the same value at its centre. -/
private theorem eq_center_of_max_mem_ball {U : Set E} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {u : E → ℝ} (hu : HarmonicOnNhd u U)
    (hc : ContinuousOn u (closure U)) {a z : E} {R : ℝ} (hz : z ∈ ball a R)
    (hball : ball a R ⊆ U) (hmax : IsMaxOn u (closure U) z) : u a = u z := by
  have ha := hball (mem_ball_self (lt_of_le_of_lt dist_nonneg (mem_ball.mp hz)))
  apply (hmax (subset_closure ha) : u a ≤ u z).eq_of_not_lt
  intro hlt
  obtain ⟨m, ham, hmz⟩ := exists_between hlt
  obtain ⟨r, hr, hrm⟩ := Metric.mem_nhds_iff.mp
    ((hu a ha).1.continuousAt (Iio_mem_nhds ham))
  obtain ⟨b, hb, hbpos, hble, hΔ⟩ := exists_gaussian_barrier a hr
  -- Scale the perturbation so the values on the small ball stay below the old maximum.
  let ε := (u z - m) / b a
  have hε : 0 < ε := div_pos (sub_pos.mpr hmz) (hbpos a)
  have hεa : ε * b a = u z - m := div_mul_cancel₀ _ (hbpos a).ne'
  let v := u + ε • b
  obtain ⟨x, hx, hvmax⟩ := hUb.isCompact_closure.exists_isMaxOn
    ⟨z, subset_closure (hball hz)⟩ (f := v) (hc.add (hb.continuous.continuousOn.const_smul ε))
  have hvxz : u z + ε * b z ≤ u x + ε * b x := hvmax (subset_closure (hball hz))
  have hux : u x ≤ u z := hmax hx
  have hxz : dist x a ≤ dist z a := (hble z x).mp (by nlinarith)
  have hxU := hball (mem_ball.mpr (hxz.trans_lt (mem_ball.mp hz)))
  have hxr : r ≤ dist x a := by
    by_contra! h
    have hxm : u x < m := hrm (mem_ball.mpr h)
    have hba := (hble x a).mpr (by simp)
    linarith [mul_le_mul_of_nonneg_left hba hε.le, mul_pos hε (hbpos z)]
  -- At this interior maximum of v its Laplacian would be both positive and nonpositive.
  have hloc := hvmax.isLocalMax (mem_of_superset (hU.mem_nhds hxU) subset_closure)
  have hd := (hu x hxU).1
  have hεb : ContDiffAt ℝ 2 (ε • b) x := hb.contDiffAt.const_smul ε
  have hneg : Δ (u + ε • b) x ≤ 0 := laplacian_nonpos_of_isLocalMax (hd.add hεb) hloc
  rw [hd.laplacian_add hεb, laplacian_smul ε hb.contDiffAt,
    (hu x hxU).2.self_of_nhds] at hneg
  exact (mul_pos hε (hΔ x hxr)).not_ge (by simpa using hneg)

/-- **Strong maximum principle for harmonic functions.** Let `U` be bounded, open and connected,
and let `u` be harmonic on `U` and continuous on `closure U`. If `u` attains its maximum over
`closure U` at a point of `U`, then `u` is constant on `closure U`. This is Strong Maximum
Principle 3.10 of M. Schmidt, *Partial Differential Equations*, lecture notes, Universität
Mannheim, HWS 2025, Chapter 3 (stated there for path-connected open sets, which for open subsets
of a normed space is the same as connected), and the case `aⁱʲ = δⁱʲ` of the Corollary in
Chapter IV.A.3 of L. C. Evans, *Entropy and Partial Differential Equations* (which assumes
`u ∈ C²(closure U)`). -/
theorem eqOn_closure_of_isMaxOn_harmonicOnNhd {U : Set E} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hconn : IsConnected U) {u : E → ℝ}
    (hu : HarmonicOnNhd u U) (hc : ContinuousOn u (closure U)) {x₀ : E} (hx₀ : x₀ ∈ U)
    (hmax : IsMaxOn u (closure U) x₀) : ∀ x ∈ closure U, u x = u x₀ := by
  let A := {z | z ∈ U ∧ u z = u x₀}
  have hAo : IsOpen A := by
    refine Metric.isOpen_iff.mpr fun z ⟨hzU, heq⟩ => ?_
    obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU z hzU
    refine ⟨R / 2, by positivity, fun a ha => ?_⟩
    have hball : ball a (R / 2) ⊆ U :=
      (ball_subset_ball' (by linarith [mem_ball.mp ha] : R / 2 + dist a z ≤ R)).trans hRU
    have hzmax : IsMaxOn u (closure U) z := fun x hx => heq ▸ hmax hx
    exact ⟨hball (mem_ball_self (by positivity)),
      (eq_center_of_max_mem_ball hU hUb hu hc (mem_ball_comm.mp ha) hball hzmax).trans heq⟩
  have hAeq : EqOn u (fun _ => u x₀) A := fun _ hx => hx.2
  have hsub := hconn.isPreconnected.subset_of_closure_inter_subset hAo ⟨x₀, hx₀, hx₀, rfl⟩
    (fun x ⟨hx, hxU⟩ => ⟨hxU,
      (hu x hxU).1.continuousAt.continuousWithinAt.eq_const_of_mem_closure hx hAeq⟩)
  exact fun _ hx => (hAeq.mono hsub).of_subset_closure hc continuousOn_const subset_closure
    Subset.rfl hx

end MathlibExt.Analysis.PDE.LaplaceMeanValueWanted
