/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/PDE/RadialSymmetry.lean` (leanprover/lean-eval), at commit
38361be884302c7edce1908c4aef8296eb2cb27e, problem `semilinear_poisson_radial_symmetry`
(manifest `manifests/problems/semilinear_poisson_radial_symmetry.toml`, rev 1,
submitter Yongxi Lin): the definition `SolvesSemilinearPoisson` and the statement of
`semilinear_poisson_radial_symmetry`, with their docstrings from
`WantedExt/Analysis/RadialSymmetryWanted.lean`.
Copyright 2026 Lean FRO, LLC.
Authors: Yongxi Lin
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). The original eval problem was converted
to a wanted theorem and then proved. The declarations were placed in the
`MathlibExt.Analysis.RadialSymmetryWanted` namespace and moved from the wanted module with their
names, statements and current docstrings preserved.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Topology.TietzeExtension
import MathlibExt.Analysis.Complex.LogNormHarmonicPlane
import MathlibExt.Analysis.PDE.HeatKernel

/-!
# Radial symmetry for a semilinear Poisson equation

Suppose `u` is a positive solution to a semilinear Poisson PDE:

  `-Δ u = f(u)` in the open unit ball,
  `u = 0` on the boundary.

For Lipschitz `f`, every `C^2` solution on the closed ball is radial and
strictly decreasing as a function of the radius.

The proof reflects the solution across parallel hyperplanes. A quadratic barrier establishes
comparison in a narrow slab and a Gaussian barrier gives strict comparison in the interior of a
cap. Compactness then lets the reflecting plane move to the center of the ball.
-/

@[expose] public section

open InnerProductSpace Metric Set Filter Topology Laplacian
open scoped NNReal
open MathlibExt.Analysis.PDE.HeatKernel MathlibExt.Analysis.PDE.LaplaceMaximumPrinciple
open MathlibExt.Analysis.Complex.LogNormHarmonicPlaneWanted (laplacian_comp_linearIsometryEquiv)

namespace MathlibExt.Analysis.RadialSymmetryWanted.Analysis.PDE

set_option linter.dupNamespace false in
/-- **Semilinear Poisson problem on the unit ball.** Let $n$ be a natural number, let
$f : \mathbb{R} \to \mathbb{R}$, and let $u : \mathbb{R}^n \to \mathbb{R}$ be a function on
Euclidean space. Then $u$ solves the semilinear Poisson problem for $f$ if
$-\Delta u(x) = f(u(x))$ for every $x$ in the open unit ball and $u(x) = 0$ for every $x$ on the
unit sphere.

The definition imposes no differentiability on $u$; regularity is assumed separately where it is
needed. -/
def SolvesSemilinearPoisson {n : ℕ} (f : ℝ → ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  (∀ x ∈ ball 0 1, -Laplacian.laplacian u x = f (u x)) ∧ ∀ x ∈ sphere 0 1, u x = 0

section Comparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem exists_gaussian_barrier (a : E) {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K) :
    ∃ b : E → ℝ, ContDiff ℝ 2 b ∧ (∀ x, 0 < b x) ∧
      (∀ x y, b x ≤ b y ↔ dist y a ≤ dist x a) ∧
      ∀ x, r ≤ dist x a → K * b x < Δ b x := by
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 ≤ n := Nat.cast_nonneg _
  -- Choose the heat-kernel scale so its Laplacian dominates the zeroth-order term.
  let t := min (r ^ 2 / (2 * (n + 1))) (1 / (2 * (K + 1)))
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have hscale : 2 * t * (n + 1) ≤ r ^ 2 := by
    have h := (le_div_iff₀ (show 0 < 2 * (n + 1) by positivity)).mp
      (min_le_left (r ^ 2 / (2 * (n + 1))) (1 / (2 * (K + 1))))
    convert h using 1; ring
  have hKscale : K < 1 / (2 * t) := by
    have h := (le_div_iff₀ (show 0 < 2 * (K + 1) by positivity)).mp
      (min_le_right (r ^ 2 / (2 * (n + 1))) (1 / (2 * (K + 1))))
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
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
  refine ⟨b, hb, hbpos, hble, fun x hx => ?_⟩
  have htranslate : Δ b x = Δ (heatKernel E t) (x - a) := by
    simp only [b, laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_comp_sub]
  have hratio : (n + 1) / (2 * t) ≤ dist x a ^ 2 / (4 * t ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hs := hscale.trans ((sq_le_sq₀ hr.le dist_nonneg).mpr hx)
    nlinarith [mul_le_mul_of_nonneg_right hs (show 0 ≤ 2 * t by positivity)]
  rw [htranslate, laplacian_heatKernel ht, ← dist_eq_norm]
  change K * b x < b x * (dist x a ^ 2 / (4 * t ^ 2) - n / (2 * t))
  rw [mul_comm K, mul_lt_mul_iff_right₀ (hbpos x)]
  linarith [add_div n 1 (2 * t)]

private theorem eq_zero_of_zero_mem_ball {D U : Set E} {w : E → ℝ} {K : ℝ}
    (hD : IsCompact D) (hUD : U ⊆ D) (hU : IsOpen U) (hK : 0 ≤ K)
    (hc : ContinuousOn w D) (hd : ∀ x ∈ U, ContDiffAt ℝ 2 w x)
    (hΔ : ∀ x ∈ U, K * w x ≤ Δ w x) (hw : ∀ x ∈ D, w x ≤ 0)
    {a z : E} {R : ℝ} (hz : z ∈ ball a R) (hball : ball a R ⊆ U) (hz0 : w z = 0) :
    w a = 0 := by
  have ha := hball (mem_ball_self (lt_of_le_of_lt dist_nonneg (mem_ball.mp hz)))
  apply (hw a (hUD ha)).eq_of_not_lt
  intro hlt
  obtain ⟨m, ham, hmz⟩ := exists_between hlt
  obtain ⟨r, hr, hrm⟩ := Metric.mem_nhds_iff.mp
    ((hd a ha).continuousAt (Iio_mem_nhds ham))
  obtain ⟨b, hb, hbpos, hble, hbΔ⟩ := exists_gaussian_barrier a hr hK
  -- The perturbation stays negative in the small ball around a and is positive at z.
  let ε := -m / b a
  have hε : 0 < ε := div_pos (neg_pos.mpr hmz) (hbpos a)
  have hεa : ε * b a = -m := div_mul_cancel₀ _ (hbpos a).ne'
  let v := w + ε • b
  obtain ⟨x, hx, hvmax⟩ := hD.exists_isMaxOn ⟨z, hUD (hball hz)⟩
    (f := v) (hc.add (hb.continuous.continuousOn.const_smul ε))
  have hvxz : w z + ε * b z ≤ w x + ε * b x := hvmax (hUD (hball hz))
  have hwx : w x ≤ 0 := hw x hx
  have hvpos : 0 < w x + ε * b x := by
    rw [hz0, zero_add] at hvxz
    exact (mul_pos hε (hbpos z)).trans_le hvxz
  have hxz : dist x a ≤ dist z a := (hble z x).mp
    ((mul_le_mul_iff_right₀ hε).mp (by linarith))
  have hxU := hball (mem_ball.mpr (hxz.trans_lt (mem_ball.mp hz)))
  have hxr : r ≤ dist x a := by
    by_contra! h
    have hxm : w x < m := hrm (mem_ball.mpr h)
    have hba := (hble x a).mpr (by simp)
    linarith [mul_le_mul_of_nonneg_left hba hε.le]
  have hloc := hvmax.isLocalMax (mem_of_superset (hU.mem_nhds hxU) hUD)
  have hεb : ContDiffAt ℝ 2 (ε • b) x := hb.contDiffAt.const_smul ε
  have hneg : Δ v x ≤ 0 := laplacian_nonpos_of_isLocalMax ((hd x hxU).add hεb) hloc
  dsimp only [v] at hneg
  rw [(hd x hxU).laplacian_add hεb, laplacian_smul ε hb.contDiffAt, smul_eq_mul] at hneg
  nlinarith [hΔ x hxU, mul_lt_mul_of_pos_left (hbΔ x hxr) hε,
    mul_nonneg hK hvpos.le]

private theorem eq_zero_of_zero_on_preconnected {D U : Set E} {w : E → ℝ} {K : ℝ}
    (hD : IsCompact D) (hUD : U ⊆ D) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hK : 0 ≤ K) (hc : ContinuousOn w D) (hd : ∀ x ∈ U, ContDiffAt ℝ 2 w x)
    (hΔ : ∀ x ∈ U, K * w x ≤ Δ w x) (hw : ∀ x ∈ D, w x ≤ 0)
    {z : E} (hz : z ∈ U) (hz0 : w z = 0) :
    ∀ x ∈ closure U, w x = 0 := by
  let A := {x | x ∈ U ∧ w x = 0}
  have hAo : IsOpen A := by
    refine Metric.isOpen_iff.mpr fun x ⟨hxU, hx0⟩ => ?_
    obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU x hxU
    refine ⟨R / 2, by positivity, fun a ha => ?_⟩
    have hball : ball a (R / 2) ⊆ U :=
      (ball_subset_ball' (by linarith [mem_ball.mp ha] : R / 2 + dist a x ≤ R)).trans hRU
    exact ⟨hball (mem_ball_self (by positivity)),
      eq_zero_of_zero_mem_ball hD hUD hU hK hc hd hΔ hw
        (mem_ball_comm.mp ha) hball hx0⟩
  have hAeq : EqOn w (fun _ => 0) A := fun _ hx => hx.2
  have hsub := hconn.subset_of_closure_inter_subset hAo ⟨z, hz, hz, hz0⟩
    (fun x ⟨hx, hxU⟩ => ⟨hxU,
      (hd x hxU).continuousAt.continuousWithinAt.eq_const_of_mem_closure hx hAeq⟩)
  exact (hAeq.mono hsub).of_subset_closure
    (hc.mono (closure_minimal hUD hD.isClosed)) continuousOn_const subset_closure Subset.rfl

omit [FiniteDimensional ℝ E] in
private theorem contDiff_inner_sub_sq (e : E) (a : ℝ) :
    ContDiff ℝ 2 (fun x : E => (inner ℝ e x - a) ^ 2) :=
  ((innerSL ℝ e).contDiff.sub contDiff_const).pow 2

private theorem laplacian_inner_sub_sq (e : E) (a : ℝ) (z : E) :
    Δ (fun x : E => (inner ℝ e x - a) ^ 2) z = 2 * ‖e‖ ^ 2 := by
  have hc : ContDiff ℝ 2 (fun x : E => (inner ℝ e x - a) ^ 2) := contDiff_inner_sub_sq e a
  have hdir (v : E) :
      iteratedFDeriv ℝ 2 (fun x : E => (inner ℝ e x - a) ^ 2) z ![v, v] =
        2 * (inner ℝ e v) ^ 2 := by
    rw [iteratedFDeriv_two_apply_eq_deriv_deriv hc.contDiffAt v]
    simp only [inner_add_right, real_inner_smul_right]
    have h1 (t : ℝ) :
        HasDerivAt (fun s : ℝ => (inner ℝ e z + s * inner ℝ e v - a) ^ 2)
          (2 * (inner ℝ e z + t * inner ℝ e v - a) * inner ℝ e v) t := by
      change HasDerivAt ((fun s : ℝ => inner ℝ e z + s * inner ℝ e v - a) ^ 2) _ _
      simpa using ((((hasDerivAt_id t).mul_const (inner ℝ e v)).const_add
        (inner ℝ e z)).sub_const a).pow 2
    have hderiv : deriv (fun s : ℝ => (inner ℝ e z + s * inner ℝ e v - a) ^ 2) =
        fun t => 2 * (inner ℝ e z + t * inner ℝ e v - a) * inner ℝ e v :=
      funext fun t => (h1 t).deriv
    rw [hderiv]
    have h2 := (((((hasDerivAt_id (0 : ℝ)).mul_const (inner ℝ e v)).const_add
      (inner ℝ e z)).sub_const a).const_mul 2).mul_const (inner ℝ e v)
    exact h2.deriv.trans (by ring)
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp_rw [hdir, ← Finset.mul_sum, OrthonormalBasis.sum_sq_inner_left]

private theorem nonneg_of_slab {D U : Set E} {w : E → ℝ} {K a b : ℝ} {e : E}
    (he : ‖e‖ = 1) (hK : 0 ≤ K) (hab : (K + 1) * (b - a) ^ 2 < 1)
    (hD : IsCompact D) (hUD : U ⊆ D) (hU : IsOpen U)
    (hs : ∀ x ∈ D, inner ℝ e x ∈ Icc a b)
    (hc : ContinuousOn w D) (hd : ∀ x ∈ U, ContDiffAt ℝ 2 w x)
    (hΔ : ∀ x ∈ U, Δ w x ≤ K * |w x|)
    (hbound : ∀ x ∈ D, x ∉ U → 0 ≤ w x) :
    ∀ x ∈ D, 0 ≤ w x := by
  intro y hy
  by_contra! hyneg
  obtain ⟨z, hz, hzmin⟩ := hD.exists_isMinOn ⟨y, hy⟩ hc
  -- The quadratic has amplitude smaller than the size of the negative minimum.
  let M := -w z
  have hM : 0 < M := neg_pos.mpr ((hzmin hy : w z ≤ w y).trans_lt hyneg)
  let c := M * (K + 1)
  have hcp : 0 < c := by dsimp [c]; positivity
  let p := fun x : E => (inner ℝ e x - a) ^ 2
  have hp : ContDiff ℝ 2 p := contDiff_inner_sub_sq e a
  let v := -w + c • p
  obtain ⟨x, hx, hxmax⟩ := hD.exists_isMaxOn ⟨y, hy⟩
    (f := v) (hc.neg.add (hp.continuous.continuousOn.const_smul c))
  have hvx : M ≤ v x := le_trans (le_add_of_nonneg_right (by
    change 0 ≤ c * p z
    dsimp [p]
    positivity)) (hxmax hz)
  have hpx : c * p x < M := by
    have h1 := (hs x hx).1
    have h2 := (hs x hx).2
    have hsq := (sq_le_sq₀ (sub_nonneg.mpr h1) (by linarith)).mpr
      (show inner ℝ e x - a ≤ b - a by linarith)
    calc
      c * p x ≤ c * (b - a) ^ 2 := mul_le_mul_of_nonneg_left hsq hcp.le
      _ = M * ((K + 1) * (b - a) ^ 2) := by simp only [c, mul_assoc]
      _ < M := by simpa using mul_lt_mul_of_pos_left hab hM
  change M ≤ -w x + c * p x at hvx
  have hneg : w x < 0 := by linarith
  have hxU : x ∈ U := by
    by_contra hn
    exact hneg.not_ge (hbound x hx hn)
  have hloc := hxmax.isLocalMax (mem_of_superset (hU.mem_nhds hxU) hUD)
  have hpc : ContDiffAt ℝ 2 (c • p) x := hp.contDiffAt.const_smul c
  have hcrit : Δ v x ≤ 0 := laplacian_nonpos_of_isLocalMax ((hd x hxU).neg.add hpc) hloc
  dsimp only [v] at hcrit
  change Δ ((fun x => -w x) + c • p) x ≤ 0 at hcrit
  rw [(hd x hxU).neg.laplacian_add hpc, ← Pi.neg_def, laplacian_neg,
    laplacian_smul c hp.contDiffAt,
    show Δ p x = 2 * ‖e‖ ^ 2 from laplacian_inner_sub_sq e a x, he, one_pow] at hcrit
  have hupper : Δ w x ≤ K * M := by
    refine (hΔ x hxU).trans (mul_le_mul_of_nonneg_left ?_ hK)
    rw [abs_of_neg hneg]
    exact neg_le_neg (hzmin hx)
  change -Δ w x + c * (2 * 1) ≤ 0 at hcrit
  dsimp only [c] at hcrit
  nlinarith [mul_nonneg hM.le hK]

end Comparison

section MovingPlanes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private noncomputable def reflect (e : E) (ℓ : ℝ) (x : E) : E :=
  (ℝ ∙ e)ᗮ.reflection x + (2 * ℓ) • e

private theorem reflect_zero (e x : E) :
    reflect e 0 x = (ℝ ∙ e)ᗮ.reflection x := by simp [reflect]

private theorem reflect_apply {e : E} (he : ‖e‖ = 1) (ℓ : ℝ) (x : E) :
    reflect e ℓ x = x + (2 * (ℓ - inner ℝ e x)) • e := by
  rw [reflect, Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply,
    he]
  simp only [RCLike.ofReal_one, one_pow, div_one]
  module

private theorem norm_reflect_sq {e : E} (he : ‖e‖ = 1) (ℓ : ℝ) (x : E) :
    ‖reflect e ℓ x‖ ^ 2 = ‖x‖ ^ 2 - 4 * ℓ * (inner ℝ e x - ℓ) := by
  rw [reflect_apply he, norm_add_sq_real, norm_smul, Real.norm_eq_abs, he, mul_one, sq_abs,
    real_inner_smul_right, real_inner_comm x e]
  ring

private theorem reflect_mem_closedBall {e x : E} {ℓ : ℝ} (he : ‖e‖ = 1) (hℓ : 0 ≤ ℓ)
    (hx : x ∈ closedBall (0 : E) 1) (hproj : ℓ ≤ inner ℝ e x) :
    reflect e ℓ x ∈ closedBall (0 : E) 1 := by
  have h := norm_reflect_sq he ℓ x
  simp only [mem_closedBall, dist_zero_right] at hx ⊢
  have hsq := (sq_le_sq₀ (norm_nonneg x) zero_le_one).mpr hx
  nlinarith [mul_nonneg hℓ (sub_nonneg.mpr hproj), norm_nonneg (reflect e ℓ x)]

private theorem reflect_mem_ball {e x : E} {ℓ : ℝ} (he : ‖e‖ = 1) (hℓ : 0 ≤ ℓ)
    (hx : x ∈ ball (0 : E) 1) (hproj : ℓ ≤ inner ℝ e x) :
    reflect e ℓ x ∈ ball (0 : E) 1 := by
  have h := norm_reflect_sq he ℓ x
  simp only [mem_ball, dist_zero_right] at hx ⊢
  have hsq := (sq_lt_sq₀ (norm_nonneg x) zero_le_one).mpr hx
  nlinarith [mul_nonneg hℓ (sub_nonneg.mpr hproj), norm_nonneg (reflect e ℓ x)]

private theorem reflect_mem_ball_of_pos {e x : E} {ℓ : ℝ} (he : ‖e‖ = 1) (hℓ : 0 < ℓ)
    (hx : x ∈ closedBall (0 : E) 1) (hproj : ℓ < inner ℝ e x) :
    reflect e ℓ x ∈ ball (0 : E) 1 := by
  have h := norm_reflect_sq he ℓ x
  simp only [mem_closedBall, mem_ball, dist_zero_right] at hx ⊢
  have hsq := (sq_le_sq₀ (norm_nonneg x) zero_le_one).mpr hx
  nlinarith [mul_pos hℓ (sub_pos.mpr hproj), norm_nonneg (reflect e ℓ x)]

private theorem inner_le_one {e x : E} (he : ‖e‖ = 1) (hx : x ∈ closedBall (0 : E) 1) :
    inner ℝ e x ≤ 1 := by
  simpa [he] using (real_inner_le_norm e x).trans (by simpa only [he, one_mul, mem_closedBall,
    dist_zero_right] using hx : ‖e‖ * ‖x‖ ≤ 1)

variable [FiniteDimensional ℝ E] in
private theorem laplacian_reflect (u : E → ℝ) (e : E) (ℓ : ℝ) (x : E) :
    Δ (u ∘ reflect e ℓ) x = Δ u (reflect e ℓ x) := by
  let R := (ℝ ∙ e)ᗮ.reflection
  let v := fun y : E => u (y + (2 * ℓ) • e)
  change Δ (v ∘ R) x = Δ u (R x + (2 * ℓ) • e)
  rw [laplacian_comp_linearIsometryEquiv v R]
  simp only [Function.comp_apply, v, laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_comp_add_right]

private noncomputable def reflectionDiff (u : E → ℝ) (e : E) (ℓ : ℝ) (x : E) : ℝ :=
  u (reflect e ℓ x) - u x

private theorem continuous_reflectionDiff {u : E → ℝ} (hc : Continuous u) (e : E) :
    Continuous (fun p : ℝ × E => reflectionDiff u e p.1 p.2) := by
  have hR : Continuous fun p : ℝ × E => (ℝ ∙ e)ᗮ.reflection p.2 :=
    (LinearIsometryEquiv.continuous _).comp continuous_snd
  unfold reflectionDiff reflect
  fun_prop

omit [InnerProductSpace ℝ E] in
private theorem mem_sphere_of_closedBall_not_ball {x : E}
    (hc : x ∈ closedBall (0 : E) 1) (ho : x ∉ ball (0 : E) 1) :
    x ∈ sphere (0 : E) 1 :=
  mem_sphere.mpr (le_antisymm (mem_closedBall.mp hc) (le_of_not_gt (mt mem_ball.mpr ho)))

omit [InnerProductSpace ℝ E] in
private theorem solution_nonneg {u : E → ℝ} (hu_pos : ∀ x ∈ ball (0 : E) 1, 0 < u x)
    (hu_boundary : ∀ x ∈ sphere (0 : E) 1, u x = 0) :
    ∀ x ∈ closedBall (0 : E) 1, 0 ≤ u x := by
  intro x hx
  by_cases hi : x ∈ ball (0 : E) 1
  · exact (hu_pos x hi).le
  · rw [hu_boundary x (mem_sphere_of_closedBall_not_ball hx hi)]

private theorem reflectionDiff_nonneg_on_edge {u : E → ℝ} {e x : E} {ℓ : ℝ} (he : ‖e‖ = 1)
    (hℓ : 0 ≤ ℓ) (hx : x ∈ closedBall (0 : E) 1) (hx' : ℓ ≤ inner ℝ e x)
    (hu_pos : ∀ x ∈ ball (0 : E) 1, 0 < u x) (hu_boundary : ∀ x ∈ sphere (0 : E) 1, u x = 0)
    (hedge : x ∉ ball (0 : E) 1 ∨ inner ℝ e x = ℓ) :
    0 ≤ reflectionDiff u e ℓ x := by
  rcases hedge with hout | hplane
  · rw [reflectionDiff, hu_boundary x (mem_sphere_of_closedBall_not_ball hx hout), sub_zero]
    exact solution_nonneg hu_pos hu_boundary _ (reflect_mem_closedBall he hℓ hx hx')
  · simp [reflectionDiff, reflect_apply he, hplane]

private theorem reflectionDiff_continuousOn {u : E → ℝ} {e : E} {ℓ : ℝ} (he : ‖e‖ = 1)
    (hℓ : 0 ≤ ℓ) (hu : ContinuousOn u (closedBall (0 : E) 1)) :
    ContinuousOn (reflectionDiff u e ℓ)
      (closedBall (0 : E) 1 ∩ {x | ℓ ≤ inner ℝ e x}) := by
  have hR : Continuous (reflect e ℓ) := (LinearIsometryEquiv.continuous _).add continuous_const
  have hm : MapsTo (reflect e ℓ) (closedBall (0 : E) 1 ∩ {x | ℓ ≤ inner ℝ e x})
      (closedBall 0 1) := fun _ hx => reflect_mem_closedBall he hℓ hx.1 hx.2
  exact (hu.comp hR.continuousOn hm).sub (hu.mono inter_subset_left)

private theorem reflectionDiff_c2 {u : E → ℝ} {e x : E} {ℓ : ℝ} (he : ‖e‖ = 1)
    (hℓ : 0 ≤ ℓ) (hx : x ∈ ball (0 : E) 1) (hx' : ℓ ≤ inner ℝ e x)
    (hu : ∀ x ∈ ball (0 : E) 1, ContDiffAt ℝ 2 u x) :
    ContDiffAt ℝ 2 (reflectionDiff u e ℓ) x := by
  have hR : ContDiff ℝ 2 (reflect e ℓ) :=
    ((ℝ ∙ e)ᗮ.reflection.toContinuousLinearEquiv.contDiff).add contDiff_const
  exact ((hu _ (reflect_mem_ball he hℓ hx hx')).comp x hR.contDiffAt).sub (hu _ hx)

variable [FiniteDimensional ℝ E]

private theorem reflectionDiff_laplacian {u : E → ℝ} {e x : E} {ℓ : ℝ} {f : ℝ → ℝ}
    {K : ℝ≥0} (he : ‖e‖ = 1) (hℓ : 0 ≤ ℓ) (hx : x ∈ ball (0 : E) 1)
    (hx' : ℓ ≤ inner ℝ e x) (hf : LipschitzWith K f)
    (hu : ∀ x ∈ ball (0 : E) 1, ContDiffAt ℝ 2 u x)
    (hPDE : ∀ x ∈ ball (0 : E) 1, -Δ u x = f (u x)) :
    Δ (reflectionDiff u e ℓ) x ≤ K * |reflectionDiff u e ℓ x| := by
  have hr := reflect_mem_ball he hℓ hx hx'
  have hR : ContDiff ℝ 2 (reflect e ℓ) :=
    ((ℝ ∙ e)ᗮ.reflection.toContinuousLinearEquiv.contDiff).add contDiff_const
  have h := ((hu _ hr).comp x hR.contDiffAt).laplacian_sub (hu _ hx)
  change Δ (reflectionDiff u e ℓ) x = Δ (u ∘ reflect e ℓ) x - Δ u x at h
  rw [h, laplacian_reflect]
  have hdiff := hf.dist_le_mul (u x) (u (reflect e ℓ x))
  simp only [Real.dist_eq, abs_sub_comm (u x) (u (reflect e ℓ x))] at hdiff
  have hle := (le_abs_self (f (u x) - f (u (reflect e ℓ x)))).trans hdiff
  change _ ≤ (K : ℝ) * |u (reflect e ℓ x) - u x|
  linarith [hPDE x hx, hPDE _ hr]

private theorem reflectionDiff_strict {u : E → ℝ} {e : E} {ℓ : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (he : ‖e‖ = 1) (hℓ : 0 < ℓ) (hf : LipschitzWith K f)
    (hc : ContinuousOn u (closedBall (0 : E) 1))
    (hd : ∀ x ∈ ball (0 : E) 1, ContDiffAt ℝ 2 u x)
    (hPDE : ∀ x ∈ ball (0 : E) 1, -Δ u x = f (u x))
    (hu_pos : ∀ x ∈ ball (0 : E) 1, 0 < u x) (hu_boundary : ∀ x ∈ sphere (0 : E) 1, u x = 0)
    (hw : ∀ x ∈ closedBall (0 : E) 1, ℓ < inner ℝ e x → 0 ≤ reflectionDiff u e ℓ x) :
    ∀ x ∈ closedBall (0 : E) 1, ℓ < inner ℝ e x → 0 < reflectionDiff u e ℓ x := by
  let D := closedBall (0 : E) 1 ∩ {x | ℓ ≤ inner ℝ e x}
  let U := ball (0 : E) 1 ∩ {x | ℓ < inner ℝ e x}
  have hproj : Continuous (inner ℝ e) := (innerSL ℝ e).continuous
  have hhalf : IsOpen {x | ℓ < inner ℝ e x} := isOpen_lt continuous_const hproj
  have hD : IsCompact D := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const hproj)
  have hUD : U ⊆ D := fun _ hx => ⟨ball_subset_closedBall hx.1, (show ℓ < inner ℝ e _ from hx.2).le⟩
  have hU : IsOpen U := isOpen_ball.inter hhalf
  have hconn : IsPreconnected U :=
    ((convex_ball _ _).inter
      (convex_halfSpace_gt ((innerSL ℝ e).toLinearMap.isLinear) _)).isPreconnected
  have hwD : ∀ x ∈ D, -(reflectionDiff u e ℓ x) ≤ 0 := by
    intro x hx
    rcases (show ℓ ≤ inner ℝ e x from hx.2).eq_or_lt with heq | hlt
    · simp [reflectionDiff, reflect_apply he, heq]
    · exact neg_nonpos.mpr (hw x hx.1 hlt)
  intro x hx hxt
  have hlt (y : E) (hy : y ∈ closedBall (0 : E) 1)
      (hy' : ℓ < inner ℝ e y) (hyb : y ∉ ball (0 : E) 1) :
      0 < reflectionDiff u e ℓ y := by
    rw [reflectionDiff, hu_boundary y (mem_sphere_of_closedBall_not_ball hy hyb), sub_zero]
    exact hu_pos _ (reflect_mem_ball_of_pos he hℓ hy hy')
  by_cases hxU : x ∈ ball (0 : E) 1
  · apply lt_of_le_of_ne (hw x hx hxt)
    intro hx0
    have hzero := eq_zero_of_zero_on_preconnected
      (w := -reflectionDiff u e ℓ) hD hUD hU hconn K.coe_nonneg
      (reflectionDiff_continuousOn he hℓ.le hc).neg
      (fun y hy => (reflectionDiff_c2 he hℓ.le hy.1 hy.2.le hd).neg)
      (fun y hy => by
        rw [laplacian_neg]
        change (K : ℝ) * -(reflectionDiff u e ℓ y) ≤ -Δ (reflectionDiff u e ℓ) y
        have h := reflectionDiff_laplacian he hℓ.le hy.1 hy.2.le hf hd hPDE
        rw [abs_of_nonneg (hw y (ball_subset_closedBall hy.1) hy.2)] at h
        linarith) hwD ⟨hxU, hxt⟩ (by simp [← hx0])
    have hec : e ∈ closedBall (0 : E) 1 := by simp [mem_closedBall, he]
    have het : ℓ < inner ℝ e e := by
      simpa [real_inner_self_eq_norm_sq, he] using hxt.trans_le (inner_le_one he hx)
    have heb : e ∉ ball (0 : E) 1 := by simp [mem_ball, he]
    have hecl : e ∈ closure U := by
      have hcl : e ∈ closure (ball (0 : E) 1) := by
        rwa [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
      exact hhalf.closure_inter ⟨hcl, het⟩
    have hcontra : -(reflectionDiff u e ℓ e) = 0 := hzero e hecl
    linarith [hlt e hec het heb]
  · exact hlt x hx hxt hxU


omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem eventually_pos_on_compact {T : Set E} {W : ℝ × E → ℝ} {ℓ : ℝ}
    (hT : IsCompact T) (hW : Continuous W) (hpos : ∀ x ∈ T, 0 < W (ℓ, x)) :
    ∀ᶠ μ in 𝓝 ℓ, ∀ x ∈ T, 0 < W (μ, x) := by
  let O := {p : ℝ × E | 0 < W p}
  have hO : IsOpen O := isOpen_lt continuous_const hW
  have htube : O ∈ (𝓝 ℓ) ×ˢ (𝓝ˢ T) :=
    hT.mem_prod_nhdsSet_of_forall fun x hx => by
      rw [← nhds_prod_eq]
      exact hO.mem_nhds (hpos x hx)
  obtain ⟨V, hV, V', hV', hsub⟩ := Filter.mem_prod_iff.mp htube
  filter_upwards [hV] with μ hμ
  intro x hx
  have hx' : x ∈ V' := (subset_of_mem_nhdsSet hV') hx
  have hp : (μ, x) ∈ V ×ˢ V' := ⟨hμ, hx'⟩
  exact hsub hp

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem isClosed_comparison_planes {B : Set E} {q : E → ℝ} {W : ℝ × E → ℝ}
    (hW : Continuous W) :
    IsClosed {ℓ | ∀ x ∈ B, ℓ < q x → 0 ≤ W (ℓ, x)} := by
  rw [← isOpen_compl_iff]
  refine isOpen_iff_mem_nhds.mpr fun ℓ hℓ => ?_
  change ¬ (∀ x ∈ B, ℓ < q x → 0 ≤ W (ℓ, x)) at hℓ
  push Not at hℓ
  obtain ⟨x, hx, hq, hw⟩ := hℓ
  have hWℓ : Continuous (fun μ : ℝ => W (μ, x)) := by
    change Continuous (W ∘ fun μ : ℝ => (μ, x))
    exact hW.comp (continuous_id.prodMk continuous_const)
  filter_upwards [Iio_mem_nhds hq, hWℓ.continuousAt (Iio_mem_nhds hw)] with μ hμ hwμ
  exact fun hμG => hwμ.not_ge (hμG x hx hμ)

private theorem reflectionDiff_nonneg {u : E → ℝ} {e : E} {f : ℝ → ℝ} {K : ℝ≥0}
    (he : ‖e‖ = 1) (hf : LipschitzWith K f)
    (hc : ContinuousOn u (closedBall (0 : E) 1))
    (hd : ∀ x ∈ ball (0 : E) 1, ContDiffAt ℝ 2 u x)
    (hPDE : ∀ x ∈ ball (0 : E) 1, -Δ u x = f (u x))
    (hu_pos : ∀ x ∈ ball (0 : E) 1, 0 < u x) (hu_boundary : ∀ x ∈ sphere (0 : E) 1, u x = 0) :
    ∀ ℓ ≥ 0, ∀ x ∈ closedBall (0 : E) 1, ℓ < inner ℝ e x → 0 ≤ reflectionDiff u e ℓ x := by
  let B := closedBall (0 : E) 1
  -- The extension makes the reflection difference jointly continuous in the plane and point.
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq (s := B) isClosed_closedBall
    ⟨fun x : B => u x, continuousOn_iff_continuous_domRestrict.mp hc⟩
  have hg_eq : EqOn g u B := fun x hx => DFunLike.congr_fun hg ⟨x, hx⟩
  let W (p : ℝ × E) := reflectionDiff g e p.1 p.2
  have hW : Continuous W := continuous_reflectionDiff g.continuous e
  have hsame (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (x : E) (hx : x ∈ B) (hproj : ℓ ≤ inner ℝ e x) :
      W (ℓ, x) = reflectionDiff u e ℓ x := by
    simp only [W, reflectionDiff, hg_eq (reflect_mem_closedBall he hℓ hx hproj), hg_eq hx]
  let G : Set ℝ := {ℓ | ∀ x ∈ B, ℓ < inner ℝ e x → 0 ≤ W (ℓ, x)}
  have hGc : IsClosed G := isClosed_comparison_planes hW
  let δ := 1 / (2 * ((K : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by nlinarith [K.coe_nonneg])
  have hδmul : (2 * ((K : ℝ) + 1)) * δ = 1 :=
    mul_div_cancel₀ 1 (by positivity)
  have hδsmall : ((K : ℝ) + 1) * δ ^ 2 < 1 := by
    have h := congrArg (fun a : ℝ => a * δ) hδmul
    change 2 * ((K : ℝ) + 1) * δ * δ = 1 * δ at h
    nlinarith only [h, hδ1]
  have hproj : Continuous (inner ℝ e) := (innerSL ℝ e).continuous
  have hnarrow (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hwidth : b - a ≤ δ)
      (hupper : ∀ x ∈ B, inner ℝ e x = b → 0 ≤ reflectionDiff u e a x) :
      ∀ x ∈ B, inner ℝ e x ∈ Icc a b → 0 ≤ reflectionDiff u e a x := by
    let D := B ∩ (inner ℝ e) ⁻¹' Icc a b
    let U := ball (0 : E) 1 ∩ (inner ℝ e) ⁻¹' Ioo a b
    have hD : IsCompact D := (isCompact_closedBall _ _).inter_right
      (isClosed_Icc.preimage hproj)
    have hUD : U ⊆ D := fun _ hx => ⟨ball_subset_closedBall hx.1, Ioo_subset_Icc_self hx.2⟩
    have hU : IsOpen U := isOpen_ball.inter (isOpen_Ioo.preimage hproj)
    have hsq := (sq_le_sq₀ (sub_nonneg.mpr hab.le) hδ.le).mpr hwidth
    have hw : ((K : ℝ) + 1) * (b - a) ^ 2 < 1 :=
      (mul_le_mul_of_nonneg_left hsq (by positivity)).trans_lt hδsmall
    have hbound (x : E) (hx : x ∈ D) (hn : x ∉ U) : 0 ≤ reflectionDiff u e a x := by
      by_cases hin : x ∈ ball (0 : E) 1
      · rcases hx.2.1.eq_or_lt with hxa | hxa
        · exact reflectionDiff_nonneg_on_edge he ha hx.1 hx.2.1 hu_pos hu_boundary (Or.inr hxa.symm)
        · exact hupper x hx.1 (hx.2.2.eq_of_not_lt (fun hxb => hn ⟨hin, hxa, hxb⟩))
      · exact reflectionDiff_nonneg_on_edge he ha hx.1 hx.2.1 hu_pos hu_boundary (Or.inl hin)
    exact fun x hx hx' => nonneg_of_slab he K.coe_nonneg hw hD hUD hU (fun _ hy => hy.2)
      ((reflectionDiff_continuousOn he ha hc).mono (fun _ hy => ⟨hy.1, hy.2.1⟩))
      (fun _ hy => reflectionDiff_c2 he ha hy.1 hy.2.1.le hd)
      (fun _ hy => reflectionDiff_laplacian he ha hy.1 hy.2.1.le hf hd hPDE) hbound x ⟨hx, hx'⟩
  -- Strict comparison keeps the portion away from the plane positive as the plane moves.
  let A := Ioi (0 : ℝ) ∩ G
  have hAo : IsOpen A := by
    refine isOpen_iff_mem_nhds.mpr fun ℓ hℓ => ?_
    have hℓp : 0 < ℓ := hℓ.1
    have hgood : ∀ x ∈ B, ℓ < inner ℝ e x → 0 ≤ reflectionDiff u e ℓ x := by
      intro x hx hxl
      rw [← hsame ℓ hℓp.le x hx hxl.le]
      exact hℓ.2 x hx hxl
    have hstrict := reflectionDiff_strict he hℓp hf hc hd hPDE hu_pos hu_boundary hgood
    let b := ℓ + δ / 2
    let T := B ∩ {x | b ≤ inner ℝ e x}
    have hT : IsCompact T := (isCompact_closedBall _ _).inter_right
      (isClosed_le continuous_const hproj)
    have hb : ℓ < b := by dsimp [b]; linarith
    have hWpos := eventually_pos_on_compact hT hW (ℓ := ℓ) (fun x hx => by
      have hxb : b ≤ inner ℝ e x := hx.2
      have h := hb.trans_le hxb
      change 0 < W (ℓ, x)
      rw [hsame ℓ hℓp.le x hx.1 h.le]
      exact hstrict x hx.1 h)
    filter_upwards [Ioi_mem_nhds hℓp, Ioo_mem_nhds (show b - δ < ℓ by dsimp [b]; linarith) hb,
      hWpos] with μ hμ hμ' hpos
    have hμp : 0 < μ := hμ
    have hbμ : μ < b := hμ'.2
    refine ⟨hμ, fun x hx hxμ => ?_⟩
    by_cases hxb : b ≤ inner ℝ e x
    · exact (hpos x ⟨hx, hxb⟩).le
    · rw [hsame μ hμp.le x hx hxμ.le]
      refine hnarrow μ b hμp.le hbμ (by linarith [hμ'.1]) ?_ x hx ⟨hxμ.le, le_of_not_ge hxb⟩
      intro y hy hyb
      rw [← hsame μ hμp.le y hy (by linarith)]
      exact (hpos y ⟨hy, hyb.ge⟩).le
  have hsub : Ioi (0 : ℝ) ⊆ A := isPreconnected_Ioi.subset_of_closure_inter_subset
    hAo ⟨1, by norm_num, by norm_num, fun x hx hlt => ((inner_le_one he hx).not_gt hlt).elim⟩
    (fun ℓ hℓ => ⟨hℓ.2, (closure_minimal inter_subset_right hGc) hℓ.1⟩)
  have hG : Ici (0 : ℝ) ⊆ G := by
    rw [← closure_Ioi]
    exact closure_minimal (hsub.trans inter_subset_right) hGc
  intro ℓ hℓ x hx hxl
  rw [← hsame ℓ hℓ x hx hxl.le]
  exact hG hℓ x hx hxl

end MovingPlanes

set_option linter.dupNamespace false in
/-- **Radial symmetry of positive solutions of the semilinear Poisson problem.** Let $n \ge 1$,
let $f : \mathbb{R} \to \mathbb{R}$ be Lipschitz, and let $u : \mathbb{R}^n \to \mathbb{R}$ be a
function on Euclidean space that is $C^2$ on the closed unit ball $\overline{B}$. Suppose that $u$
solves the semilinear Poisson problem for $f$, that is, $-\Delta u = f(u)$ on the open unit ball
$B$ and $u = 0$ on the unit sphere, and that $u > 0$ on $B$. Then there is a function
$v : \mathbb{R} \to [0, \infty)$ that is strictly decreasing on $[0, 1]$ and satisfies
$u(x) = v(\|x\|)$ for every $x \in \overline{B}$.

Source: B. Gidas, W. M. Ni, and L. Nirenberg, Symmetry and related properties via the maximum
principle, Comm. Math. Phys. 68 (1979), 209-243. Also stated as Theorem 2 (Radial symmetry) in L. C.
Evans, Partial Differential Equations, Section 9 on nonvariational techniques. Via
leanprover/lean-eval@38361be, problem `semilinear_poisson_radial_symmetry`. -/
theorem semilinear_poisson_radial_symmetry {n : ℕ} (hn : 0 < n)
    {f : ℝ → ℝ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_lipschitz : ∃ K : ℝ≥0, LipschitzWith K f)
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1))
    (hu_solve : SolvesSemilinearPoisson f u)
    (hu_positive : ∀ x ∈ ball 0 1, 0 < u x) :
    ∃ v : ℝ → ℝ≥0,
      StrictAntiOn v (Set.Icc (0 : ℝ) 1) ∧
        ∀ x ∈ closedBall 0 1, u x = v ‖x‖ := by
  let E := EuclideanSpace ℝ (Fin n)
  let B := closedBall (0 : E) 1
  obtain ⟨K, hK⟩ := hf_lipschitz
  obtain ⟨hPDE, hboundary⟩ := hu_solve
  have hc : ContinuousOn u B := hu_c2.continuousOn
  have hd : ∀ x ∈ ball (0 : E) 1, ContDiffAt ℝ 2 u x :=
    fun x hx => (hu_c2.mono ball_subset_closedBall).contDiffAt (isOpen_ball.mem_nhds hx)
  have hnonneg := solution_nonneg hu_positive hboundary
  have hdiff (e : E) (he : ‖e‖ = 1) :=
    reflectionDiff_nonneg he hK hc hd hPDE hu_positive hboundary
  have hle (e : E) (he : ‖e‖ = 1) (x : E) (hx : x ∈ B) :
      u x ≤ u (reflect e 0 x) := by
    rcases lt_trichotomy 0 (inner ℝ e x) with hp | hz | hn
    · exact sub_nonneg.mp (hdiff e he 0 le_rfl x hx hp)
    · simp [reflect_apply he, ← hz]
    · have hne : ‖-e‖ = 1 := by simpa using he
      have hpos : 0 < inner ℝ (-e) x := by simpa using neg_pos.mpr hn
      have hsame : reflect (-e) 0 x = reflect e 0 x := by
        rw [reflect_apply hne, reflect_apply he, inner_neg_left]
        module
      rw [← hsame]
      exact sub_nonneg.mp (hdiff (-e) hne 0 le_rfl x hx hpos)
  have hinvariant (e : E) (he : ‖e‖ = 1) (x : E) (hx : x ∈ B) :
      u x = u (reflect e 0 x) := by
    have hxr : reflect e 0 x ∈ B := by
      simpa [B, reflect_zero, mem_closedBall] using hx
    exact (hle e he x hx).antisymm (by simpa [reflect_zero] using hle e he _ hxr)
  -- Reflection in the perpendicular bisector through the origin exchanges equal-radius points.
  have hradial (x y : E) (hx : x ∈ B) (hxy : ‖x‖ = ‖y‖) : u x = u y := by
    by_cases hsame : x = y
    · rw [hsame]
    let e := ‖x - y‖⁻¹ • (x - y)
    have hnz : ‖x - y‖ ≠ 0 := fun h => hsame (sub_eq_zero.mp (norm_eq_zero.mp h))
    have he : ‖e‖ = 1 := by
      dsimp only [e]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_mul_cancel₀ hnz]
    have hspan : (ℝ ∙ e) = ℝ ∙ (x - y) :=
      Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero hnz)) _
    simpa only [reflect_zero, hspan, Submodule.reflection_sub hxy] using hinvariant e he x hx
  let i : Fin n := ⟨0, hn⟩
  let e : E := EuclideanSpace.single i 1
  have he : ‖e‖ = 1 := EuclideanSpace.orthonormal_single.norm_eq_one i
  have hnsmul (r : ℝ) (hr : 0 ≤ r) : ‖r • e‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, he, mul_one]
  have hline (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) : r • e ∈ B := by
    simpa [B, mem_closedBall, hnsmul r hr.1] using hr.2
  have hstrict (r : ℝ) (hr : 0 < r) :=
    reflectionDiff_strict he hr hK hc hd hPDE hu_positive hboundary (hdiff e he r hr.le)
  refine ⟨fun r => Real.toNNReal (u (r • e)), ?_, ?_⟩
  · intro s hs t ht hst
    -- The plane halfway between the two points on the ray has positive offset.
    let m := (s + t) / 2
    have hm : 0 < m := by dsimp [m]; linarith [hs.1]
    have htproj : inner ℝ e (t • e) = t := by
      simp [real_inner_smul_right, he]
    have hmt : m < inner ℝ e (t • e) := by rw [htproj]; dsimp [m]; linarith
    have href : reflect e m (t • e) = s • e := by
      rw [reflect_apply he, htproj]
      dsimp only [m]
      module
    have hlt := hstrict m hm (t • e) (hline t ht) hmt
    rw [reflectionDiff, href, sub_pos] at hlt
    exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (hnonneg _ (hline t ht))).mpr hlt
  · intro x hx
    have hr : ‖x‖ ∈ Icc (0 : ℝ) 1 :=
      ⟨norm_nonneg _, by simpa [mem_closedBall] using hx⟩
    rw [Real.coe_toNNReal _ (hnonneg _ (hline _ hr))]
    exact hradial x (‖x‖ • e) hx (hnsmul _ (norm_nonneg _)).symm

end MathlibExt.Analysis.RadialSymmetryWanted.Analysis.PDE
