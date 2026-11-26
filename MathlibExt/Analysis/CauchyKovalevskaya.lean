/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/CauchyKovalevskaya.lean` (leanprover/lean-eval), at commit
38361be884302c7edce1908c4aef8296eb2cb27e, for the model space and theorem statement.
Manifest: `manifests/problems/cauchy_kovalevskaya.toml`, rev 1, status archived.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison (problem submitter)
Licensed under the Apache License, Version 2.0 (the "License");
you may not use these portions except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). The evaluation problem was previously
converted to a Batteries wanted declaration. This file moves the model space and statement
from `WantedExt/Analysis/CauchyKovalevskayaWanted.lean` and supplies the proof.
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Cauchy–Kovalevskaya theorem

§32 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. For
analytic data `F`, `f`, `u₀`, the quasi-linear scalar Cauchy problem

  `uₜ(x, t) = F(x, t, u(x,t)) · ∇ₓu(x, t) + f(x, t, u(x, t))`,
  `u(x, 0) = u₀(x)`

has a unique local analytic solution near every point of the initial
hypersurface `t = 0`.

The statement uses only off-the-shelf mathlib (`AnalyticOnNhd`, `fderiv`,
`EuclideanSpace`); mathlib has no Cauchy–Kovalevskaya theorem. The PDE is
encoded through the Fréchet derivative: `fderiv ℝ u p (0, 1)` is `∂u/∂t`
and `fderiv ℝ u p (v, 0)` is the spatial directional derivative along `v`,
so `fderiv ℝ u p (F-data, 0)` is `F · ∇ₓu`. Locality and uniqueness are
folded into a single `∀ x₀, ∃ U …` statement.

The proof constructs characteristics for the field `(-F, 1, f)`. To see their joint analytic
dependence on time and the initial point, rescale a trajectory to the unit interval. Its
integral equation is analytic on the Banach space of continuous paths, and at time zero
the derivative of its residual with respect to the path is the identity. A second implicit
function recovers the initial spatial point from the current space-time coordinates.
-/

@[expose] public section

namespace MathlibExt.Analysis.CauchyKovalevskayaWanted.Analysis

open Set Filter MeasureTheory
open scoped Topology unitInterval ContDiff

set_option linter.dupNamespace false in
/-- **Model space $\mathbb{R}^d$ of the Cauchy–Kovalevskaya problem.** For a natural number $d$,
this is the real Euclidean space $\mathbb{R}^d$ of dimension $d$, with the Euclidean inner product
and norm. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable section

variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/- Lift a Taylor coefficient to paths by evaluating every input at the same time. -/
private def pathCoeffMap {n : ℕ} (c : X [×n]→L[ℝ] Y) :
    (Fin n → C(I, X)) →ₘₗ[ℝ] C(I, Y) where
  toFun m := ⟨fun s => c (fun i => m i s), c.cont.comp (continuous_pi fun i => (m i).continuous)⟩
  map_update_add' m i a b := by
    ext s
    change c (fun j => Function.update m i (a + b) j s) =
      c (fun j => Function.update m i a j s) + c (fun j => Function.update m i b j s)
    simpa only [Function.apply_update (fun _ (g : C(I, X)) => g s), ContinuousMap.add_apply]
      using c.map_update_add (fun j => m j s) i (a s) (b s)
  map_update_smul' m i a b := by
    ext s
    change c (fun j => Function.update m i (a • b) j s) =
      a • c (fun j => Function.update m i b j s)
    simpa only [Function.apply_update (fun _ (g : C(I, X)) => g s), ContinuousMap.smul_apply]
      using c.map_update_smul (fun j => m j s) i a (b s)

private lemma pathCoeff_bound {n : ℕ} (c : X [×n]→L[ℝ] Y) (m : Fin n → C(I, X)) :
    ‖pathCoeffMap c m‖ ≤ ‖c‖ * ∏ i, ‖m i‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro s
  apply (c.le_opNorm (fun i => m i s)).trans
  gcongr with i
  exact (m i).norm_coe_le_norm s

private def pathCoeff {n : ℕ} (c : X [×n]→L[ℝ] Y) : C(I, X) [×n]→L[ℝ] C(I, Y) :=
  (pathCoeffMap c).mkContinuous ‖c‖ (pathCoeff_bound c)

/- The lifted Taylor series converges in the uniform norm around a constant path. -/
private theorem analyticAt_path_comp [CompleteSpace Y] (g : C(X, Y)) {a : X}
    (hg : AnalyticAt ℝ g a) :
    AnalyticAt ℝ (fun y : C(I, X) => g.comp y) (ContinuousMap.const I a) := by
  obtain ⟨p, r, h⟩ := hg
  let q : FormalMultilinearSeries ℝ C(I, X) C(I, Y) := fun n => pathCoeff (p n)
  have hr : r ≤ q.radius := h.r_le.trans (FormalMultilinearSeries.radius_le_of_le
    (fun n => (pathCoeffMap (p n)).mkContinuous_norm_le (norm_nonneg _) _))
  refine ⟨q, r, hr, h.r_pos, fun {y} hy => ?_⟩
  have hsum := ((q.summable_norm_apply (Metric.eball_subset_eball hr hy)).of_norm).hasSum
  convert hsum using 1
  ext s
  apply HasSum.unique _ ((ContinuousMap.evalCLM ℝ s).hasSum hsum)
  change HasSum (fun n => p n fun _ => y s) (g (a + y s))
  apply h.hasSum
  rw [mem_eball_zero_iff] at hy ⊢
  exact lt_of_le_of_lt (ENNReal.coe_le_coe.mpr (show ‖y s‖₊ ≤ ‖y‖₊ from y.norm_coe_le_norm s)) hy

private abbrev clip (t : ℝ) : I := projIcc 0 1 zero_le_one t

/- Integration from zero to the variable upper endpoint on the unit interval. -/
private def primitive [CompleteSpace X] : C(I, X) →L[ℝ] C(I, X) :=
  LinearMap.mkContinuous
    { toFun := fun g => ⟨fun s => ∫ t in 0..(s : ℝ), g (clip t),
        (intervalIntegral.differentiable_integral_of_continuous
          (g.continuous.comp continuous_projIcc)).continuous.comp continuous_subtype_val⟩
      map_add' := fun g h => by
        ext s
        exact intervalIntegral.integral_add
          ((g.continuous.comp continuous_projIcc).intervalIntegrable _ _)
          ((h.continuous.comp continuous_projIcc).intervalIntegrable _ _)
      map_smul' := fun a g => by
        ext s
        exact intervalIntegral.integral_smul a _ } 1 (by
    intro g
    rw [one_mul]
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun s => ?_
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => g.norm_coe_le_norm
      (clip t))).trans
    simpa [abs_of_nonneg s.2.1] using mul_le_mul_of_nonneg_left s.2.2 (norm_nonneg g))

/- Solve an analytic equation whose partial derivative in the unknown is the identity. -/
private lemma analytic_implicit {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [CompleteSpace A] [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    {a : A} {b : B} {H : A × B → B} (h : AnalyticAt ℝ H (a, b))
    (hs : HasFDerivAt (fun y => H (a, y)) (ContinuousLinearMap.id ℝ B) b) :
    ∃ y : A → B, AnalyticAt ℝ y a ∧ y a = b ∧
      ∀ᶠ p in 𝓝 (a, b), (H p = H (a, b) ↔ y p.1 = p.2) := by
  have hd := h.contDiffAt (n := ω)
  have pinv : (fderiv ℝ H (a, b) ∘L ContinuousLinearMap.inr ℝ A B).IsInvertible := by
    have hinner := (hasFDerivAt_const (𝕜 := ℝ) a b).prodMk (hasFDerivAt_id b)
    have he := (h.differentiableAt.hasFDerivAt.comp b hinner).unique hs
    change fderiv ℝ H (a, b) ∘L ContinuousLinearMap.inr ℝ A B =
      ContinuousLinearMap.id ℝ B at he
    rw [he]
    exact ⟨ContinuousLinearEquiv.refl ℝ B, rfl⟩
  exact ⟨hd.implicitFunction (by simp) pinv,
    (hd.contDiffAt_implicitFunction (by simp) pinv).analyticAt,
    hd.implicitFunction_apply_self (by simp) pinv,
    hd.eventually_apply_eq_iff_implicitFunction (by simp) pinv⟩

omit [NormedSpace ℝ X] in
private lemma eventually_scaled {P : X × ℝ → Prop} {a : X}
    (h : ∀ᶠ p in 𝓝 (a, (0 : ℝ)), P p) :
    ∀ᶠ p : X × ℝ in 𝓝 (a, (0 : ℝ)), ∀ s : I, P (p.1, p.2 * s) := by
  obtain ⟨r, hr, H⟩ := Metric.eventually_nhds_iff_ball.mp h
  filter_upwards [Metric.ball_mem_nhds (a, (0 : ℝ)) hr] with p hp s
  apply H
  rw [← ball_prod_same] at hp ⊢
  refine ⟨hp.1, ?_⟩
  have ht := hp.2
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero] at ht ⊢
  rw [abs_mul, abs_of_nonneg s.2.1]
  exact (mul_le_of_le_one_right (abs_nonneg _) s.2.2).trans_lt ht

/- Local solutions of an analytic vector field depend analytically on initial point and time. -/
private lemma analytic_flow [CompleteSpace X] {a : X} (g : C(X, X)) (hg : AnalyticAt ℝ g a) :
    ∃ Φ : X × ℝ → X, AnalyticAt ℝ Φ (a, 0) ∧
      ∀ᶠ p : X × ℝ in 𝓝 (a, (0 : ℝ)),
        Φ (p.1, 0) = p.1 ∧ HasDerivAt (fun t => Φ (p.1, t)) (g (Φ p)) p.2 := by
  obtain ⟨ε, hε, b, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one
    (hg.contDiffAt (n := 1))
  obtain ⟨Φ, hΦ, hcont⟩ := (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hdom : Metric.closedBall a (r : ℝ) ×ˢ Icc (0 - ε) (0 + ε) ∈ 𝓝 (a, (0 : ℝ)) :=
    prod_mem_nhds (Metric.closedBall_mem_nhds _ (by exact_mod_cast hr))
      (Icc_mem_nhds (by linarith) (by linarith))
  have hΦa := (hΦ a (Metric.mem_closedBall_self r.2)).1
  have hflow : ∀ᶠ p : X × ℝ in 𝓝 (a, (0 : ℝ)),
      Φ (p.1, 0) = p.1 ∧ HasDerivAt (fun t => Φ (p.1, t)) (g (Φ p)) p.2 := by
    filter_upwards [hdom, (continuous_snd.tendsto (a, (0 : ℝ))).eventually
      (Ioo_mem_nhds (show 0 - ε < 0 by linarith) (show 0 < 0 + ε by linarith))]
      with p hp ht
    exact ⟨(hΦ _ hp.1).1, ((hΦ _ hp.1).2 _ hp.2).hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩
  refine ⟨Φ, ?_, hflow⟩
  -- After rescaling time, the Picard integral has the fixed domain [0, 1].
  let c := ContinuousLinearMap.const ℝ I (M := X)
  let H (q : (X × ℝ) × C(I, X)) := q.2 - q.1.2 • primitive (g.comp q.2) - c q.1.1
  have hH : AnalyticAt ℝ H ((a, 0), c a) := by
    let q₀ : (X × ℝ) × C(I, X) := ((a, 0), c a)
    have h1 : AnalyticAt ℝ (fun q : (X × ℝ) × C(I, X) => g.comp q.2) q₀ :=
      (analyticAt_path_comp g hg).comp_of_eq (x := q₀) analyticAt_snd rfl
    have h2 : AnalyticAt ℝ (fun q : (X × ℝ) × C(I, X) => primitive (g.comp q.2)) q₀ :=
      ((primitive (X := X)).analyticAt _).comp h1
    have htime : AnalyticAt ℝ (fun q : (X × ℝ) × C(I, X) => q.1.2) q₀ :=
      analyticAt_snd.comp analyticAt_fst
    have hstart : AnalyticAt ℝ (fun q : (X × ℝ) × C(I, X) => c q.1.1) q₀ :=
      (c.analyticAt _).comp (f := fun q : (X × ℝ) × C(I, X) => q.1.1)
        (analyticAt_fst.comp analyticAt_fst)
    exact (analyticAt_snd.sub (htime.smul h2)).sub hstart
  have hH0 : H ((a, 0), c a) = 0 := by simp [H]
  have hslice : HasFDerivAt (fun y => H ((a, 0), y)) (ContinuousLinearMap.id ℝ _) (c a) := by
    simpa [H] using (hasFDerivAt_id (c a)).sub_const (c a)
  obtain ⟨y, hy, _, heq⟩ := analytic_implicit hH hslice
  have hend := (ContinuousMap.evalCLM ℝ (1 : I) (M := X)).analyticAt _ |>.comp hy
  apply hend.congr
  -- Identify the implicit path with the rescaled Picard–Lindelöf solution.
  have hc : ContinuousAt Φ (a, 0) := (hcont _ (mem_of_mem_nhds hdom)).continuousAt hdom
  obtain ⟨δ, hδ, hiff⟩ := Metric.eventually_nhds_iff_ball.mp heq
  have hn : ∀ᶠ p in 𝓝 (a, (0 : ℝ)), Φ p ∈ Metric.ball a δ := by
    apply hc.eventually
    change Metric.ball a δ ∈ 𝓝 (Φ (a, (0 : ℝ)))
    rw [show Φ (a, (0 : ℝ)) = a from hΦa]
    exact Metric.ball_mem_nhds _ hδ
  filter_upwards [eventually_scaled hflow, eventually_scaled hn,
    Metric.ball_mem_nhds (a, (0 : ℝ)) hδ] with p hp hclose hnear
  let γ (s : ℝ) := Φ (p.1, p.2 * s)
  have hγ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivAt γ (p.2 • g (γ s)) s :=
    by simpa [γ, Function.comp_def] using (hp ⟨s, hs⟩).2.scomp s ((hasDerivAt_id' s).const_mul p.2)
  let w : C(I, X) := ⟨fun s => γ s, continuousOn_iff_continuous_domRestrict.mp
    (fun s hs => (hγ s hs).continuousAt.continuousWithinAt)⟩
  have hw : (p, w) ∈ Metric.ball ((a, 0), c a) δ := by
    rw [← ball_prod_same]
    exact ⟨hnear, (ContinuousMap.dist_lt_iff hδ).mpr hclose⟩
  have hHw : H (p, w) = 0 := by
    apply sub_eq_zero.mpr
    apply sub_eq_iff_eq_add.mpr
    ext s
    change γ s = p.1 + p.2 • ∫ t in 0..(s:ℝ), g (w (clip t))
    rw [← intervalIntegral.integral_smul]
    have hγ0 : γ 0 = p.1 := by simpa [γ] using (hp 0).1
    rw [← hγ0, ← sub_eq_iff_eq_add', eq_comm]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by
        rw [uIcc_of_le s.2.1] at ht
        exact ⟨ht.1, ht.2.trans s.2.2⟩
      change HasDerivAt γ (p.2 • g (γ (clip t))) t
      rw [clip, projIcc_of_mem zero_le_one ht']
      exact hγ t ht'
    · apply Continuous.intervalIntegrable
      exact continuous_const.smul (g.continuous.comp (w.continuous.comp continuous_projIcc))
  have he := (hiff _ hw).mp (hHw.trans hH0.symm)
  have hval := congrArg (fun z : C(I, X) => z 1) he
  change y p 1 = Φ (p.1, p.2 * (1 : I)) at hval
  simpa using hval

/- Start the characteristic curves on the graph of the initial data. -/
private lemma characteristics [CompleteSpace X] (F : X × ℝ × ℝ → X)
    (f : X × ℝ × ℝ → ℝ) (u₀ : X → ℝ)
    (hF : AnalyticOnNhd ℝ F univ) (hf : AnalyticOnNhd ℝ f univ)
    (hi : AnalyticOnNhd ℝ u₀ univ) (a : X) :
    ∃ (Y : X × ℝ → X) (Z : X × ℝ → ℝ),
      AnalyticAt ℝ Y (a, 0) ∧ AnalyticAt ℝ Z (a, 0) ∧
      ∀ᶠ p : X × ℝ in 𝓝 (a, (0 : ℝ)), Y (p.1, 0) = p.1 ∧ Z (p.1, 0) = u₀ p.1 ∧
        HasDerivAt (fun t => Y (p.1, t)) (-F (Y p, p.2, Z p)) p.2 ∧
        HasDerivAt (fun t => Z (p.1, t)) (f (Y p, p.2, Z p)) p.2 := by
  let V (q : X × ℝ × ℝ) := (-F q, (1 : ℝ), f q)
  have hV (q) : AnalyticAt ℝ V q :=
    (hF q trivial).neg.prod (analyticAt_const.prod (hf q trivial))
  let g : C(X × ℝ × ℝ, X × ℝ × ℝ) := ⟨V, continuous_iff_continuousAt.mpr
    (fun q => (hV q).continuousAt)⟩
  let initial (x : X) := (x, (0 : ℝ), u₀ x)
  let param (p : X × ℝ) := (initial p.1, p.2)
  have hp : AnalyticAt ℝ param (a, 0) := by
    exact (analyticAt_fst.prod (analyticAt_const.prod ((hi a trivial).comp analyticAt_fst))).prod
      analyticAt_snd
  obtain ⟨Φ, hΦ, hflow⟩ := analytic_flow g (hV (initial a))
  let W := Φ ∘ param
  have hW : AnalyticAt ℝ W (a, 0) := hΦ.comp_of_eq hp rfl
  have hODE : ∀ᶠ p : X × ℝ in 𝓝 (a, (0 : ℝ)), W (p.1, 0) = initial p.1 ∧
      HasDerivAt (fun t => W (p.1, t)) (V (W p)) p.2 := hp.continuousAt.tendsto.eventually hflow
  obtain ⟨r, hr, H⟩ := Metric.eventually_nhds_iff_ball.mp hODE
  refine ⟨fun p => (W p).1, fun p => (W p).2.2, analyticAt_fst.comp hW,
    analyticAt_snd.comp (analyticAt_snd.comp hW), ?_⟩
  filter_upwards [Metric.ball_mem_nhds (a, (0 : ℝ)) hr] with p hp'
  have hrect := ball_prod_same a (0 : ℝ) r
  have hpm := hrect ▸ hp'
  have ht (t : ℝ) (ht : t ∈ Metric.ball 0 r) := H (p.1, t) (hrect ▸ (⟨hpm.1, ht⟩ :
    (p.1, t) ∈ Metric.ball a r ×ˢ Metric.ball (0 : ℝ) r))
  let T (t : ℝ) := (W (p.1, t)).2.1
  have hT (t) (ht' : t ∈ Metric.ball 0 r) : HasDerivAt T 1 t :=
    by simpa [T, V] using (ht t ht').2.hasFDerivAt.snd.fst.hasDerivAt
  have hclock : T p.2 = p.2 := Metric.isOpen_ball.eqOn_of_deriv_eq Metric.isPreconnected_ball
    (fun t hm => (hT t hm).differentiableAt.differentiableWithinAt)
    differentiable_id.differentiableOn
    (fun t hm => (hT t hm).deriv.trans (hasDerivAt_id t).deriv.symm)
    (Metric.mem_ball_self hr) (congrArg (fun q : X × ℝ × ℝ => q.2.1) (H p hp').1) hpm.2
  have heq : W p = ((W p).1, p.2, (W p).2.2) := by
    change (W p).2.1 = p.2 at hclock
    rw [← hclock]
  have hd := (H p hp').2
  refine ⟨congrArg Prod.fst (H p hp').1, congrArg (fun q : X × ℝ × ℝ => q.2.2) (H p hp').1, ?_, ?_⟩
  · have h : HasDerivAt (fun t => (W (p.1, t)).1) (-F (W p)) p.2 :=
      by simpa [V] using hd.hasFDerivAt.fst.hasDerivAt
    rwa [heq] at h
  · have h : HasDerivAt (fun t => (W (p.1, t)).2.2) (f (W p)) p.2 :=
      by simpa [V] using hd.hasFDerivAt.snd.snd.hasDerivAt
    rwa [heq] at h

/- Invert the spatial characteristic map at fixed time, near the initial surface. -/
private lemma inverse_characteristics [CompleteSpace X] {Y : X × ℝ → X} {a : X}
    (hY : AnalyticAt ℝ Y (a, 0)) (h0 : ∀ᶠ x in 𝓝 a, Y (x, 0) = x) :
    ∃ A : X × ℝ → X, AnalyticAt ℝ A (a, 0) ∧ A (a, 0) = a ∧
      (∀ᶠ p : X × ℝ in 𝓝 (a, (0 : ℝ)), Y (A p, p.2) = p.1) ∧
      (∀ᶠ p : X × ℝ in 𝓝 (a, (0 : ℝ)), A (Y p, p.2) = p.1) := by
  let H (q : (X × ℝ) × X) := Y (q.2, q.1.2) - q.1.1
  have hH : AnalyticAt ℝ H ((a, 0), a) := by
    apply AnalyticAt.sub
    · exact hY.comp_of_eq (f := fun q : (X × ℝ) × X => (q.2, q.1.2))
        (analyticAt_snd.prod (analyticAt_snd.comp analyticAt_fst)) rfl
    · exact analyticAt_fst.comp analyticAt_fst
  have hs : HasFDerivAt (fun y => H ((a, 0), y)) (ContinuousLinearMap.id ℝ X) a := by
    apply ((hasFDerivAt_id a).sub_const a).congr_of_eventuallyEq
    filter_upwards [h0] with x hx
    simp [H, hx]
  have hbase : H ((a, 0), a) = 0 := by simp [H, h0.self_of_nhds]
  obtain ⟨A, hA, ha, h⟩ := analytic_implicit hH hs
  have h1 : Tendsto (fun p : X × ℝ => (p, A p)) (𝓝 (a, (0 : ℝ))) (𝓝 ((a, 0), a)) :=
    tendsto_id.prodMk_nhds (by simpa only [ha] using hA.continuousAt.tendsto)
  have hYt : Tendsto Y (𝓝 (a, 0)) (𝓝 a) := by
    simpa only [h0.self_of_nhds] using hY.continuousAt.tendsto
  have h2 : Tendsto (fun p : X × ℝ => ((Y p, p.2), p.1)) (𝓝 (a, (0 : ℝ))) (𝓝 ((a, 0), a)) :=
    (hYt.prodMk_nhds (continuous_snd.tendsto _)).prodMk_nhds (continuous_fst.tendsto _)
  refine ⟨A, hA, ha, ?_, ?_⟩
  · filter_upwards [h1.eventually h] with p hp
    simpa only [H, hbase, sub_eq_zero] using (hp.mpr rfl)
  · filter_upwards [h2.eventually h] with p hp
    apply hp.mp
    simp [hbase, H]

private lemma directional_eq (L : X × ℝ →L[ℝ] ℝ) (b : X) (c : ℝ) :
    L (0, 1) = L (b, 0) + c ↔ L (-b, 1) = c := by
  have he : (0, 1) = (b, (0 : ℝ)) + (-b, 1) := by simp
  rw [he, L.map_add, add_right_inj]

/- The graph of any solution contains the characteristic through each of its initial points. -/
private lemma agree_along_characteristic [CompleteSpace X] {F : X × ℝ × ℝ → X}
    {f : X × ℝ × ℝ → ℝ} {v : X × ℝ → ℝ} {y : ℝ → X} {z : ℝ → ℝ}
    (hF : AnalyticOnNhd ℝ F univ) (hf : AnalyticOnNhd ℝ f univ)
    (h0 : v (y 0, 0) = z 0) (hv : AnalyticAt ℝ v (y 0, 0))
    (hPDE : ∀ᶠ p in 𝓝 (y 0, (0 : ℝ)),
      fderiv ℝ v p (-F (p.1, p.2, v p), 1) = f (p.1, p.2, v p))
    (hODE : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt y (-F (y t, t, z t)) t ∧
      HasDerivAt z (f (y t, t, z t)) t) :
    (fun t => v (y t, t)) =ᶠ[𝓝 0] z := by
  let graph (p : X × ℝ) := (p.1, p.2, v p)
  let G (p : X × ℝ) := (-F (graph p), (1 : ℝ))
  let V (q : X × ℝ × ℝ) := (-F q, (1 : ℝ), f q)
  have hG : AnalyticAt ℝ G (y 0, 0) := ((hF _ trivial).comp (f := graph)
    (analyticAt_fst.prod (analyticAt_snd.prod hv))).neg.prod analyticAt_const
  obtain ⟨β, hβ0, ε, hε, hβ⟩ :=
    hG.contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  have hb : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt β (G (β t)) t := by
    filter_upwards [Ioo_mem_nhds (show 0 - ε < 0 by linarith) (show 0 < 0 + ε by linarith)]
      with t ht using hβ t ht
  have ht : Tendsto β (𝓝 0) (𝓝 (y 0, 0)) := by
    simpa only [hβ0] using hb.self_of_nhds.continuousAt.tendsto
  have hgraph : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (graph ∘ β) (V (graph (β t))) t := by
    filter_upwards [hb, ht.eventually hv.eventually_analyticAt, ht.eventually hPDE] with t hb' ha he
    have hx := (ContinuousLinearMap.fst ℝ X ℝ).hasFDerivAt.comp_hasDerivAt t hb'
    have htime := (ContinuousLinearMap.snd ℝ X ℝ).hasFDerivAt.comp_hasDerivAt t hb'
    have hz := ha.differentiableAt.hasFDerivAt.comp_hasDerivAt t hb'
    change HasDerivAt (v ∘ β) (fderiv ℝ v (β t) (-F (graph (β t)), 1)) t at hz
    rw [show fderiv ℝ v (β t) (-F (graph (β t)), 1) = _ from he] at hz
    exact hx.prodMk (htime.prodMk hz)
  let γ (t : ℝ) := (y t, t, z t)
  have hγ : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt γ (V (γ t)) t :=
    hODE.mono fun t ht => ht.1.prodMk ((hasDerivAt_id' t).prodMk ht.2)
  have he₀ : graph (β 0) = γ 0 := by simp [graph, γ, hβ0, h0]
  have hV : AnalyticAt ℝ V (γ 0) := (hF _ trivial).neg.prod (analyticAt_const.prod (hf _ trivial))
  obtain ⟨K, S, hS, hL⟩ := (hV.contDiffAt (n := 1)).exists_lipschitzOnWith
  have hB : ∀ᶠ t in 𝓝 0, (graph ∘ β) t ∈ S := hgraph.self_of_nhds.continuousAt.eventually
    (by change S ∈ 𝓝 (graph (β 0)); rwa [he₀])
  have heq := ODE_solution_unique_of_eventually (v := fun _ => V)
    (s := fun _ => S) (Eventually.of_forall fun _ => hL) (hgraph.and hB)
    (hγ.and (hγ.self_of_nhds.continuousAt.eventually hS)) he₀
  filter_upwards [heq] with t ht'
  have he : ∀ q : X × ℝ × ℝ, q = graph (β t) → v (q.1, q.2.1) = q.2.2 := by
    rintro _ rfl
    rfl
  exact he (γ t) ht'.symm

set_option linter.dupNamespace false in
/-- **Cauchy–Kovalevskaya theorem.** Let $d$ be a natural number, write $\mathbb{R}^d$ for real
Euclidean $d$-space, and let $F : \mathbb{R}^d \times \mathbb{R} \times \mathbb{R} \to
\mathbb{R}^d$, $f : \mathbb{R}^d \times \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ and
$u_0 : \mathbb{R}^d \to \mathbb{R}$ be real analytic at every point. Then for every
$x_0 \in \mathbb{R}^d$ there are an open set $U \subseteq \mathbb{R}^d \times \mathbb{R}$
containing $(x_0, 0)$ and a function $u : \mathbb{R}^d \times \mathbb{R} \to \mathbb{R}$, real
analytic on $U$, such that $u(x, 0) = u_0(x)$ whenever $(x, 0) \in U$ and

$$\partial_t u(x, t) = F(x, t, u(x, t)) \cdot \nabla_x u(x, t) + f(x, t, u(x, t))$$

for every $(x, t) \in U$, where $\partial_t u$ is the partial derivative of $u$ in $t$ and
$\nabla_x u$ is its gradient in $x$. Moreover, every function
$v : \mathbb{R}^d \times \mathbb{R} \to \mathbb{R}$ that is real analytic on $U$, satisfies
$v(x, 0) = u_0(x)$ whenever $(x, 0) \in U$, and satisfies the same equation at every point of
$U$ agrees with $u$ on $U$.

Source: A.-L. Cauchy (1842) and S. Kovalevskaya (1875). Listed as §32 in O. Knill, Some Fundamental
Theorems in Mathematics
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `cauchy_kovalevskaya`. -/
public theorem cauchy_kovalevskaya {d : ℕ}
    (F : E d × ℝ × ℝ → E d) (f : E d × ℝ × ℝ → ℝ) (u₀ : E d → ℝ)
    (_hF : AnalyticOnNhd ℝ F univ) (_hf : AnalyticOnNhd ℝ f univ)
    (_hu₀ : AnalyticOnNhd ℝ u₀ univ) (x₀ : E d) :
    ∃ (U : Set (E d × ℝ)) (u : E d × ℝ → ℝ),
      (x₀, (0 : ℝ)) ∈ U ∧ IsOpen U ∧ AnalyticOnNhd ℝ u U ∧
      (∀ x : E d, (x, (0 : ℝ)) ∈ U → u (x, 0) = u₀ x) ∧
      (∀ p ∈ U,
        fderiv ℝ u p ((0 : E d), (1 : ℝ)) =
          fderiv ℝ u p (F (p.1, p.2, u p), (0 : ℝ)) + f (p.1, p.2, u p)) ∧
      (∀ v : E d × ℝ → ℝ, AnalyticOnNhd ℝ v U →
        (∀ x : E d, (x, (0 : ℝ)) ∈ U → v (x, 0) = u₀ x) →
        (∀ p ∈ U,
          fderiv ℝ v p ((0 : E d), (1 : ℝ)) =
            fderiv ℝ v p (F (p.1, p.2, v p), (0 : ℝ)) + f (p.1, p.2, v p)) →
        ∀ p ∈ U, u p = v p) := by
  obtain ⟨Y, Z, hY, hZ, hchar⟩ := characteristics F f u₀ _hF _hf _hu₀ x₀
  have atZero : Tendsto (fun x : E d => (x, (0 : ℝ))) (𝓝 x₀) (𝓝 (x₀, (0 : ℝ))) :=
    tendsto_id.prodMk_nhds tendsto_const_nhds
  have hY0 : ∀ᶠ x in 𝓝 x₀, Y (x, 0) = x := (atZero.eventually hchar).mono fun _ h => h.1
  obtain ⟨A, hA, hA0, hright, hleft⟩ := inverse_characteristics hY hY0
  let Q (p : E d × ℝ) := (Y p, p.2)
  let B (p : E d × ℝ) := (A p, p.2)
  let u := Z ∘ B
  have hQa : Q (x₀, 0) = (x₀, 0) := Prod.ext hY0.self_of_nhds rfl
  have hBa : B (x₀, 0) = (x₀, 0) := Prod.ext hA0 rfl
  have hQ : AnalyticAt ℝ Q (x₀, 0) := hY.prod analyticAt_snd
  have hB : AnalyticAt ℝ B (x₀, 0) := hA.prod analyticAt_snd
  have hu : AnalyticAt ℝ u (x₀, 0) := hZ.comp_of_eq hB hBa
  have tQ : Tendsto Q (𝓝 (x₀, 0)) (𝓝 (x₀, 0)) := by simpa only [hQa] using hQ.continuousAt.tendsto
  have tB : Tendsto B (𝓝 (x₀, 0)) (𝓝 (x₀, 0)) := by simpa only [hBa] using hB.continuousAt.tendsto
  have hBQ : ∀ᶠ p in 𝓝 (x₀, (0 : ℝ)), B (Q p) = p := hleft.mono fun _ h => Prod.ext h rfl
  have hQB : ∀ᶠ p in 𝓝 (x₀, (0 : ℝ)), Q (B p) = p := hright.mono fun _ h => Prod.ext h rfl
  have hUZ : (u ∘ Q) =ᶠ[𝓝 (x₀, 0)] Z := hBQ.mono fun p he => congrArg Z he
  have hinit : ∀ᶠ x in 𝓝 x₀, u (x, 0) = u₀ x := by
    filter_upwards [atZero.eventually hUZ, atZero.eventually hchar] with x he hc
    change u (Y (x, 0), 0) = Z (x, 0) at he
    rw [hc.1] at he
    exact he.trans hc.2.1
  let P (p : E d × ℝ) := fderiv ℝ u p (0, 1) =
    fderiv ℝ u p (F (p.1, p.2, u p), 0) + f (p.1, p.2, u p)
  -- Differentiate the solution along a characteristic, then return to space-time coordinates.
  have hP : ∀ᶠ q in 𝓝 (x₀, (0 : ℝ)), P (Q q) := by
    filter_upwards [hchar, hUZ.eventually_nhds, tQ.eventually hu.eventually_analyticAt]
      with q hc he hd
    have hcurve := hc.2.2.1.prodMk (hasDerivAt_id' q.2)
    have hdu := hd.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq q.2 hcurve rfl
    have ht : Tendsto (fun t : ℝ => (q.1, t)) (𝓝 q.2) (𝓝 q) :=
      tendsto_const_nhds.prodMk_nhds tendsto_id
    have hz : HasDerivAt (fun t => u (Q (q.1, t))) (f (Y q, q.2, Z q)) q.2 :=
      hc.2.2.2.congr_of_eventuallyEq (ht.eventually he)
    have e : u (Q q) = Z q := he.self_of_nhds
    apply (directional_eq _ _ _).mpr
    rw [e]
    exact hdu.unique hz
  have hgood : ∀ᶠ p in 𝓝 (x₀, (0 : ℝ)), P p ∧ AnalyticAt ℝ u p ∧ u (p.1, 0) = u₀ p.1 := by
    filter_upwards [tB.eventually hP, hQB, hu.eventually_analyticAt,
      (continuous_fst.tendsto (x₀, (0 : ℝ))).eventually hinit] with p hp he hd _hu₀'
    exact ⟨he ▸ hp, hd, _hu₀'⟩
  obtain ⟨r, hr, H⟩ := Metric.eventually_nhds_iff_ball.mp hgood
  let U := Metric.ball (x₀, (0 : ℝ)) r
  have haU : (x₀, (0 : ℝ)) ∈ U := Metric.mem_ball_self hr
  have ho : IsOpen U := Metric.isOpen_ball
  have huU : AnalyticOnNhd ℝ u U := fun p hp => (H p hp).2.1
  refine ⟨U, u, haU, ho, huU, fun x hx => (H (x, 0) hx).2.2, fun p hp => (H p hp).1, ?_⟩
  intro v hv hv0 hvP
  apply huU.eqOn_of_preconnected_of_eventuallyEq hv Metric.isPreconnected_ball haU
  have hcomp : ∀ᶠ q in 𝓝 (x₀, (0 : ℝ)), Q q ∈ U ∧ AnalyticAt ℝ Q q ∧ AnalyticAt ℝ Z q ∧
      Y (q.1, 0) = q.1 ∧ Z (q.1, 0) = u₀ q.1 ∧
      HasDerivAt (fun t => Y (q.1, t)) (-F (Y q, q.2, Z q)) q.2 ∧
      HasDerivAt (fun t => Z (q.1, t)) (f (Y q, q.2, Z q)) q.2 := by
    filter_upwards [tQ.eventually (ho.mem_nhds haU), hQ.eventually_analyticAt,
      hZ.eventually_analyticAt, hchar] with q h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨δ, hδ, D⟩ := Metric.eventually_nhds_iff_ball.mp hcomp
  -- Equality near time zero extends along each analytic characteristic in the parameter ball.
  have hVZ : (v ∘ Q) =ᶠ[𝓝 (x₀, 0)] Z := by
    filter_upwards [Metric.ball_mem_nhds (x₀, (0 : ℝ)) hδ] with q hq
    rw [← ball_prod_same] at hq
    have Ht (s : ℝ) (hs : s ∈ Metric.ball (0 : ℝ) δ) := D (q.1, s)
      ((ball_prod_same x₀ (0 : ℝ) δ) ▸
        (⟨hq.1, hs⟩ : (q.1, s) ∈ Metric.ball x₀ δ ×ˢ Metric.ball 0 δ))
    have hzero := Ht 0 (Metric.mem_ball_self hδ)
    let y (s : ℝ) := Y (q.1, s)
    let z (s : ℝ) := Z (q.1, s)
    have hinitial : v (y 0, 0) = z 0 := by
      change v (Y (q.1, 0), 0) = Z (q.1, 0)
      rw [hv0 _ hzero.1, hzero.2.2.2.1, hzero.2.2.2.2.1]
    have hvG := agree_along_characteristic (y := y) (z := z) _hF _hf hinitial (hv _ hzero.1)
      (by filter_upwards [ho.mem_nhds hzero.1] with p hp using (directional_eq _ _ _).mp (hvP p hp))
      (by filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with s hs using (Ht s hs).2.2.2.2.2)
    have hvline : AnalyticOnNhd ℝ (fun s => v (Q (q.1, s))) (Metric.ball (0 : ℝ) δ) := by
      intro s hs
      exact (hv _ (Ht s hs).1).comp_of_eq ((Ht s hs).2.1.comp_of_eq
        (analyticAt_const.prod analyticAt_id) rfl) rfl
    have hzline : AnalyticOnNhd ℝ z (Metric.ball (0 : ℝ) δ) := fun s hs =>
      (Ht s hs).2.2.1.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
    exact hvline.eqOn_of_preconnected_of_eventuallyEq hzline Metric.isPreconnected_ball
      (Metric.mem_ball_self hδ) hvG hq.2
  filter_upwards [tB.eventually hVZ, hQB] with p hvp he
  exact hvp.symm.trans (congrArg v he)

end

end MathlibExt.Analysis.CauchyKovalevskayaWanted.Analysis
