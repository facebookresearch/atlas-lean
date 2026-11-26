/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Control.NonlinearControl
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import MathlibExt.Analysis.Convex.BrouwerFixedPoint
import MathlibExt.Analysis.ODE.MaximalSolution
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Brockett's necessary condition for stabilisation

A stabilising continuous stationary feedback forces the image of each neighbourhood of the
equilibrium state and control to contain a neighbourhood of zero velocity.

The closed-loop field is continuous. If its image on a small closed ball omits arbitrarily
small velocities, C¹ approximation and subtraction of those velocities give Lipschitz fields
without zeros on the ball. For each such field, vary the flow time from zero in the inner half-ball
to a large time on the boundary. Brouwer's fixed-point theorem gives either a periodic trajectory
through the outer annulus or a boundary point whose displacement points outwards. In both cases
a trajectory is far from the origin at a late time. Arzelà–Ascoli gives a limiting trajectory of
the closed-loop field, contradicting local asymptotic stability.
-/

open Set Filter Topology Metric
open scoped ContDiff NNReal

namespace MathlibExt.Analysis.Control.NonlinearControlWanted

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem lipschitz_curves_compact {u : ℕ → C(ℝ, E)} {K : ℝ≥0} {R : ℝ}
    (hu : ∀ n, LipschitzWith K (u n)) (h0 : ∀ n, ‖u n 0‖ ≤ R) :
    ∃ g : C(ℝ, E), ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 g) := by
  have : T2Space (UniformOnFun ℝ E {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering <|
      eq_univ_iff_forall.mpr fun x => mem_sUnion_of_mem (mem_singleton x) isCompact_singleton
  have hc : IsCompact (closure (range u)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (𝔖 := {s : Set ℝ | IsCompact s}) (F := fun f : C(ℝ, E) => (f : ℝ → E))
      (fun _ h => h) ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · intro s _
      apply Equicontinuous.equicontinuousOn
      apply UniformEquicontinuous.equicontinuous
      apply LipschitzWith.uniformEquicontinuous _ K
      rintro ⟨_, n, rfl⟩
      exact hu n
    · intro s _ t _
      refine ⟨closedBall 0 (K * ‖t‖ + R), isCompact_closedBall .., ?_⟩
      rintro _ ⟨n, rfl⟩
      rw [mem_closedBall, dist_zero_right]
      have ht := (hu n).dist_le_mul t 0
      rw [dist_zero_right] at ht
      calc
        ‖u n t‖ ≤ dist (u n t) (u n 0) + ‖u n 0‖ := by simpa using dist_triangle (u n t) (u n 0) 0
        _ ≤ K * ‖t‖ + R := add_le_add ht (h0 n)
  obtain ⟨g, -, φ, hφ, hlim⟩ := hc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  exact ⟨g, φ, hφ, hlim⟩

private theorem limit_solution {F : ℕ → C(E, E)} {X : C(E, E)}
    {x : ℕ → C(ℝ, E)} {y : C(ℝ, E)} (hF : Tendsto F atTop (𝓝 X))
    (hx : Tendsto x atTop (𝓝 y))
    (hd : ∀ n t, HasDerivAt (x n) (F n (x n t)) t) :
    ∀ t, HasDerivAt y (X (y t)) t := by
  have hc : Tendsto (fun n => (F n).comp (x n)) atTop (𝓝 (X.comp y)) :=
    hF.compCM hx
  have hu := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hc
  intro t
  apply hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ hu.tendstoLocallyUniformlyOn
  · exact .of_forall fun n t _ => hd n t
  · exact fun t _ => (continuous_eval_const t).tendsto _ |>.comp hx
  · exact mem_univ _

private theorem compact_solutions {F : ℕ → C(E, E)} {Y : C(E, E)}
    (hF : Tendsto F atTop (𝓝 Y)) {K : ℝ≥0} (hK : ∀ n z, ‖F n z‖ ≤ K)
    {x : ℕ → C(ℝ, E)} (hd : ∀ n t, HasDerivAt (x n) (F n (x n t)) t)
    {R : ℝ} (h0 : ∀ n, ‖x n 0‖ ≤ R)
    {t : ℕ → ℝ} {J : Set ℝ} (hJ : IsCompact J) (ht : ∀ n, t n ∈ J) :
    ∃ y : C(ℝ, E), ∃ s ∈ J, (∀ v, HasDerivAt y (Y (y v)) v) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n => x (φ n) 0) atTop (𝓝 (y 0)) ∧
        Tendsto (fun n => x (φ n) (t (φ n))) atTop (𝓝 (y s)) := by
  have hlip (n : ℕ) : LipschitzWith K (x n) := by
    apply lipschitzWith_of_nnNorm_deriv_le (fun t => (hd n t).differentiableAt)
    intro t
    rw [(hd n t).deriv]
    exact hK n _
  obtain ⟨y, ψ, hψ, hy⟩ := lipschitz_curves_compact hlip h0
  obtain ⟨s, hs, γ, hγ, hγt⟩ := hJ.tendsto_subseq fun n => ht (ψ n)
  refine ⟨y, s, hs, limit_solution (hF.comp hψ.tendsto_atTop) hy (fun n => hd (ψ n)),
    ψ ∘ γ, hψ.comp hγ, (hy.eval_const 0).comp hγ.tendsto_atTop, ?_⟩
  exact (hy.comp hγ.tendsto_atTop).eval hγt

omit [FiniteDimensional ℝ E] [NormedSpace ℝ E] in
private theorem first_hit {x : ℝ → E} (hx : Continuous x) {r t : ℝ}
    (h0 : ‖x 0‖ < r) (ht : 0 ≤ t) (hrt : r ≤ ‖x t‖) :
    ∃ s ∈ Icc 0 t, ‖x s‖ = r ∧ ∀ v ∈ Ico 0 s, ‖x v‖ < r := by
  let S := Icc 0 t ∩ {s | ‖x s‖ = r}
  have hc : IsCompact S := isCompact_Icc.inter_right (isClosed_eq hx.norm continuous_const)
  obtain ⟨b, hb, heb⟩ := intermediate_value_Icc ht hx.norm.continuousOn ⟨h0.le, hrt⟩
  obtain ⟨s, hs, hmin⟩ := hc.exists_isLeast ⟨b, hb, heb⟩
  refine ⟨s, hs.1, hs.2, fun v hv => lt_of_not_ge fun hv' => ?_⟩
  obtain ⟨c, hc, hec⟩ := intermediate_value_Icc hv.1 hx.norm.continuousOn ⟨h0.le, hv'⟩
  exact (hmin (show c ∈ S from ⟨⟨hc.1, hc.2.trans (hv.2.le.trans hs.1.2)⟩, hec⟩)).not_gt
    (hc.2.trans_lt hv.2)

omit [FiniteDimensional ℝ E] in
private theorem delayed_solution {Y : E → E} {x : ℝ → E} (h0 : x 0 = 0) (hY : Y 0 = 0)
    (hd : ∀ t, HasDerivAt x (Y (x t)) t) (d : ℝ) :
    ∀ t, HasDerivAt (fun t => x (max 0 (t - d))) (Y (x (max 0 (t - d)))) t := by
  intro t
  rcases lt_trichotomy t d with h | rfl | h
  · rw [max_eq_left (sub_nonpos.mpr h.le), h0, hY]
    apply (hasDerivAt_const t (0 : E)).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds h] with s hs
    simp [max_eq_left (sub_nonpos.mpr hs.le), h0]
  · simp only [sub_self, max_self, h0, hY]
    have hl : HasDerivWithinAt (fun s => x (max 0 (s - t))) 0 (Iic t) t := by
      apply (hasDerivWithinAt_const t (Iic t) (0 : E)).congr
      · intro s hs
        simp [max_eq_left (sub_nonpos.mpr (show s ≤ t from hs)), h0]
      · simp [h0]
    have hr : HasDerivWithinAt (fun s => x (max 0 (s - t))) 0 (Ici t) t := by
      have h := (hd (t - t)).comp_sub_const t t
      simp only [sub_self, h0, hY] at h
      exact h.hasDerivWithinAt.congr (fun s hs => by rw [max_eq_right (sub_nonneg.mpr hs)])
        (by simp)
    simpa using hl.union hr
  · rw [max_eq_right (sub_nonneg.mpr h.le)]
    apply ((hd (t - d)).comp_sub_const t d).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds h] with s hs
    rw [max_eq_right (sub_nonneg.mpr hs.le)]

private theorem confinement {X : E → E} {Y : C(E, E)} (hX : IsLocallyAsymptoticallyStable X)
    (hY0 : Y 0 = 0) (hagree : ∀ z, ‖z‖ ≤ 1 → Y z = X z) {K : ℝ≥0} (hK : ∀ z, ‖Y z‖ ≤ K) :
    ∃ r > 0, ∀ x : C(ℝ, E), (∀ t, HasDerivAt x (Y (x t)) t) → ‖x 0‖ ≤ r →
      ∀ t ≥ 0, ‖x t‖ < 1 / 2 := by
  obtain ⟨δ, hδ, hstab⟩ := hX
  obtain ⟨M, hM, hbound⟩ := hstab (1 / 4) (by norm_num)
  -- Any first exit from the half-unit ball must occur during the transient interval.
  have exit_bound {x : C(ℝ, E)} (hd : ∀ t, HasDerivAt x (Y (x t)) t)
      (h0 : ‖x 0‖ < δ) {s : ℝ} (hs : ‖x s‖ = 1 / 2)
      (hpre : ∀ t ∈ Ico 0 s, ‖x t‖ < 1 / 2) : s ≤ M := by
    by_contra! hMs
    have hD (t : ℝ) (ht : t ∈ Ico 0 s) :
        HasDerivWithinAt x (X (x t)) (Ico 0 s) t := by
      rw [← hagree _ (by linarith [hpre t ht])]
      exact (hd t).hasDerivWithinAt
    have hsub : Ioo M s ⊆ {t | ‖x t‖ ≤ 1 / 4} := fun t ht =>
      (hbound s x hD h0 t ⟨hM.le.trans ht.1.le, ht.2⟩ ht.1).le
    have hcl := closure_minimal hsub (isClosed_le x.continuous.norm continuous_const)
    rw [closure_Ioo hMs.ne] at hcl
    have : ‖x s‖ ≤ 1 / 4 := hcl (right_mem_Icc.mpr hMs.le)
    linarith
  -- A solution issuing from zero can wait there for the entire transient interval.
  have zero_stays {x : C(ℝ, E)} (hd : ∀ t, HasDerivAt x (Y (x t)) t) (h0 : x 0 = 0)
      {v : ℝ} (hv : 0 ≤ v) : ‖x v‖ < 1 / 2 := by
    by_contra! hbad
    let d := M + 1
    let z : C(ℝ, E) := ⟨fun t => x (max 0 (t - d)), by fun_prop⟩
    have hz0 : z 0 = 0 := by
      change x (max 0 (0 - d)) = 0
      rwa [max_eq_left (by dsimp [d]; linarith)]
    have hlast : 1 / 2 ≤ ‖z (d + v)‖ := by simpa [z, max_eq_right hv] using hbad
    obtain ⟨s, hs, he, hp⟩ := first_hit z.continuous (by rw [hz0]; norm_num)
      (show 0 ≤ d + v by dsimp [d]; linarith) hlast
    have hearly := exit_bound (delayed_solution h0 hY0 hd d) (by simpa [hz0] using hδ) he hp
    have hzs : z s = 0 := by simpa [z, max_eq_left (by dsimp [d]; linarith : s - d ≤ 0)] using h0
    rw [hzs, norm_zero] at he
    norm_num at he
  by_contra! hn
  let a (n : ℕ) : ℝ := min (min (δ / 2) (1 / 4)) (1 / ((n : ℝ) + 1))
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  choose x hd h0 t ht hbad using fun n => hn (a n) (ha n)
  have hδ' (n : ℕ) : ‖x n 0‖ < δ :=
    ((h0 n).trans ((min_le_left ..).trans (min_le_left ..))).trans_lt (half_lt_self hδ)
  have hsmall (n : ℕ) : ‖x n 0‖ ≤ 1 / 4 :=
    (h0 n).trans ((min_le_left ..).trans (min_le_right ..))
  choose s hs hhit hpre using fun n =>
    first_hit (x n).continuous (lt_of_le_of_lt (hsmall n) (by norm_num)) (ht n) (hbad n)
  have htimes (n : ℕ) : s n ∈ Icc 0 M :=
    ⟨(hs n).1, exit_bound (hd n) (hδ' n) (hhit n) (hpre n)⟩
  obtain ⟨y, v, hv, hyd, φ, hφ, hy0, hyv⟩ :=
    compact_solutions tendsto_const_nhds (fun _ => hK) hd hsmall isCompact_Icc htimes
  have hx0 : Tendsto (fun n => x n 0) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (h0 n).trans (min_le_right ..))
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hyzero : y 0 = 0 := tendsto_nhds_unique hy0 (hx0.comp hφ.tendsto_atTop)
  have he : ‖y v‖ = 1 / 2 := tendsto_nhds_unique hyv.norm (by simpa only [hhit] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 _)))
  exact (zero_stays hyd hyzero hv.1).ne he

-- Continuous dependence on the initial state for the forward Lipschitz flow.
omit [FiniteDimensional ℝ E] in
private theorem continuous_forward {F : E → E} {L K : ℝ≥0} (hL : LipschitzWith L F)
    (hK : ∀ z, ‖F z‖ ≤ K) {p : E → ℝ → E} (h0 : ∀ x, p x 0 = x)
    (hd : ∀ x t, HasDerivAt (p x) (F (p x t)) t) :
    Continuous (fun q : E × ℝ => p q.1 (max 0 q.2)) := by
  have hc x : Continuous (p x) := continuous_iff_continuousAt.mpr fun t => (hd x t).continuousAt
  have hLip x : LipschitzWith K (p x) := by
    apply lipschitzWith_of_nnNorm_deriv_le (fun t => (hd x t).differentiableAt)
    intro t
    rw [(hd x t).deriv]
    exact hK _
  have hdist (x y : E) (t : ℝ) (ht : 0 ≤ t) :
      dist (p x t) (p y t) ≤ dist x y * Real.exp (L * t) := by
    have h := dist_le_of_trajectories_ODE (v := fun _ => F) (fun _ => hL)
      (hc x).continuousOn (fun t _ => (hd x t).hasDerivWithinAt)
      (hc y).continuousOn (fun t _ => (hd y t).hasDerivWithinAt)
      (a := 0) (b := t) (δ := dist x y) (by simp [h0]) t (right_mem_Icc.mpr ht)
    simpa using h
  rw [continuous_iff_continuousAt]
  intro q
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (.of_forall fun _ => dist_nonneg)
  · exact .of_forall fun w => (dist_triangle _ (p w.1 (max 0 q.2)) _).trans
      (add_le_add ((hLip w.1).dist_le_mul _ _) (hdist w.1 q.1 _ (le_max_left ..)))
  · have hc' : Continuous (fun w : E × ℝ =>
        K * dist (max 0 w.2) (max 0 q.2) + dist w.1 q.1 * Real.exp (L * max 0 q.2)) := by
      fun_prop
    simpa using hc'.tendsto q

-- A nonvanishing Lipschitz field cannot bring every point of the ball inside its half-radius
-- throughout the time interval [T, 2T]. Vary the flow time from zero in the core to T at the edge.
private theorem late_excursion {F : E → E} {L K : ℝ≥0} (hL : LipschitzWith L F)
    (hK : ∀ z, ‖F z‖ ≤ K) {r T : ℝ} (hr : 0 < r) (hT : 0 < T)
    (hnz : ∀ z, ‖z‖ ≤ r → F z ≠ 0) :
    ∃ x : C(ℝ, E), (∀ s, HasDerivAt x (F (x s)) s) ∧ ‖x 0‖ ≤ r ∧
      ∃ s ∈ Icc T (2 * T), r / 2 ≤ ‖x s‖ := by
  classical
  have hex x := ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz
    (fun _ => F) 0 x L (hL.continuous.comp continuous_snd) (fun _ => hL)
  choose p hp huniq using hex
  have h0 x : p x 0 = x := (hp x).1
  have hd x t : HasDerivAt (p x) (F (p x t)) t := (hp x).2 t
  let P (x : E) : C(ℝ, E) := ⟨p x, continuous_iff_continuousAt.mpr fun t => (hd x t).continuousAt⟩
  have hforw := continuous_forward hL hK h0 hd
  let τ (x : E) : ℝ := T * max 0 (2 * ‖x‖ / r - 1)
  have hτ : Continuous τ := by dsimp [τ]; fun_prop
  have hτ0 x : 0 ≤ τ x := mul_nonneg hT.le (le_max_left ..)
  have hτr {x : E} (hx : ‖x‖ ≤ r) : τ x ≤ T := by
    apply mul_le_of_le_one_right hT.le
    rw [max_le_iff]
    refine ⟨zero_le_one, ?_⟩
    have : 2 * ‖x‖ / r ≤ 2 := (div_le_iff₀ hr).mpr (by linarith)
    linarith
  let v (x : E) (s : ℝ) := F (p x (max 0 (s * τ x)))
  have hv : Continuous (Function.uncurry v) :=
    hL.continuous.comp (hforw.comp (continuous_fst.prodMk (continuous_snd.mul
      (hτ.comp continuous_fst))))
  let G (x : E) := ∫ s in (0 : ℝ)..1, v x s
  have hG : Continuous G := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    hv 0 1
  have displ x : τ x • G x = p x (τ x) - x := by
    have hD (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) 1) :
        HasDerivAt (fun t => p x (t * τ x)) (τ x • v x s) s := by
      have hs0 : 0 ≤ s := (uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1) ▸ hs).1
      dsimp [v]
      rw [max_eq_right (mul_nonneg hs0 (hτ0 x))]
      simpa [Function.comp_def] using (hd x (s * τ x)).scomp s ((hasDerivAt_id s).mul_const (τ x))
    have hc : Continuous (fun s => τ x • v x s) :=
      continuous_const.smul (hv.comp (continuous_const.prodMk continuous_id))
    simpa [G, intervalIntegral.integral_smul, h0] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt hD (hc.intervalIntegrable ..)
  -- A zero of the average velocity gives a periodic orbit outside the inner half-ball.
  by_cases hz : ∃ x, ‖x‖ ≤ r ∧ G x = 0
  · obtain ⟨x, hxr, hzero⟩ := hz
    have htpos : 0 < τ x := by
      by_contra! h
      have ht := le_antisymm h (hτ0 x)
      exact hnz x hxr (by simpa [G, v, ht, h0] using hzero)
    have hxcore : r / 2 ≤ ‖x‖ := by
      by_contra! h
      have hsmall : 2 * ‖x‖ / r ≤ 1 := (div_le_iff₀ hr).mpr (by linarith)
      simp [τ, max_eq_left (sub_nonpos.mpr hsmall)] at htpos
    have hreturn : p x (τ x) = x := by
      apply sub_eq_zero.mp
      simpa [hzero] using (displ x).symm
    have hshift : (fun t => p x (t + τ x)) = p x := huniq x _ ⟨by simpa using hreturn,
      fun t => (hd x (t + τ x)).comp_add_const t (τ x)⟩
    have hper : Function.Periodic (p x) (τ x) := fun t => congrFun hshift t
    let n := ⌈T / τ x⌉₊
    have hlo : T ≤ (n : ℝ) * τ x := (div_le_iff₀ htpos).mp (Nat.le_ceil _)
    have hhi := mul_le_mul_of_nonneg_right
      (Nat.ceil_lt_add_one (div_nonneg hT.le htpos.le)).le htpos.le
    rw [add_mul, div_mul_cancel₀ _ htpos.ne', one_mul] at hhi
    refine ⟨P x, hd x, by simpa [P, h0] using hxr, n * τ x,
      ⟨hlo, hhi.trans (by linarith [hτr hxr])⟩, ?_⟩
    simpa [P, hper.nat_mul_eq n, h0] using hxcore
  · -- Normalise the average velocity to the boundary sphere and apply Brouwer.
    push Not at hz
    let B := closedBall (0 : E) r
    let g (x : E) := (r / ‖G x‖) • G x
    have hn {x : E} (hx : x ∈ B) : G x ≠ 0 := hz x (by simpa [B] using hx)
    have hlen {x : E} (hx : x ∈ B) : ‖g x‖ = r := by
      dsimp only [g]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr (norm_pos_iff.mpr (hn hx))),
        div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (hn hx))]
    have hg : ContinuousOn g B := (continuousOn_const.div hG.norm.continuousOn
      (fun x hx => norm_ne_zero_iff.mpr (hn hx))).smul hG.continuousOn
    obtain ⟨x, hx, hfix⟩ := Convex.BrouwerFixedPoint.exists_fixedPoint
      (isCompact_closedBall ..) (convex_closedBall ..)
      ⟨0, mem_closedBall_self hr.le⟩ hg (fun z hzB => by simp [hlen hzB])
    have hxr : ‖x‖ = r := hfix ▸ hlen hx
    have ht : τ x = T := by norm_num [τ, hxr, hr.ne']
    have he := displ x
    rw [ht] at he
    have hpx : p x T = (T + r / ‖G x‖) • G x := by
      rw [add_smul, show (r / ‖G x‖) • G x = x from hfix]
      exact sub_eq_iff_eq_add.mp he.symm
    refine ⟨P x, hd x, by simp [P, h0, hxr], T, ⟨le_rfl, by linarith⟩, ?_⟩
    change r / 2 ≤ ‖p x T‖
    rw [hpx, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), add_mul,
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (hn hx))]
    nlinarith [mul_nonneg hT.le (norm_nonneg (G x))]

-- Subtract an omitted velocity after approximating the field. On the compact ball its
-- distance from the image is positive, so the approximation can preserve the omission.
private theorem approximate_without_zero {Y : C(E, E)} (hY : HasCompactSupport (Y : E → E))
    {r : ℝ} (hr : 0 < r) (hmiss : Y '' closedBall 0 r ∉ 𝓝 (0 : E)) :
    ∃ F : ℕ → C(E, E), Tendsto F atTop (𝓝 Y) ∧ (∃ K : ℝ≥0, ∀ n z, ‖F n z‖ ≤ K) ∧
      ∀ n, (∃ L, LipschitzWith L (F n)) ∧ ∀ z, ‖z‖ ≤ r → F n z ≠ 0 := by
  classical
  let e (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have he (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have hε (n : ℕ) : ∃ w : E, ‖w‖ < e n ∧ w ∉ Y '' closedBall 0 r := by
    by_contra! h
    apply hmiss
    refine Metric.mem_nhds_iff.mpr ⟨e n, he n, fun z hz => h z (by simpa using hz)⟩
  choose w hw hwout using hε
  have happrox (n : ℕ) : ∃ g : C(E, E), (∃ L, LipschitzWith L g) ∧
      (∀ z, dist (g z) (Y z) < e n) ∧ ∀ z ∈ closedBall 0 r, g z ≠ w n := by
    have hc : Continuous (fun z => dist (Y z) (w n)) := Y.continuous.dist continuous_const
    obtain ⟨a, ha, hmin⟩ := (isCompact_closedBall (0 : E) r).exists_isMinOn
      ⟨0, mem_closedBall_self hr.le⟩ hc.continuousOn
    have hpos : 0 < dist (Y a) (w n) :=
      dist_pos.mpr fun heq => hwout n ⟨a, ha, heq⟩
    obtain ⟨g, hg, hdist, hs⟩ := Y.continuous.exists_contDiff_approx 1
      (ε := fun _ => min (e n) (dist (Y a) (w n))) continuous_const (fun _ => lt_min (he n) hpos)
    have hgs : HasCompactSupport g :=
      HasCompactSupport.of_support_subset_isCompact hY (hs.trans subset_closure)
    refine ⟨⟨g, hg.continuous⟩, hg.lipschitzWith_of_hasCompactSupport hgs (by simp),
      fun z => (hdist z).trans_le (min_le_left ..), ?_⟩
    intro z hz heq
    have hh := (hdist z).trans_le (min_le_right ..)
    change g z = w n at heq
    rw [heq, dist_comm] at hh
    exact (hmin hz).not_gt hh
  choose g hL hdist hnz using happrox
  let F (n : ℕ) : C(E, E) := ⟨fun z => g n z - w n, (g n).continuous.sub continuous_const⟩
  have herr n z : dist (Y z) (F n z) < 2 * e n := by
    have heq : dist (g n z) (F n z) = ‖w n‖ := by simp [F]
    calc
      _ ≤ dist (Y z) (g n z) + dist (g n z) (F n z) := dist_triangle ..
      _ < 2 * e n := by rw [dist_comm (Y z), heq]; linarith [hdist n z, hw n]
  refine ⟨F, ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr ?_, ?_, ?_⟩
  · intro S _
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have ht : Tendsto (fun n => 2 * e n) atTop (𝓝 0) := by
      simpa [e] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn z _
    exact (herr n z).trans hn
  · obtain ⟨B, hB⟩ := hY.exists_bound_of_continuous Y.continuous
    refine ⟨⟨max 0 B + 2, by positivity⟩, fun n z => ?_⟩
    have he1 : e n ≤ 1 := (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr (by simp)
    have htri := dist_triangle (F n z) (Y z) 0
    rw [dist_zero_right, dist_zero_right, dist_comm (F n z)] at htri
    change ‖F n z‖ ≤ max 0 B + 2
    linarith [herr n z, hB z, le_max_right (0 : ℝ) B]
  · intro n
    obtain ⟨L, hL⟩ := hL n
    refine ⟨⟨L, LipschitzWith.of_dist_le_mul fun x y => ?_⟩, fun z hz => ?_⟩
    · simpa [F] using hL.dist_le_mul x y
    · exact sub_ne_zero.mpr (hnz n z (by simpa using hz))

private theorem stable_image {X : E → E} (hc : Continuous X) (hzero : X 0 = 0)
    (hstable : IsLocallyAsymptoticallyStable X) (V : Set E) (hV : V ∈ 𝓝 0) :
    X '' V ∈ 𝓝 (0 : E) := by
  -- Truncation gives a bounded field which agrees with the original on the unit ball.
  let Y : C(E, E) := ⟨fun z => max 0 (min 1 (2 - ‖z‖)) • X z, by fun_prop⟩
  have hagree z (hz : ‖z‖ ≤ 1) : Y z = X z := by
    simp [Y, min_eq_left (by linarith : 1 ≤ 2 - ‖z‖)]
  have hY : HasCompactSupport (Y : E → E) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 2)
    intro z hz
    contrapose hz
    simp only [mem_closedBall, dist_zero_right, not_le] at hz
    simp [Y, max_eq_left ((min_le_right ..).trans (by linarith : 2 - ‖z‖ ≤ 0))]
  obtain ⟨B, hB⟩ := hY.exists_bound_of_continuous Y.continuous
  obtain ⟨r₀, hr₀, hstay⟩ := confinement hstable (by rw [hagree 0 (by simp), hzero]) hagree
    (K := ⟨max B 0, le_max_right ..⟩) (fun z => (hB z).trans (le_max_left ..))
  obtain ⟨δ, hδ, hstab⟩ := hstable
  obtain ⟨ρ, hρ, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hV
  let r := min (min r₀ 1) (min ρ (δ / 2))
  have hr : 0 < r := by dsimp [r]; positivity
  have hr₀' : r ≤ r₀ := (min_le_left ..).trans (min_le_left ..)
  have hr1 : r ≤ 1 := (min_le_left ..).trans (min_le_right ..)
  have hrρ : r ≤ ρ := (min_le_right ..).trans (min_le_left ..)
  have hrδ : r < δ := ((min_le_right ..).trans (min_le_right ..)).trans_lt (half_lt_self hδ)
  by_contra hmiss
  have hbad : Y '' closedBall 0 r ∉ 𝓝 (0 : E) := by
    apply mt (mem_of_superset · ?_) hmiss
    rintro y ⟨z, hz, rfl⟩
    refine ⟨z, hsub (closedBall_subset_closedBall hrρ hz), (hagree z ?_).symm⟩
    exact (show ‖z‖ ≤ r by simpa using hz).trans hr1
  obtain ⟨F, hF, ⟨K, hK⟩, hFprop⟩ := approximate_without_zero hY hr hbad
  obtain ⟨M, hM, hbound⟩ := hstab (r / 2) (half_pos hr)
  let T := M + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have hex n := late_excursion (hFprop n).1.choose_spec (hK n) hr hT (hFprop n).2
  choose x hd h0 t ht hlate using hex
  obtain ⟨y, s, hs, hyd, φ, -, hy0, hys⟩ := compact_solutions hF hK hd h0 isCompact_Icc ht
  have hinit : ‖y 0‖ ≤ r := le_of_tendsto hy0.norm (.of_forall fun n => h0 (φ n))
  have hfar : r / 2 ≤ ‖y s‖ := ge_of_tendsto hys.norm (.of_forall fun n => hlate (φ n))
  have hsol (v : ℝ) (hv : v ∈ Ico 0 (s + 1)) :
      HasDerivWithinAt y (X (y v)) (Ico 0 (s + 1)) v := by
    have hsmall := hstay y hyd (hinit.trans hr₀') v hv.1
    rw [← hagree _ (by linarith)]
    exact (hyd v).hasDerivWithinAt
  exact hfar.not_gt (hbound (s + 1) y hsol (hinit.trans_lt hrδ) s
    ⟨hT.le.trans hs.1, by linarith⟩ (by dsimp [T] at hs; linarith [hs.1]))

end

/-- **Brockett's necessary condition for stabilisation** (Brockett 1983; Coron, *Control and
Nonlinearity*, AMS 2007, Theorem 11.1). Let `f : ℝⁿ × ℝᵐ → ℝⁿ` be of class `C^∞` with
`f(0, 0) = 0`. If `ẋ = f(x, u)` is locally asymptotically stabilisable by continuous stationary
feedback laws, then the image under `f` of every neighbourhood of `(0, 0)` is a neighbourhood of
`0`. (Coron allows `f` to be defined only on an open neighbourhood of `(0, 0)`; this is the case
where `f` is defined and smooth everywhere.) -/
public theorem brockettCondition_of_isLocallyAsymptoticallyStabilizable {E U : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
    (f : E × U → E) (hf : ContDiff ℝ ∞ f) (h0 : f (0, 0) = 0)
    (hstab : IsLocallyAsymptoticallyStabilizable f) :
    BrockettCondition f := by
  obtain ⟨u, hu, hu0, hs⟩ := hstab
  have hgraph : Continuous (fun x : E => (x, u x)) := continuous_id.prodMk hu
  intro N hN
  have hpre : (fun x => (x, u x)) ⁻¹' N ∈ 𝓝 (0 : E) := by
    apply hgraph.continuousAt
    simpa [hu0] using hN
  have himage := stable_image (hf.continuous.comp hgraph) (by simpa [hu0] using h0) hs _ hpre
  exact mem_of_superset himage fun y ⟨x, hx, he⟩ => ⟨(x, u x), hx, he⟩

end MathlibExt.Analysis.Control.NonlinearControlWanted
