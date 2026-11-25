/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

@[expose] public section

section
namespace MathlibExt.Analysis.ODE.CauchyPeanoWanted

/-!
# Cauchy–Peano existence theorem for ODEs
-/

/--
**Cauchy–Peano existence theorem.** Let $E$ be a finite-dimensional real normed space and let
$f : \mathbb{R} \times E \to E$ be continuous. Then for every $t_0 \in \mathbb{R}$ and
$x_0 \in E$ there are $\varepsilon > 0$ and a function $x : \mathbb{R} \to E$ with
$x(t_0) = x_0$ such that, for every $t \in (t_0 - \varepsilon, t_0 + \varepsilon)$, $x$ is
differentiable at $t$ with $x'(t) = f(t, x(t))$.

Proves `Wanted` entry `cauchy_peano_exists`.

Source: G. Peano, Math. Ann. 37 (1890), 182-228, DOI 10.1007/BF01200235.
-/
theorem cauchy_peano_exists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : ℝ × E → E) (hf : Continuous f) (t₀ : ℝ) (x₀ : E) :
    ∃ ε > 0, ∃ x : ℝ → E, x t₀ = x₀ ∧
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), HasDerivAt x (f (t, x t)) t := by
  classical
  have : ProperSpace E := FiniteDimensional.proper_real E
  have : ProperSpace (ℝ × E) := FiniteDimensional.proper_real (ℝ × E)
  have : CompleteSpace E := inferInstance
  -- compact convex box and bound M
  set box : Set (ℝ × E) := Set.Icc (t₀ - 1) (t₀ + 1) ×ˢ Metric.closedBall x₀ 1 with hbox
  have hbox_compact : IsCompact box := isCompact_Icc.prod (isCompact_closedBall x₀ 1)
  have hbox_convex : Convex ℝ box :=
    (convex_Icc (t₀ - 1) (t₀ + 1)).prod (convex_closedBall x₀ 1)
  have hcont_norm : ContinuousOn (fun p : ℝ × E => ‖f p‖) box := hf.norm.continuousOn
  obtain ⟨C, hC⟩ := hbox_compact.bddAbove_image hcont_norm
  have hbound : ∀ p ∈ box, ‖f p‖ ≤ C := fun p hp => hC (Set.mem_image_of_mem _ hp)
  set M : ℝ := max C 0 + 2 with hM
  have hM_pos : 0 < M := by
    have hle : (0 : ℝ) ≤ max C 0 := le_max_right _ _
    linarith
  have hfM : ∀ p ∈ box, ‖f p‖ + 1 ≤ M := fun p hp => by
    have h1 : C ≤ max C 0 := le_max_left _ _
    linarith [hbound p hp]
  set ε : ℝ := min 1 (1 / M) / 2 with hε
  have hε_pos : 0 < ε := by
    have h1 : (0:ℝ) < min 1 (1 / M) := lt_min zero_lt_one (by positivity)
    linarith
  have hε_le1 : ε ≤ 1 := by
    have h1 : min 1 (1 / M) ≤ 1 := min_le_left _ _
    linarith
  have hMε : M * ε ≤ 1 := by
    have h1 : min 1 (1 / M) ≤ 1 / M := min_le_right _ _
    have h2 : ε ≤ (1 / M) / 2 := by linarith
    have h3 : M * ε ≤ M * ((1 / M) / 2) := by gcongr
    have h4 : M * ((1 / M) / 2) = 1 / 2 := by field_simp
    linarith
  -- smooth approximations
  have happ : ∀ n : ℕ, ∃ g : ℝ × E → E,
      ContDiff ℝ ((1 : ℕ∞) : WithTop ℕ∞) g ∧ ∀ p, dist (g p) (f p) < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨g, hg1, hg2, -⟩ := hf.exists_contDiff_approx (1 : ℕ∞)
      (ε := fun _ : ℝ × E => (1 / ((n : ℝ) + 1))) continuous_const (fun _ => by positivity)
    exact ⟨g, hg1, hg2⟩
  choose g hg_smooth hg_close using happ
  have hlip_box : ∀ n, ∃ K : NNReal, LipschitzOnWith K (g n) box := by
    intro n
    have hne : ((1 : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
    obtain ⟨K, hK⟩ := ((hg_smooth n).contDiffOn).exists_lipschitzOnWith hne hbox_convex hbox_compact
    exact ⟨K, hK⟩
  choose K hK using hlip_box
  -- Picard data
  set tmin : ℝ := t₀ - ε with htmin
  set tmax : ℝ := t₀ + ε with htmax
  have hle : tmin ≤ tmax := by linarith [hε_pos]
  have ht₀mem : t₀ ∈ Set.Icc tmin tmax := ⟨by linarith [hε_pos], by linarith [hε_pos]⟩
  set t₀' : Set.Icc tmin tmax := ⟨t₀, ht₀mem⟩ with ht₀'
  set Mnn : NNReal := ⟨M, hM_pos.le⟩ with hMnn
  set F : ℕ → ℝ → E → E := fun n t x => g n (t, x) with hF
  have hmem_box : ∀ (t : ℝ) (x : E), t ∈ Set.Icc tmin tmax → x ∈ Metric.closedBall x₀ 1 →
      ((t, x) : ℝ × E) ∈ box := by
    intro t x ht hx
    constructor
    · constructor <;> linarith [ht.1, ht.2, hε_pos, hε_le1]
    · exact hx
  have hMnn_eq : ((Mnn : NNReal) : ℝ) = M := rfl
  have hPL : ∀ n, IsPicardLindelof (F n) t₀' x₀ 1 0 Mnn (K n) := by
    intro n
    refine IsPicardLindelof.mk ?lip ?cont ?norm ?mm
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      have hx' : x ∈ Metric.closedBall x₀ 1 := by simpa using hx
      have hy' : y ∈ Metric.closedBall x₀ 1 := by simpa using hy
      have hmem1 : ((t, x) : ℝ × E) ∈ box := hmem_box t x ht hx'
      have hmem2 : ((t, y) : ℝ × E) ∈ box := hmem_box t y ht hy'
      have h := (hK n).dist_le_mul _ hmem1 _ hmem2
      have heq : dist ((t, x) : ℝ × E) (t, y) = dist x y := by simp [dist_eq_norm]
      rw [heq] at h
      simpa only [hF] using h
    · intro x hx
      have hcont : Continuous (fun t : ℝ => g n (t, x)) :=
        (hg_smooth n).continuous.comp (continuous_id.prodMk continuous_const)
      exact hcont.continuousOn
    · intro t ht x hx
      have hx' : x ∈ Metric.closedBall x₀ 1 := by simpa using hx
      have hmem : ((t, x) : ℝ × E) ∈ box := hmem_box t x ht hx'
      have h1 : dist (g n (t, x)) (f (t, x)) < 1 / ((n : ℝ) + 1) := hg_close n _
      rw [dist_eq_norm] at h1
      have h2 : ‖f (t, x)‖ + 1 ≤ M := hfM _ hmem
      have h3 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
        apply div_le_one_of_le₀
        · linarith [Nat.cast_nonneg (α := ℝ) n]
        · positivity
      change ‖g n (t, x)‖ ≤ _
      rw [hMnn_eq]
      calc ‖g n (t, x)‖ = ‖f (t, x) + (g n (t, x) - f (t, x))‖ := by congr 1; abel
        _ ≤ ‖f (t, x)‖ + ‖g n (t, x) - f (t, x)‖ := norm_add_le _ _
        _ ≤ M := by linarith
    · have e1 : tmax - (t₀' : ℝ) = ε := by simp [htmax, ht₀']
      have e2 : (t₀' : ℝ) - tmin = ε := by simp [htmin, ht₀']
      rw [e1, e2, max_self, hMnn_eq]
      simpa using hMε
  -- approximate solutions via Picard fixed points
  have hx0 : x₀ ∈ Metric.closedBall x₀ ((0 : NNReal) : ℝ) := by simp
  have hfp_exists : ∀ n, ∃ α : ODE.FunSpace t₀' x₀ 0 Mnn,
      Function.IsFixedPt (ODE.FunSpace.next (hPL n) hx0) α := fun n =>
    ODE.FunSpace.exists_isFixedPt_next (hPL n) hx0
  choose α hfp using hfp_exists
  set u : ℕ → ℝ → E := fun n => (α n).compProj with hu
  have hu_cont : ∀ n, Continuous (u n) := fun n => (α n).continuous_compProj
  have hu_mem : ∀ n (t : ℝ), u n t ∈ Metric.closedBall x₀ (1 : ℝ) := by
    intro n t
    change (α n).compProj t ∈ _
    have h : (α n).compProj t ∈ Metric.closedBall x₀ ((1 : NNReal) : ℝ) :=
      (α n).compProj_mem_closedBall (hPL n).mul_max_le
    simpa using h
  have hu_init : ∀ n, u n t₀ = x₀ := by
    intro n
    have h0 : (α n) t₀' = x₀ := ODE.FunSpace.apply_of_zero (α n)
    have hcomp : (α n).compProj t₀ = (α n) ⟨t₀, ht₀mem⟩ :=
      ODE.FunSpace.compProj_of_mem ht₀mem
    change (α n).compProj t₀ = x₀
    rw [hcomp]
    have hsub : (⟨t₀, ht₀mem⟩ : Set.Icc tmin tmax) = t₀' := by simp [ht₀']
    rw [hsub]
    exact h0
  -- Arzela-Ascoli extraction
  have : CompactSpace (Set.Icc tmin tmax) := isCompact_iff_compactSpace.mp isCompact_Icc
  set BF : ℕ → BoundedContinuousFunction (Set.Icc tmin tmax) E :=
    fun n => BoundedContinuousFunction.mkOfCompact ⟨fun t' => (α n) t', (α n).continuous⟩ with hBF
  set S : Set E := Metric.closedBall x₀ ((1 : NNReal) : ℝ) with hS
  have hS_compact : IsCompact S := isCompact_closedBall x₀ _
  have hmemS : ∀ (fb : BoundedContinuousFunction (Set.Icc tmin tmax) E) (x : Set.Icc tmin tmax),
      fb ∈ Set.range BF → fb x ∈ S := by
    intro fb x hfb
    obtain ⟨n, rfl⟩ := hfb
    have heq : ((BF n) x : E) = (α n) x := rfl
    rw [heq, hS]
    exact ODE.FunSpace.mem_closedBall (hPL n).mul_max_le
  have hb0 : Filter.Tendsto (fun d : ℝ => M * d) (nhds 0) (nhds 0) := by
    have h : Continuous (fun d : ℝ => M * d) := continuous_const.mul continuous_id
    have h2 : Filter.Tendsto (fun d : ℝ => M * d) (nhds (0:ℝ)) (nhds ((fun d : ℝ => M * d) 0)) :=
      h.continuousAt
    simpa using h2
  have hequi : Equicontinuous (fun a : Set.range BF =>
      ((a : BoundedContinuousFunction (Set.Icc tmin tmax) E) : Set.Icc tmin tmax → E)) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun d => M * d) hb0
    intro s t a
    obtain ⟨fb, hfb⟩ := a
    obtain ⟨n, rfl⟩ := hfb
    change dist ((BF n) s) ((BF n) t) ≤ M * dist s t
    have h := (α n).lipschitzWith.dist_le_mul s t
    rw [hMnn_eq] at h
    have heq1 : ((BF n) s : E) = (α n) s := rfl
    have heq2 : ((BF n) t : E) = (α n) t := rfl
    rw [heq1, heq2]
    exact h
  have hClos : IsCompact (closure (Set.range BF)) :=
    BoundedContinuousFunction.arzela_ascoli S hS_compact _ hmemS hequi
  obtain ⟨z, -, φ, hφmono, hφlim⟩ :=
    hClos.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  -- uniform convergence of the subsequence
  have hφlim' : Filter.Tendsto (fun n => BF (φ n)) Filter.atTop (nhds z) := hφlim
  have hunif : TendstoUniformly (fun n => ((BF (φ n)) : Set.Icc tmin tmax → E)) (⇑z) Filter.atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hφlim'
  -- limit function on all of ℝ
  set x : ℝ → E := fun t => z (Set.projIcc tmin tmax hle t) with hx_def
  have hx_cont : Continuous x := z.continuous.comp continuous_projIcc
  have hproj_mem : ∀ (t : ℝ) (ht : t ∈ Set.Icc tmin tmax),
      Set.projIcc tmin tmax hle t = ⟨t, ht⟩ := by
    intro t ht
    apply Subtype.ext
    change max tmin (min tmax t) = t
    rw [min_eq_right ht.2, max_eq_right ht.1]
  have hz0 : z ⟨t₀, ht₀mem⟩ = x₀ := by
    have hpt := hunif.tendsto_at (⟨t₀, ht₀mem⟩ : Set.Icc tmin tmax)
    have hconst : ∀ n, (((BF (φ n)) : Set.Icc tmin tmax → E) ⟨t₀, ht₀mem⟩) = x₀ := by
      intro n
      have heq : ((((BF (φ n)) : Set.Icc tmin tmax → E)) ⟨t₀, ht₀mem⟩ : E)
          = (α (φ n)) ⟨t₀, ht₀mem⟩ := rfl
      rw [heq]
      have h0 : (α (φ n)) t₀' = x₀ := ODE.FunSpace.apply_of_zero _
      have hsub : (⟨t₀, ht₀mem⟩ : Set.Icc tmin tmax) = t₀' := by simp [ht₀']
      rw [hsub]; exact h0
    have hlim : Filter.Tendsto (fun _ : ℕ => x₀) Filter.atTop (nhds (z ⟨t₀, ht₀mem⟩)) := by
      simpa [hconst] using hpt
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  have hx_init : x t₀ = x₀ := by
    change z (Set.projIcc tmin tmax hle t₀) = x₀
    rw [hproj_mem t₀ ht₀mem]
    exact hz0
  -- limit takes values in the ball
  have hz_mem : ∀ s : Set.Icc tmin tmax, z s ∈ Metric.closedBall x₀ (1 : ℝ) := by
    intro s
    have hlim : Filter.Tendsto (fun n => (((BF (φ n)) : Set.Icc tmin tmax → E)) s) Filter.atTop
        (nhds (z s)) := hunif.tendsto_at s
    have hmem_each : ∀ n, ((((BF (φ n)) : Set.Icc tmin tmax → E)) s)
        ∈ Metric.closedBall x₀ (1 : ℝ) := by
      intro n
      have h := hmemS (BF (φ n)) s (Set.mem_range_self (φ n))
      simpa only [hS, NNReal.coe_one] using h
    exact (isCompact_closedBall x₀ (1 : ℝ)).isClosed.mem_of_tendsto hlim
      (Filter.Eventually.of_forall hmem_each)
  have hx_mem : ∀ (τ : ℝ) (hτ : τ ∈ Set.Icc tmin tmax),
      x τ ∈ Metric.closedBall x₀ (1 : ℝ) := by
    intro τ hτ
    change z (Set.projIcc tmin tmax hle τ) ∈ _
    rw [hproj_mem τ hτ]
    exact hz_mem ⟨τ, hτ⟩
  -- integral equation for approximants
  have hint_eq : ∀ n (t : ℝ) (ht : t ∈ Set.Icc tmin tmax),
      u n t = x₀ + ∫ τ in t₀..t, F n τ (u n τ) := by
    intro n t ht
    have hcomp : u n t = (α n) ⟨t, ht⟩ := by
      change (α n).compProj t = _
      rw [ODE.FunSpace.compProj_of_mem ht]
    have hall : (α n) ⟨t, ht⟩ = ODE.picard (F n) t₀ x₀ (u n) t :=
      (ODE.FunSpace.isFixedPt_next_iff (hPL n) hx0).mp (hfp n) ⟨t, ht⟩
    rw [hcomp]
    exact hall
  have hFcont : ∀ n, Continuous (fun τ : ℝ => F n τ (u n τ)) := by
    intro n
    exact (hg_smooth n).continuous.comp (continuous_id.prodMk (hu_cont n))
  -- uniform convergence of integrands on each uIcc
  have hpair_unif : ∀ (t : ℝ), t ∈ Set.Icc tmin tmax →
      TendstoUniformlyOn (fun n τ => F (φ n) τ (u (φ n) τ)) (fun τ => f (τ, x τ))
        Filter.atTop (Set.uIcc t₀ t) := by
    intro t ht
    have hsub : Set.uIcc t₀ t ⊆ Set.Icc tmin tmax := by
      intro τ hτ
      rw [Set.mem_uIcc] at hτ
      rcases hτ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        constructor <;> linarith [ht.1, ht.2, ht₀mem.1, ht₀mem.2, h1, h2]
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    have huc : UniformContinuousOn f box :=
      hbox_compact.uniformContinuousOn_of_continuous hf.continuousOn
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨η, hη, hηf⟩ := huc (δ / 2) (by linarith)
    have hN1base := (Metric.tendstoUniformly_iff.mp hunif) (min η (δ / 2))
      (lt_min hη (by linarith))
    have hN1 : ∀ᶠ n in Filter.atTop, ∀ s : Set.Icc tmin tmax,
        dist (z s) ((((BF (φ n)) : Set.Icc tmin tmax → E)) s) < min η (δ / 2) := hN1base
    have herr : ∀ᶠ n in Filter.atTop, (1 : ℝ) / (((φ n : ℕ) : ℝ) + 1) < δ / 2 := by
      have hlim : Filter.Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hcomp : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (((φ n : ℕ) : ℝ) + 1)) Filter.atTop
          (nhds 0) := hlim.comp hφmono.tendsto_atTop
      exact hcomp.eventually (gt_mem_nhds (by linarith))
    filter_upwards [hN1, herr] with n hn1 hn2 τ hτ
    have hτIcc : τ ∈ Set.Icc tmin tmax := hsub hτ
    have hP1 : (τ, u (φ n) τ) ∈ box := hmem_box τ _ hτIcc (hu_mem _ _)
    have hP2 : (τ, x τ) ∈ box := hmem_box τ _ hτIcc (hx_mem _ hτIcc)
    have e_approx : dist (F (φ n) τ (u (φ n) τ)) (f (τ, u (φ n) τ)) < δ / 2 := by
      change dist (g (φ n) (τ, u (φ n) τ)) (f (τ, u (φ n) τ)) < δ / 2
      have h1 := hg_close (φ n) (τ, u (φ n) τ)
      linarith
    have e_unif : dist (f (τ, u (φ n) τ)) (f (τ, x τ)) < δ / 2 := by
      apply hηf _ hP1 _ hP2
      have hpd : dist ((τ, u (φ n) τ) : ℝ × E) (τ, x τ) = dist (u (φ n) τ) (x τ) := by
        simp [dist_eq_norm]
      rw [hpd]
      have e1 : ∀ m, u (φ m) τ
          = ((((BF (φ m)) : Set.Icc tmin tmax → E))) ⟨τ, hτIcc⟩ := by
        intro m
        change (α (φ m)).compProj τ = _
        have hbf : ((((BF (φ m)) : Set.Icc tmin tmax → E))) ⟨τ, hτIcc⟩
            = (α (φ m)) ⟨τ, hτIcc⟩ := rfl
        rw [ODE.FunSpace.compProj_of_mem hτIcc, hbf]
      have e2 : x τ = z ⟨τ, hτIcc⟩ := by
        change z (Set.projIcc tmin tmax hle τ) = _
        rw [hproj_mem τ hτIcc]
      rw [e1 n, e2, dist_comm]
      exact lt_of_lt_of_le (hn1 ⟨τ, hτIcc⟩) (min_le_left _ _)
    have c1 : dist (f (τ, x τ)) (f (τ, u (φ n) τ)) < δ / 2 := by
      rw [dist_comm]; exact e_unif
    have c2 : dist (f (τ, u (φ n) τ)) (F (φ n) τ (u (φ n) τ)) < δ / 2 := by
      rw [dist_comm]; exact e_approx
    calc dist (f (τ, x τ)) (F (φ n) τ (u (φ n) τ))
        ≤ dist (f (τ, x τ)) (f (τ, u (φ n) τ))
          + dist (f (τ, u (φ n) τ)) (F (φ n) τ (u (φ n) τ)) := dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := add_lt_add c1 c2
      _ = δ := by ring
  -- limit integral equation on the closed interval
  have hlim_eq : ∀ s ∈ Set.Icc tmin tmax, x s = x₀ + ∫ τ in t₀..s, f (τ, x τ) := by
    intro s hs
    have hLHS : Filter.Tendsto (fun n => u (φ n) s) Filter.atTop (nhds (x s)) := by
      have hpt := hunif.tendsto_at (⟨s, hs⟩ : Set.Icc tmin tmax)
      have e1 : ∀ n, u (φ n) s = ((((BF (φ n)) : Set.Icc tmin tmax → E))) ⟨s, hs⟩ := by
        intro n
        change (α (φ n)).compProj s = _
        have hbf : ((((BF (φ n)) : Set.Icc tmin tmax → E))) ⟨s, hs⟩
            = (α (φ n)) ⟨s, hs⟩ := rfl
        rw [ODE.FunSpace.compProj_of_mem hs, hbf]
      have e2 : x s = z ⟨s, hs⟩ := by
        change z (Set.projIcc tmin tmax hle s) = _
        rw [hproj_mem s hs]
      simpa [e1, e2] using hpt
    have hev_s : ∀ᶠ n in Filter.atTop,
        ContinuousOn (fun τ => F (φ n) τ (u (φ n) τ)) (Set.uIcc t₀ s) :=
      Filter.Eventually.of_forall (fun n => (hFcont (φ n)).continuousOn)
    have hRHS : Filter.Tendsto (fun n => x₀ + ∫ τ in t₀..s, F (φ n) τ (u (φ n) τ)) Filter.atTop
        (nhds (x₀ + ∫ τ in t₀..s, f (τ, x τ))) :=
      ((hpair_unif s hs).tendsto_intervalIntegral_of_continuousOn hev_s).const_add x₀
    have heq : (fun n => u (φ n) s)
        = (fun n => x₀ + ∫ τ in t₀..s, F (φ n) τ (u (φ n) τ)) :=
      funext (fun n => hint_eq (φ n) s hs)
    rw [heq] at hLHS
    exact tendsto_nhds_unique hLHS hRHS
  -- derivative via FTC
  have hcont_lim : Continuous (fun s => f (s, x s)) := hf.comp (continuous_id.prodMk hx_cont)
  refine ⟨ε, hε_pos, x, hx_init, ?_⟩
  intro t ht
  have htIcc : t ∈ Set.Icc tmin tmax := ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
  have hG : HasDerivAt (fun u_ => ∫ τ in t₀..u_, f (τ, x τ)) (f (t, x t)) t := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact hcont_lim.continuousOn.intervalIntegrable
    · exact hcont_lim.stronglyMeasurableAtFilter _ _
    · exact hcont_lim.continuousAt
  have hG' : HasDerivAt (fun u_ => x₀ + ∫ τ in t₀..u_, f (τ, x τ)) (f (t, x t)) t :=
    hG.const_add x₀
  refine hG'.congr_of_eventuallyEq ?_
  have hnhds : Set.Icc tmin tmax ∈ nhds t :=
    Icc_mem_nhds (by rw [htmin]; exact ht.1) (by rw [htmax]; exact ht.2)
  filter_upwards [hnhds] with s hs
  exact hlim_eq s hs

end MathlibExt.Analysis.ODE.CauchyPeanoWanted
