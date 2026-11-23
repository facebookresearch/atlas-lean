/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

namespace MathlibExt.Analysis.Calculus.NowhereDifferentiable

/-- The set of bounded continuous real functions admitting a point `x` in
`Set.Icc (-k) k` with global Lipschitz-at-`x` constant `n`. -/
private def badSet (n k : ℕ) : Set (BoundedContinuousFunction ℝ ℝ) :=
  {f | ∃ x ∈ Set.Icc (-(k : ℝ)) (k : ℝ),
    ∀ y : ℝ, ‖f y - f x‖ ≤ (n : ℝ) * ‖y - x‖}

/-- Each `badSet n k` is closed, by a compactness argument on the witnesses. -/
private lemma isClosed_badSet (n k : ℕ) : IsClosed (badSet n k) := by
  refine IsSeqClosed.isClosed ?_
  intro u f hmem hlim
  have hmem' : ∀ p : ℕ, ∃ x ∈ Set.Icc (-(k : ℝ)) (k : ℝ),
      ∀ y : ℝ, ‖u p y - u p x‖ ≤ (n : ℝ) * ‖y - x‖ := fun p => hmem p
  choose x hxI hxineq using hmem'
  obtain ⟨a, haI, φ, hφmono, hφlim⟩ := isCompact_Icc.tendsto_subseq hxI
  refine ⟨a, haI, fun y => ?_⟩
  have htop : Filter.Tendsto φ Filter.atTop Filter.atTop := hφmono.tendsto_atTop
  have hlimφ : Filter.Tendsto (u ∘ φ) Filter.atTop (nhds f) := hlim.comp htop
  have hxφ : Filter.Tendsto (fun j => x (φ j)) Filter.atTop (nhds a) := hφlim
  have h1 : Filter.Tendsto (fun j => u (φ j) y) Filter.atTop (nhds (f y)) := by
    have hmain : Filter.Tendsto (fun j => dist (u (φ j) y) (f y)) Filter.atTop
        (nhds 0) := by
      have hle : ∀ j, ‖dist (u (φ j) y) (f y)‖ ≤ dist (u (φ j)) f := fun j => by
        rw [Real.norm_of_nonneg dist_nonneg]
        exact BoundedContinuousFunction.dist_coe_le_dist y
      have e1 : Filter.Tendsto (fun j => dist (u (φ j)) f) Filter.atTop (nhds 0) := by
        have := tendsto_iff_dist_tendsto_zero.mp hlimφ
        simpa using this
      exact squeeze_zero_norm hle e1
    exact tendsto_iff_dist_tendsto_zero.mpr hmain
  have hcont : Filter.Tendsto (fun j => f (x (φ j))) Filter.atTop (nhds (f a)) :=
    ((BoundedContinuousFunction.continuous f).tendsto a).comp hxφ
  have h2 : Filter.Tendsto (fun j => u (φ j) (x (φ j))) Filter.atTop (nhds (f a)) := by
    have hmain : Filter.Tendsto (fun j => dist (u (φ j) (x (φ j))) (f a))
        Filter.atTop (nhds 0) := by
      have hle : ∀ j, ‖dist (u (φ j) (x (φ j))) (f a)‖ ≤
          dist (u (φ j)) f + dist (f (x (φ j))) (f a) := fun j => by
        rw [Real.norm_of_nonneg dist_nonneg]
        calc dist (u (φ j) (x (φ j))) (f a)
            ≤ dist (u (φ j) (x (φ j))) (f (x (φ j)))
              + dist (f (x (φ j))) (f a) := dist_triangle _ _ _
          _ ≤ dist (u (φ j)) f + dist (f (x (φ j))) (f a) :=
              add_le_add (BoundedContinuousFunction.dist_coe_le_dist _) le_rfl
      have e1 : Filter.Tendsto (fun j => dist (u (φ j)) f) Filter.atTop (nhds 0) := by
        have := tendsto_iff_dist_tendsto_zero.mp hlimφ
        simpa using this
      have e2 : Filter.Tendsto (fun j => dist (f (x (φ j))) (f a)) Filter.atTop
          (nhds 0) := tendsto_iff_dist_tendsto_zero.mp hcont
      have esum := e1.add e2
      have esum0 : Filter.Tendsto
          (fun j => dist (u (φ j)) f + dist (f (x (φ j))) (f a)) Filter.atTop
          (nhds 0) := by simpa using esum
      exact squeeze_zero_norm hle esum0
    exact tendsto_iff_dist_tendsto_zero.mpr hmain
  have hLHS : Filter.Tendsto (fun j => ‖u (φ j) y - u (φ j) (x (φ j))‖) Filter.atTop
      (nhds ‖f y - f a‖) := (h1.sub h2).norm
  have hRHS : Filter.Tendsto (fun j => (n : ℝ) * ‖y - x (φ j)‖) Filter.atTop
      (nhds ((n : ℝ) * ‖y - a‖)) :=
    tendsto_const_nhds.mul ((tendsto_const_nhds.sub hxφ).norm)
  exact le_of_tendsto_of_tendsto hLHS hRHS
    (Filter.Eventually.of_forall (fun j => hxineq (φ j) y))

/-- Each `badSet n k` has dense complement: near any `f`, a small high-frequency
sine perturbation destroys every candidate Lipschitz-at-a-point bound on
`Set.Icc (-k) k`. -/
private lemma dense_compl_badSet (n k : ℕ) : Dense (badSet n k)ᶜ := by
  rw [Metric.dense_iff]
  intro f ε hε
  set δ : ℝ := ε / 2 with hδdef
  have hδ : 0 < δ := by linarith
  have hKc : IsCompact (Set.Icc (-((k : ℝ) + 1)) ((k : ℝ) + 1)) := isCompact_Icc
  have huc := hKc.uniformContinuousOn_of_continuous
    (BoundedContinuousFunction.continuous f).continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨η, hηpos, hη⟩ := huc (δ / 4) (by linarith)
  set M : ℝ := max 4 (max (Real.pi / η + 1) (4 * (n : ℝ) * Real.pi / δ + 1)) with hMdef
  have hM4 : 4 ≤ M := le_max_left _ _
  have hMη : Real.pi / η + 1 ≤ M :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hMn : 4 * (n : ℝ) * Real.pi / δ + 1 ≤ M :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hMpos : 0 < M := by linarith
  have hMne : M ≠ 0 := ne_of_gt hMpos
  have hpiM : Real.pi / M < η := by
    have h1 : Real.pi < M * η := (div_lt_iff₀ hηpos).mp (by linarith)
    rw [div_lt_iff₀ hMpos]
    linarith [mul_comm M η]
  have hpiM1 : Real.pi / M < 1 := by
    rw [div_lt_one hMpos]
    calc Real.pi < 4 := Real.pi_lt_four
    _ ≤ M := hM4
  have hnM : (n : ℝ) * (Real.pi / M) < δ / 4 := by
    have h2 : 4 * (n : ℝ) * Real.pi / δ < M := by linarith
    have h1 : 4 * (n : ℝ) * Real.pi < M * δ := (div_lt_iff₀ hδ).mp h2
    rw [← mul_div_assoc, div_lt_iff₀ hMpos]
    linarith
  have hcont : Continuous (fun t : ℝ => δ * Real.sin (M * t)) :=
    continuous_const.mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id'))
  have hbound : ∀ t : ℝ, ‖δ * Real.sin (M * t)‖ ≤ δ := by
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hδ]
    have h := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (M * t)) hδ.le
    rwa [mul_one] at h
  set s : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup _ hcont δ hbound with hsdef
  have hs_eq : ∀ t : ℝ, s t = δ * Real.sin (M * t) := fun t => rfl
  have hdist : dist (f + s) f < ε := by
    have hnorm : ‖f + s - f‖ ≤ δ := by
      have hpt : ∀ x : ℝ, ‖(f + s - f) x‖ ≤ δ := by
        intro x
        have e : (f + s - f) x = s x := by simp
        rw [e, hs_eq x]
        exact hbound x
      exact (BoundedContinuousFunction.norm_le hδ.le).mpr hpt
    calc dist (f + s) f = ‖f + s - f‖ := dist_eq_norm _ _
      _ ≤ δ := hnorm
      _ < ε := by linarith
  have hgadd : ∀ t₁ t₂ : ℝ, (f + s) t₁ - (f + s) t₂
      = (f t₁ - f t₂) + (s t₁ - s t₂) := by
    intro t₁ t₂
    rw [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.add_apply]
    ring
  refine ⟨f + s, Metric.mem_ball.mpr hdist, ?_⟩
  rw [Set.mem_compl_iff]
  intro hcon
  obtain ⟨x, hxI, hx⟩ := hcon
  rw [Set.mem_Icc] at hxI
  obtain ⟨hxlo, hxhi⟩ := hxI
  set θ : ℝ := M * x with hθdef
  set y₁ : ℝ := x + Real.pi / M with hy1def
  set y₂ : ℝ := x + Real.pi / (2 * M) with hy2def
  have hMy1 : M * y₁ = θ + Real.pi := by
    change M * (x + Real.pi / M) = M * x + Real.pi
    field_simp
  have hMy2 : M * y₂ = θ + Real.pi / 2 := by
    change M * (x + Real.pi / (2 * M)) = M * x + Real.pi / 2
    field_simp
  have hsin1 : Real.sin (M * y₁) = -Real.sin θ := by
    rw [hMy1]; exact Real.sin_add_pi θ
  have hsin2 : Real.sin (M * y₂) = Real.cos θ := by
    rw [hMy2]; exact Real.sin_add_pi_div_two θ
  have hs1 : s y₁ - s x = δ * (-2 * Real.sin θ) := by
    rw [hs_eq y₁, hs_eq x, hsin1]; ring
  have hs2 : s y₂ - s x = δ * (Real.cos θ - Real.sin θ) := by
    rw [hs_eq y₂, hs_eq x, hsin2]; ring
  have hS1 : ‖s y₁ - s x‖ = δ * (2 * |Real.sin θ|) := by
    have e : δ * (-2 * Real.sin θ) = -(δ * (2 * Real.sin θ)) := by ring
    rw [hs1, e, norm_neg, Real.norm_eq_abs, abs_mul, abs_of_pos hδ]
    congr 1
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hS2 : ‖s y₂ - s x‖ = δ * |Real.cos θ - Real.sin θ| := by
    rw [hs2, Real.norm_eq_abs, abs_mul, abs_of_pos hδ]
  have hdich : (1 / 2 : ℝ) ≤ 2 * |Real.sin θ|
      ∨ (1 / 2 : ℝ) ≤ |Real.cos θ - Real.sin θ| := by
    by_contra hcon2
    push Not at hcon2
    obtain ⟨h1, h2⟩ := hcon2
    have hs_lt : |Real.sin θ| < 1 / 4 := by linarith
    have hc_lt : |Real.cos θ| < 3 / 4 := by
      have h3 : |Real.cos θ| - |Real.sin θ| ≤ |Real.cos θ - Real.sin θ| := by
        have h := abs_abs_sub_abs_le_abs_sub (Real.cos θ) (Real.sin θ)
        exact le_trans (le_abs_self _) h
      linarith
    have hs2 : |Real.sin θ| ^ 2 < (1 / 4) ^ 2 :=
      sq_lt_sq' (by linarith [abs_nonneg (Real.sin θ)]) hs_lt
    have hc2 : |Real.cos θ| ^ 2 < (3 / 4) ^ 2 :=
      sq_lt_sq' (by linarith [abs_nonneg (Real.cos θ)]) hc_lt
    have hsq : |Real.sin θ| ^ 2 + |Real.cos θ| ^ 2 = 1 := by
      rw [sq_abs, sq_abs]; exact Real.sin_sq_add_cos_sq θ
    linarith
  have hxK : x ∈ Set.Icc (-((k : ℝ) + 1)) ((k : ℝ) + 1) :=
    Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hmemK : ∀ z : ℝ, |z| ≤ (k : ℝ) + 1 →
      z ∈ Set.Icc (-((k : ℝ) + 1)) ((k : ℝ) + 1) := by
    intro z hz
    rw [Set.mem_Icc]
    exact ⟨neg_le_of_abs_le hz, le_of_abs_le hz⟩
  have hosc : ∀ z : ℝ, z ∈ Set.Icc (-((k : ℝ) + 1)) ((k : ℝ) + 1) →
      dist z x < η → ‖f z - f x‖ ≤ δ / 4 := by
    intro z hz hzx
    have := hη z hz x hxK hzx
    rw [dist_eq_norm] at this
    linarith
  have hy1K : y₁ ∈ Set.Icc (-((k : ℝ) + 1)) ((k : ℝ) + 1) := by
    apply hmemK
    have habsx : |x| ≤ (k : ℝ) := abs_le.mpr ⟨by linarith, hxhi⟩
    have hle : |y₁| ≤ |x| + Real.pi / M := by
      change |x + Real.pi / M| ≤ |x| + Real.pi / M
      calc |x + Real.pi / M| ≤ |x| + |Real.pi / M| := abs_add_le _ _
        _ = |x| + Real.pi / M := by
            rw [abs_of_pos (div_pos Real.pi_pos hMpos)]
    linarith
  have hy1x : dist y₁ x = Real.pi / M := by
    change dist (x + Real.pi / M) x = Real.pi / M
    have eeq : (x + Real.pi / M) - x = Real.pi / M := by ring
    rw [dist_eq_norm, eeq,
      Real.norm_of_nonneg (le_of_lt (div_pos Real.pi_pos hMpos))]
  have hn1 : (n : ℝ) * ‖y₁ - x‖ < δ / 4 := by
    have e : ‖y₁ - x‖ = Real.pi / M := by
      change ‖(x + Real.pi / M) - x‖ = Real.pi / M
      have eeq : (x + Real.pi / M) - x = Real.pi / M := by ring
      rw [eeq, Real.norm_of_nonneg (le_of_lt (div_pos Real.pi_pos hMpos))]
    rw [e]; exact hnM
  have hrel : Real.pi / (2 * M) = (Real.pi / M) / 2 := by ring
  have hpos2M : (0 : ℝ) < Real.pi / (2 * M) := by
    rw [hrel]
    exact div_pos (div_pos Real.pi_pos hMpos) two_pos
  have hy2K : y₂ ∈ Set.Icc (-((k : ℝ) + 1)) ((k : ℝ) + 1) := by
    apply hmemK
    have habsx : |x| ≤ (k : ℝ) := abs_le.mpr ⟨by linarith, hxhi⟩
    have hle : |y₂| ≤ |x| + Real.pi / M := by
      have h2M : Real.pi / (2 * M) ≤ Real.pi / M := by
        rw [hrel]
        have hpos : 0 ≤ Real.pi / M := le_of_lt (div_pos Real.pi_pos hMpos)
        linarith
      change |x + Real.pi / (2 * M)| ≤ |x| + Real.pi / M
      calc |x + Real.pi / (2 * M)| ≤ |x| + |Real.pi / (2 * M)| := abs_add_le _ _
        _ = |x| + Real.pi / (2 * M) := by rw [abs_of_pos hpos2M]
        _ ≤ |x| + Real.pi / M := by linarith
    linarith
  have hy2x : dist y₂ x < η := by
    have ed2 : dist y₂ x = Real.pi / (2 * M) := by
      change dist (x + Real.pi / (2 * M)) x = Real.pi / (2 * M)
      have eeq : (x + Real.pi / (2 * M)) - x = Real.pi / (2 * M) := by ring
      rw [dist_eq_norm, eeq, Real.norm_of_nonneg (le_of_lt hpos2M)]
    rw [ed2, hrel]
    have hpos : 0 < Real.pi / M := div_pos Real.pi_pos hMpos
    linarith
  have hn2 : (n : ℝ) * ‖y₂ - x‖ < δ / 4 := by
    have e : ‖y₂ - x‖ = Real.pi / (2 * M) := by
      change ‖(x + Real.pi / (2 * M)) - x‖ = Real.pi / (2 * M)
      have eeq : (x + Real.pi / (2 * M)) - x = Real.pi / (2 * M) := by ring
      rw [eeq, Real.norm_of_nonneg (le_of_lt hpos2M)]
    rw [e, hrel]
    have hnn : 0 ≤ (n : ℝ) * (Real.pi / M) :=
      mul_nonneg (Nat.cast_nonneg _) (le_of_lt (div_pos Real.pi_pos hMpos))
    linarith
  rcases hdich with hcase | hcase
  · have htri : ‖s y₁ - s x‖ ≤ ‖(f + s) y₁ - (f + s) x‖ + ‖f y₁ - f x‖ := by
      have e : s y₁ - s x = ((f + s) y₁ - (f + s) x) - (f y₁ - f x) := by
        rw [hgadd]; ring
      rw [e]
      exact norm_sub_le _ _
    have hbig : δ / 4 ≤ ‖(f + s) y₁ - (f + s) x‖ := by
      have h1 : δ * (1 / 2) ≤ δ * (2 * |Real.sin θ|) :=
        mul_le_mul_of_nonneg_left hcase hδ.le
      have hosc1 := hosc y₁ hy1K (by rw [hy1x]; exact hpiM)
      linarith [hS1, htri]
    have hle := hx y₁
    linarith [hn1]
  · have htri : ‖s y₂ - s x‖ ≤ ‖(f + s) y₂ - (f + s) x‖ + ‖f y₂ - f x‖ := by
      have e : s y₂ - s x = ((f + s) y₂ - (f + s) x) - (f y₂ - f x) := by
        rw [hgadd]; ring
      rw [e]
      exact norm_sub_le _ _
    have hbig : δ / 4 ≤ ‖(f + s) y₂ - (f + s) x‖ := by
      have h1 : δ * (1 / 2) ≤ δ * |Real.cos θ - Real.sin θ| :=
        mul_le_mul_of_nonneg_left hcase hδ.le
      have hosc2 := hosc y₂ hy2K hy2x
      linarith [hS2, htri]
    have hle := hx y₂
    linarith [hn2]

/-- A function differentiable at `x` lies in some `badSet`: differentiability
gives a local Lipschitz bound, boundedness handles the far-field. -/
private lemma mem_badSet_of_differentiable (f : BoundedContinuousFunction ℝ ℝ) (x : ℝ)
    (h : DifferentiableAt ℝ (⇑f) x) :
    ∃ m : ℕ, f ∈ badSet m.unpair.1 m.unpair.2 := by
  obtain ⟨f', hf'⟩ := h
  have hloc := Asymptotics.isLittleO_iff.mp hf'.isLittleO one_pos
  obtain ⟨r, hrpos, hr⟩ := Metric.eventually_nhds_iff_ball.mp hloc
  have hnear : ∀ y : ℝ, y ∈ Metric.ball x r → ‖⇑f y - ⇑f x‖ ≤ (‖f'‖ + 1) * dist y x := by
    intro y hy
    have hy' := hr y hy
    have hop : ‖f' (y - x)‖ ≤ ‖f'‖ * ‖y - x‖ :=
      ContinuousLinearMap.le_opNorm f' (y - x)
    have hde : dist y x = ‖y - x‖ := dist_eq_norm y x
    have hsplit : ⇑f y - ⇑f x = (⇑f y - ⇑f x - f' (y - x)) + f' (y - x) := by ring
    calc ‖⇑f y - ⇑f x‖
        = ‖(⇑f y - ⇑f x - f' (y - x)) + f' (y - x)‖ := congrArg _ hsplit
      _ ≤ ‖⇑f y - ⇑f x - f' (y - x)‖ + ‖f' (y - x)‖ := norm_add_le _ _
      _ ≤ 1 * ‖y - x‖ + ‖f'‖ * ‖y - x‖ := add_le_add hy' hop
      _ = (‖f'‖ + 1) * dist y x := by rw [hde]; ring
  have hB : ∀ y : ℝ, ‖⇑f y‖ ≤ ‖f‖ :=
    fun y => BoundedContinuousFunction.norm_coe_le_norm f y
  have hr2 : (0 : ℝ) < r / 2 := half_pos hrpos
  have hC : ∀ y : ℝ, ‖⇑f y - ⇑f x‖
      ≤ max (‖f'‖ + 1) ((‖f‖ + ‖⇑f x‖) / (r / 2)) * dist y x := by
    intro y
    by_cases hnear' : y ∈ Metric.ball x r
    · calc ‖⇑f y - ⇑f x‖ ≤ (‖f'‖ + 1) * dist y x := hnear y hnear'
        _ ≤ max (‖f'‖ + 1) ((‖f‖ + ‖⇑f x‖) / (r / 2)) * dist y x := by
            apply mul_le_mul_of_nonneg_right _ dist_nonneg
            exact le_max_left _ _
    · have hfar : r / 2 ≤ dist y x := by
        have hle : r ≤ dist y x :=
          le_of_not_gt (fun h => hnear' (Metric.mem_ball.mpr h))
        linarith
      have hCnn : 0 ≤ (‖f‖ + ‖⇑f x‖) / (r / 2) :=
        div_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (le_of_lt hr2)
      have hbound : ‖⇑f y - ⇑f x‖ ≤ (‖f‖ + ‖⇑f x‖) / (r / 2) * dist y x := by
        have h1 : ‖⇑f y - ⇑f x‖ ≤ ‖f‖ + ‖⇑f x‖ := by
          calc ‖⇑f y - ⇑f x‖ ≤ ‖⇑f y‖ + ‖⇑f x‖ := norm_sub_le _ _
            _ ≤ ‖f‖ + ‖⇑f x‖ := add_le_add (hB y) le_rfl
        have h2 : (‖f‖ + ‖⇑f x‖) = (‖f‖ + ‖⇑f x‖) / (r / 2) * (r / 2) :=
          (div_mul_cancel₀ _ (ne_of_gt hr2)).symm
        calc ‖⇑f y - ⇑f x‖ ≤ ‖f‖ + ‖⇑f x‖ := h1
          _ = (‖f‖ + ‖⇑f x‖) / (r / 2) * (r / 2) := h2
          _ ≤ (‖f‖ + ‖⇑f x‖) / (r / 2) * dist y x :=
              mul_le_mul_of_nonneg_left hfar hCnn
      calc ‖⇑f y - ⇑f x‖ ≤ (‖f‖ + ‖⇑f x‖) / (r / 2) * dist y x := hbound
        _ ≤ max (‖f'‖ + 1) ((‖f‖ + ‖⇑f x‖) / (r / 2)) * dist y x := by
            apply mul_le_mul_of_nonneg_right _ dist_nonneg
            exact le_max_right _ _
  refine ⟨Nat.pair ⌈max (‖f'‖ + 1) ((‖f‖ + ‖⇑f x‖) / (r / 2))⌉₊ ⌈|x|⌉₊, ?_⟩
  simp only [Nat.unpair_pair]
  refine ⟨x, Set.mem_Icc.mpr ⟨?_, ?_⟩, fun y => ?_⟩
  · have hxle : |x| ≤ (⌈|x|⌉₊ : ℝ) := Nat.le_ceil _
    exact neg_le_of_abs_le hxle
  · exact le_of_abs_le (Nat.le_ceil _)
  · calc ‖f y - f x‖
        ≤ max (‖f'‖ + 1) ((‖f‖ + ‖⇑f x‖) / (r / 2)) * dist y x := hC y
      _ ≤ (⌈max (‖f'‖ + 1) ((‖f‖ + ‖⇑f x‖) / (r / 2))⌉₊ : ℝ) * dist y x := by
          apply mul_le_mul_of_nonneg_right _ dist_nonneg
          exact Nat.le_ceil _
      _ = (⌈max (‖f'‖ + 1) ((‖f‖ + ‖⇑f x‖) / (r / 2))⌉₊ : ℝ) * ‖y - x‖ := by
          rw [dist_eq_norm]

/--
**A continuous nowhere differentiable function.** There exists a continuous function
$f : \mathbb{R} \to \mathbb{R}$ that is differentiable at no point of $\mathbb{R}$.

Source: K. Weierstrass, 1872 lecture; P. du Bois-Reymond, J. Reine Angew. Math. 79 (1875), 21-37,
DOI 10.1515/crll.1875.79.21.
Proves `Wanted` entry `exists_continuous_nowhere_differentiable`.
-/
theorem exists_continuous_nowhere_differentiable :
    ∃ f : C(ℝ, ℝ), ∀ x, ¬ DifferentiableAt ℝ f x := by
  have hD : Dense (⋂ (m : ℕ), (badSet m.unpair.1 m.unpair.2)ᶜ) :=
    dense_iInter_of_isOpen_nat (fun m : ℕ => (isClosed_badSet _ _).isOpen_compl)
      (fun m : ℕ => dense_compl_badSet _ _)
  obtain ⟨f₀, hf₀⟩ := Dense.nonempty hD
  rw [Set.mem_iInter] at hf₀
  refine ⟨f₀.toContinuousMap, fun x hx => ?_⟩
  have hx' : DifferentiableAt ℝ (⇑f₀) x := by
    rwa [BoundedContinuousFunction.coe_toContinuousMap] at hx
  obtain ⟨m, hm⟩ := mem_badSet_of_differentiable f₀ x hx'
  exact (hf₀ m) hm

end MathlibExt.Analysis.Calculus.NowhereDifferentiable
