/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section

section
open scoped BigOperators Pointwise

namespace MetaMathlibExt.UniversalApprox

/-- 1-D predicate: g is approximable by σ-nets uniformly on [-R, R]. -/
private def sigmaApprox (σ g : ℝ → ℝ) : Prop :=
  ∀ (R : ℝ) (ε : ℝ), 0 < ε →
    ∃ (m : ℕ) (c w b : Fin m → ℝ),
      ∀ t : ℝ, |t| ≤ R → |g t - ∑ i, c i * σ (w i * t + b i)| < ε

/-- n-D predicate: f is approximable by σ-nets uniformly on K. -/
private def netApproxOn (σ : ℝ → ℝ) {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (f : E → ℝ) : Prop :=
  ∀ (ε : ℝ), 0 < ε →
    ∃ (m : ℕ) (c : Fin m → ℝ) (W : Fin m → E) (b : Fin m → ℝ),
      ∀ x ∈ K, |f x - ∑ i, c i * σ (inner ℝ (W i) x + b i)| < ε

private theorem sigmaApprox_zero (σ : ℝ → ℝ) : sigmaApprox σ 0 := by
  intro R ε hε
  exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun t _ => by simpa using hε⟩

private theorem sigmaApprox_single (σ : ℝ → ℝ) (a d : ℝ) :
    sigmaApprox σ (fun t ↦ σ (a * t + d)) := by
  intro R ε hε
  refine ⟨1, fun _ => 1, fun _ => a, fun _ => d, fun t _ => ?_⟩
  simp only [Fin.sum_univ_one, one_mul]
  rw [sub_self]
  simp [abs_zero, hε]

private theorem sigmaApprox_add (σ g h : ℝ → ℝ) (hg : sigmaApprox σ g)
    (hh : sigmaApprox σ h) : sigmaApprox σ (g + h) := by
  intro R ε hε
  have hε2 : (0:ℝ) < ε / 2 := by linarith
  obtain ⟨m₁, c₁, w₁, b₁, h₁⟩ := hg R (ε/2) hε2
  obtain ⟨m₂, c₂, w₂, b₂, h₂⟩ := hh R (ε/2) hε2
  refine ⟨m₁ + m₂, Fin.append c₁ c₂, Fin.append w₁ w₂, Fin.append b₁ b₂, fun t ht => ?_⟩
  have e1 := h₁ t ht
  have e2 := h₂ t ht
  have hsum : (∑ i : Fin (m₁ + m₂), (Fin.append c₁ c₂) i
        * σ ((Fin.append w₁ w₂) i * t + (Fin.append b₁ b₂) i))
      = (∑ i : Fin m₁, c₁ i * σ (w₁ i * t + b₁ i))
        + (∑ i : Fin m₂, c₂ i * σ (w₂ i * t + b₂ i)) := by
    rw [Fin.sum_univ_add]
    congr 1
    · apply Finset.sum_congr rfl; intro i _
      simp only [Fin.append_left]
    · apply Finset.sum_congr rfl; intro i _
      simp only [Fin.append_right]
  simp only [Pi.add_apply] at *
  rw [hsum]
  calc |(g t + h t) - ((∑ i : Fin m₁, c₁ i * σ (w₁ i * t + b₁ i))
          + (∑ i : Fin m₂, c₂ i * σ (w₂ i * t + b₂ i)))|
      = |(g t - (∑ i : Fin m₁, c₁ i * σ (w₁ i * t + b₁ i)))
          + (h t - (∑ i : Fin m₂, c₂ i * σ (w₂ i * t + b₂ i)))| := by
        congr 1
        ring
    _ ≤ _ + _ := abs_add_le _ _
    _ < ε/2 + ε/2 := add_lt_add e1 e2
    _ = ε := by ring

private theorem sigmaApprox_const_mul (σ g : ℝ → ℝ) (a : ℝ) (hg : sigmaApprox σ g) :
    sigmaApprox σ (fun t ↦ a * g t) := by
  intro R ε hε
  by_cases ha : a = 0
  · subst ha
    refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun t _ => ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
    simp [abs_zero, hε]
  · have hpos : (0:ℝ) < |a| + 1 := by positivity
    have hε' : (0:ℝ) < ε / (|a| + 1) := by positivity
    obtain ⟨m, c, w, b, h⟩ := hg R (ε / (|a| + 1)) hε'
    refine ⟨m, fun i => a * c i, w, b, fun t ht => ?_⟩
    have e := h t ht
    have hsum : (∑ i : Fin m, (a * c i) * σ (w i * t + b i))
        = a * (∑ i : Fin m, c i * σ (w i * t + b i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [hsum]
    have heq : a * g t - a * (∑ i, c i * σ (w i * t + b i))
        = a * (g t - (∑ i, c i * σ (w i * t + b i))) := by ring
    rw [heq, abs_mul]
    have hlt : |a| * |g t - ∑ i, c i * σ (w i * t + b i)| < |a| * (ε / (|a| + 1)) :=
      mul_lt_mul_of_pos_left e (by rw [abs_pos]; exact ha)
    have hle : |a| * (ε / (|a| + 1)) < ε := by
      have hdiv : |a| / (|a| + 1) < 1 := by
        rw [div_lt_one hpos]; linarith [abs_nonneg a]
      calc |a| * (ε / (|a| + 1)) = ε * (|a| / (|a| + 1)) := by ring
        _ < ε * 1 := mul_lt_mul_of_pos_left hdiv hε
        _ = ε := by ring
    linarith

private theorem sigmaApprox_sum {ι : Type*} (σ : ℝ → ℝ) (s : Finset ι) (g : ι → ℝ → ℝ)
    (hg : ∀ i ∈ s, sigmaApprox σ (g i)) :
    sigmaApprox σ (fun t ↦ ∑ i ∈ s, g i t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : (fun t => ∑ i ∈ (∅ : Finset ι), g i t) = 0 := by funext t; simp
    rw [this]
    exact sigmaApprox_zero σ
  | insert a s ha ih =>
    have ha' : ∀ i ∈ s, sigmaApprox σ (g i) := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hga : sigmaApprox σ (g a) := hg a (Finset.mem_insert_self a s)
    have ih' := ih ha'
    have hadd := sigmaApprox_add σ (g a) (fun t => ∑ i ∈ s, g i t) hga ih'
    have heq : (fun t => ∑ i ∈ insert a s, g i t) = ((g a) + (fun t => ∑ i ∈ s, g i t)) := by
      funext t
      simp [Finset.sum_insert ha, Pi.add_apply]
    rw [heq]
    exact hadd

private theorem sigmaApprox_affine_comp (σ g : ℝ → ℝ) (hg : sigmaApprox σ g) (a d : ℝ) :
    sigmaApprox σ (fun t ↦ g (a * t + d)) := by
  intro R ε hε
  set R' := |a| * |R| + |d| with hR'
  obtain ⟨m, c, w, b, h⟩ := hg R' ε hε
  refine ⟨m, c, fun i => w i * a, fun i => w i * d + b i, fun t ht => ?_⟩
  have hmem : |a * t + d| ≤ R' := by
    calc |a * t + d| ≤ |a * t| + |d| := abs_add_le _ _
      _ = |a| * |t| + |d| := by rw [abs_mul]
      _ ≤ |a| * |R| + |d| := by
          have hle : |t| ≤ |R| := le_trans ht (le_abs_self R)
          gcongr
  have e := h (a * t + d) hmem
  have hsum : (∑ i : Fin m, c i * σ ((w i * a) * t + (w i * d + b i)))
      = (∑ i : Fin m, c i * σ (w i * (a * t + d) + b i)) := by
    apply Finset.sum_congr rfl; intro i _
    congr 1; congr 1; ring
  rw [hsum]
  exact e

private theorem sigmaApprox_of_near (σ g : ℝ → ℝ)
    (h : ∀ (R : ℝ) (ε : ℝ), 0 < ε → ∃ h : ℝ → ℝ,
      sigmaApprox σ h ∧ ∀ t : ℝ, |t| ≤ R → |g t - h t| < ε) :
    sigmaApprox σ g := by
  intro R ε hε
  have hε2 : (0:ℝ) < ε / 2 := by linarith
  obtain ⟨hfun, hhapprox, hnear⟩ := h R (ε/2) hε2
  obtain ⟨m, c, w, b, happ⟩ := hhapprox R (ε/2) hε2
  refine ⟨m, c, w, b, fun t ht => ?_⟩
  have e1 := hnear t ht
  have e2 := happ t ht
  calc |g t - ∑ i, c i * σ (w i * t + b i)|
      = |(g t - hfun t) + (hfun t - ∑ i, c i * σ (w i * t + b i))| := by congr 1; ring
    _ ≤ |g t - hfun t| + |hfun t - ∑ i, c i * σ (w i * t + b i)| := abs_add_le _ _
    _ < ε/2 + ε/2 := add_lt_add e1 e2
    _ = ε := by ring

private theorem riemann_sum_uniform
    (F : ℝ → ℝ → ℝ) (hF : Continuous (Function.uncurry F))
    {a b : ℝ} (hab : a ≤ b) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ t : ℝ, |t| ≤ R →
      |(∫ s in a..b, F t s)
        - ∑ j ∈ Finset.range N, ((b - a) / N) * F t (a + j * ((b - a) / N))|
        < ε := by
  have hKc : IsCompact (Set.Icc (-R) R ×ˢ Set.Icc a b) :=
    isCompact_Icc.prod isCompact_Icc
  have huc := hKc.uniformContinuousOn_of_continuous hF.continuousOn
  have hba : (0 : ℝ) ≤ b - a := sub_nonneg.mpr hab
  have hden : (0 : ℝ) < b - a + 1 := by linarith
  set η : ℝ := ε / (b - a + 1) with hη
  have hηpos : 0 < η := div_pos hε hden
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp huc η hηpos
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · simp only [Nat.cast_zero] at hN
      have hnn : (0 : ℝ) ≤ (b - a) / δ := div_nonneg hba (le_of_lt hδpos)
      linarith
    · exact hpos
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hNe : (N : ℝ) ≠ 0 := ne_of_gt hN'
  set h : ℝ := (b - a) / N with hh
  have hh_nonneg : 0 ≤ h := div_nonneg hba (le_of_lt hN')
  have hh_lt : h < δ := by
    have h1 : b - a < (N : ℝ) * δ := (div_lt_iff₀ hδpos).mp hN
    have h2 : δ * (N : ℝ) = (N : ℝ) * δ := mul_comm _ _
    rw [hh, div_lt_iff₀ hN', h2]
    exact h1
  set g : ℕ → ℝ := fun j => a + (j : ℝ) * h with hg
  have hNh : (N : ℝ) * h = b - a := by
    rw [hh]
    exact mul_div_cancel₀ _ hNe
  have hg0 : g 0 = a := by simp only [hg, Nat.cast_zero, zero_mul, add_zero]
  have hgN : g N = b := by
    simp only [hg]
    linarith [hNh]
  have hgle : ∀ j ≤ N, g j ≤ b := by
    intro j hj
    have hjN : (j : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hj
    have hmul : (j : ℝ) * h ≤ (N : ℝ) * h :=
      mul_le_mul_of_nonneg_right hjN hh_nonneg
    simp only [hg]
    linarith [hmul, hNh]
  have hge : ∀ j, a ≤ g j := by
    intro j
    simp only [hg]
    have hmul : (0 : ℝ) ≤ (j : ℝ) * h := mul_nonneg (Nat.cast_nonneg j) hh_nonneg
    linarith
  have hg_succ : ∀ j, g (j + 1) - g j = h := by
    intro j
    simp only [hg]
    push_cast
    ring
  have hcont_s : ∀ t, Continuous (fun s => F t s) := fun t =>
    hF.comp (continuous_const.prodMk continuous_id)
  have hint : ∀ t j, IntervalIntegrable (fun s => F t s) MeasureTheory.volume (g j)
      (g (j + 1)) :=
    fun t j => (hcont_s t).intervalIntegrable _ _
  refine ⟨N, hNpos, fun t ht => ?_⟩
  have htmem : t ∈ Set.Icc (-R) R := abs_le.mp ht
  have hsplit : (∫ s in a..b, F t s)
      = ∑ j ∈ Finset.range N, ∫ s in g j..g (j + 1), F t s := by
    have hsum := intervalIntegral.sum_integral_adjacent_intervals
      (fun k _ => hint t k) (f := fun s => F t s) (μ := MeasureTheory.volume)
      (a := g) (n := N)
    rw [hg0, hgN] at hsum
    exact hsum.symm
  have hgr : ∀ j ∈ Finset.range N, a + (j : ℝ) * ((b - a) / N) = g j := by
    intro j _
    simp only [hg, hh]
  have hsum_eq :
      (∑ j ∈ Finset.range N, ((b - a) / (N : ℝ)) * F t (a + j * ((b - a) / N)))
      = ∑ j ∈ Finset.range N, h * F t (g j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hgr j hj, hh]
  have hsub : ∀ j ∈ Finset.range N,
      ∫ s in g j..g (j + 1), (F t s - F t (g j))
        = (∫ s in g j..g (j + 1), F t s) - h * F t (g j) := by
    intro j _
    have h1 : ∫ s in g j..g (j + 1), (F t s - F t (g j))
        = (∫ s in g j..g (j + 1), F t s) - ∫ s in g j..g (j + 1), F t (g j) :=
      intervalIntegral.integral_sub (hint t j)
        (continuous_const.intervalIntegrable (g j) (g (j + 1)))
    rw [intervalIntegral.integral_const] at h1
    rw [hg_succ j, smul_eq_mul] at h1
    exact h1
  have hbound : ∀ j ∈ Finset.range N,
      ‖∫ s in g j..g (j + 1), (F t s - F t (g j))‖ ≤ η * h := by
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    have hle : g j ≤ g (j + 1) := by
      have hdiff : g (j + 1) - g j = h := hg_succ j
      linarith [hh_nonneg]
    have hle2 : ∀ x ∈ Set.uIoc (g j) (g (j + 1)), ‖F t x - F t (g j)‖ ≤ η := by
      intro x hx
      rw [Set.uIoc_of_le hle] at hx
      have hx1 : g j ≤ x := le_of_lt (Set.mem_Ioc.mp hx).1
      have hx2 : x ≤ g (j + 1) := (Set.mem_Ioc.mp hx).2
      have hjN' : j + 1 ≤ N := Nat.succ_le_of_lt hjN
      have hxI : x ∈ Set.Icc a b :=
        ⟨le_trans (hge j) hx1, le_trans hx2 (hgle _ hjN')⟩
      have hgI : g j ∈ Set.Icc a b := ⟨hge j, hgle j (le_of_lt hjN)⟩
      have hdist : dist (t, x) (t, g j) < δ := by
        rw [dist_prod_same_left, Real.dist_eq]
        have hxx : |x - g j| ≤ h := by
          rw [abs_of_nonneg (sub_nonneg.mpr hx1)]
          linarith [hg_succ j]
        linarith [hxx, hh_lt]
      have hmem := hδ (t, x) ⟨htmem, hxI⟩ (t, g j) ⟨htmem, hgI⟩ hdist
      rw [Real.dist_eq] at hmem
      rw [Real.norm_eq_abs]
      exact le_of_lt hmem
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := g j) (b := g (j + 1)) (C := η) (f := fun s => F t s - F t (g j)) hle2
    rw [hg_succ j, abs_of_nonneg hh_nonneg] at hnorm
    exact hnorm
  rw [hsplit, hsum_eq, ← Finset.sum_sub_distrib]
  calc |∑ j ∈ Finset.range N, ((∫ s in g j..g (j + 1), F t s) - h * F t (g j))|
      ≤ ∑ j ∈ Finset.range N, |(∫ s in g j..g (j + 1), F t s) - h * F t (g j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N, η * h := by
        apply Finset.sum_le_sum
        intro j hj
        rw [← hsub j hj, ← Real.norm_eq_abs]
        exact hbound j hj
    _ = (N : ℝ) * (η * h) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ < ε := by
        have hfrac : (b - a) / (b - a + 1) < 1 := by
          rw [div_lt_one hden]
          linarith
        have heq : (N : ℝ) * (η * h) = ε * ((b - a) / (b - a + 1)) := by
          calc (N : ℝ) * (η * h) = (η) * ((N : ℝ) * h) := by ring
            _ = η * (b - a) := by rw [hNh]
            _ = ε * ((b - a) / (b - a + 1)) := by rw [hη]; ring
        rw [heq]
        calc ε * ((b - a) / (b - a + 1)) < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
          _ = ε := mul_one ε

private theorem uniform_first_order_taylor
    (G : ℝ → ℝ) (hG : Differentiable ℝ G) (hG' : Continuous (deriv G))
    (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ y s : ℝ, |y| ≤ M → |s| ≤ η →
      |G (y + s) - G y - deriv G y * s| ≤ ε * |s| := by
  have hKc : IsCompact (Set.Icc (-M - 1) (M + 1)) := isCompact_Icc
  have huc := hKc.uniformContinuousOn_of_continuous hG'.continuousOn
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff_le.mp huc ε hε
  refine ⟨min δ 1, lt_min hδpos zero_lt_one, fun y s hy hs => ?_⟩
  have hs1 : |s| ≤ 1 := le_trans hs (min_le_right _ _)
  have hsδ : |s| ≤ δ := le_trans hs (min_le_left _ _)
  have hy' := abs_le.mp hy
  have hs' := abs_le.mp hs1
  have hyI : y ∈ Set.Icc (-M - 1) (M + 1) := by
    rw [Set.mem_Icc]
    constructor <;> linarith [hy'.1, hy'.2]
  have hysI : y + s ∈ Set.Icc (-M - 1) (M + 1) := by
    rw [Set.mem_Icc]
    constructor <;> linarith [hy'.1, hy'.2, hs'.1, hs'.2]
  have hseg : ∀ u ∈ Set.uIcc y (y + s),
      u ∈ Set.Icc (-M - 1) (M + 1) ∧ |u - y| ≤ |s| := by
    intro u hu
    rw [Set.mem_uIcc] at hu
    rcases hu with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
    · have hmem : u ∈ Set.Icc (-M - 1) (M + 1) := by
        rw [Set.mem_Icc]
        constructor <;> linarith [hy'.1, hy'.2, hs'.1, hs'.2, hlo, hhi]
      have hab : |u - y| ≤ |s| := by
        rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
        have hsle : s ≤ |s| := le_abs_self s
        linarith [hhi, hsle]
      exact ⟨hmem, hab⟩
    · have hmem : u ∈ Set.Icc (-M - 1) (M + 1) := by
        rw [Set.mem_Icc]
        constructor <;> linarith [hy'.1, hy'.2, hs'.1, hs'.2, hlo, hhi]
      have hab : |u - y| ≤ |s| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hhi)]
        have hsle : -s ≤ |s| := by
          have h := le_abs_self (-s)
          rwa [abs_neg] at h
        linarith [hlo, hsle]
      exact ⟨hmem, hab⟩
  set c : ℝ := deriv G y with hc
  set H : ℝ → ℝ := fun u => G u - c * u with hH
  have hHd : ∀ u ∈ Set.uIcc y (y + s), DifferentiableAt ℝ H u := by
    intro u _
    exact (hG u).sub (differentiableAt_id.const_mul c)
  have hHderiv : ∀ u, deriv H u = deriv G u - c := by
    intro u
    have e : deriv H u = deriv G u - deriv (fun u => c * u) u :=
      deriv_sub (hG u) (differentiableAt_id.const_mul c)
    have e2 : deriv (fun u => c * u) u = c := by simp
    rw [e, e2]
  have hHle : ∀ u ∈ Set.uIcc y (y + s), ‖deriv H u‖ ≤ ε := by
    intro u hu
    rw [hHderiv u, Real.norm_eq_abs]
    have hdist : dist u y ≤ δ := by
      rw [Real.dist_eq]
      exact le_trans (hseg u hu).2 hsδ
    have hmem := hδ u (hseg u hu).1 y hyI hdist
    rw [Real.dist_eq] at hmem
    rwa [hc]
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (f := H)
    (s := Set.uIcc y (y + s)) (C := ε) hHd hHle (convex_uIcc y (y + s))
    Set.left_mem_uIcc Set.right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have hHeq : H (y + s) - H y = G (y + s) - G y - c * s := by
    simp only [hH]
    ring
  have hseq : (y + s) - y = s := by ring
  rw [hHeq, hseq] at hmvt
  rwa [hc] at hmvt

private theorem netApproxOn_zero (σ : ℝ → ℝ) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (K : Set E) :
    netApproxOn σ K 0 := by
  intro ε hε
  exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun x _ => by simpa using hε⟩

private theorem netApproxOn_add (σ : ℝ → ℝ) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} {g h : E → ℝ} (hg : netApproxOn σ K g) (hh : netApproxOn σ K h) :
    netApproxOn σ K (g + h) := by
  intro ε hε
  have hε2 : (0:ℝ) < ε / 2 := by linarith
  obtain ⟨m₁, c₁, W₁, b₁, h₁⟩ := hg (ε/2) hε2
  obtain ⟨m₂, c₂, W₂, b₂, h₂⟩ := hh (ε/2) hε2
  refine ⟨m₁ + m₂, Fin.append c₁ c₂, Fin.append W₁ W₂, Fin.append b₁ b₂, fun x hx => ?_⟩
  have e1 := h₁ x hx
  have e2 := h₂ x hx
  have hsum : (∑ i : Fin (m₁ + m₂), (Fin.append c₁ c₂) i
        * σ (inner ℝ ((Fin.append W₁ W₂) i) x + (Fin.append b₁ b₂) i))
      = (∑ i : Fin m₁, c₁ i * σ (inner ℝ (W₁ i) x + b₁ i))
        + (∑ i : Fin m₂, c₂ i * σ (inner ℝ (W₂ i) x + b₂ i)) := by
    rw [Fin.sum_univ_add]
    congr 1
    · apply Finset.sum_congr rfl; intro i _
      simp only [Fin.append_left]
    · apply Finset.sum_congr rfl; intro i _
      simp only [Fin.append_right]
  simp only [Pi.add_apply] at *
  rw [hsum]
  calc |(g x + h x) - ((∑ i : Fin m₁, c₁ i * σ (inner ℝ (W₁ i) x + b₁ i))
          + (∑ i : Fin m₂, c₂ i * σ (inner ℝ (W₂ i) x + b₂ i)))|
      = |(g x - (∑ i : Fin m₁, c₁ i * σ (inner ℝ (W₁ i) x + b₁ i)))
          + (h x - (∑ i : Fin m₂, c₂ i * σ (inner ℝ (W₂ i) x + b₂ i)))| := by
        congr 1
        ring
    _ ≤ _ + _ := abs_add_le _ _
    _ < ε/2 + ε/2 := add_lt_add e1 e2
    _ = ε := by ring

private theorem netApproxOn_const_mul (σ : ℝ → ℝ) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} {g : E → ℝ} (a : ℝ) (hg : netApproxOn σ K g) :
    netApproxOn σ K (fun x ↦ a * g x) := by
  intro ε hε
  by_cases ha : a = 0
  · subst ha
    refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun x _ => ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
    simp [abs_zero, hε]
  · have hpos : (0:ℝ) < |a| + 1 := by positivity
    have hε' : (0:ℝ) < ε / (|a| + 1) := by positivity
    obtain ⟨m, c, W, b, h⟩ := hg (ε / (|a| + 1)) hε'
    refine ⟨m, fun i => a * c i, W, b, fun x hx => ?_⟩
    have e := h x hx
    have hsum : (∑ i : Fin m, (a * c i) * σ (inner ℝ (W i) x + b i))
        = a * (∑ i : Fin m, c i * σ (inner ℝ (W i) x + b i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [hsum]
    have heq : a * g x - a * (∑ i, c i * σ (inner ℝ (W i) x + b i))
        = a * (g x - (∑ i, c i * σ (inner ℝ (W i) x + b i))) := by ring
    rw [heq, abs_mul]
    have hlt : |a| * |g x - ∑ i, c i * σ (inner ℝ (W i) x + b i)| < |a| * (ε / (|a| + 1)) :=
      mul_lt_mul_of_pos_left e (by rw [abs_pos]; exact ha)
    have hle : |a| * (ε / (|a| + 1)) < ε := by
      have hdiv : |a| / (|a| + 1) < 1 := by
        rw [div_lt_one hpos]; linarith [abs_nonneg a]
      calc |a| * (ε / (|a| + 1)) = ε * (|a| / (|a| + 1)) := by ring
        _ < ε * 1 := mul_lt_mul_of_pos_left hdiv hε
        _ = ε := by ring
    linarith

private theorem netApproxOn_of_near (σ : ℝ → ℝ) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Set E} {f : E → ℝ}
    (h : ∀ (ε : ℝ), 0 < ε → ∃ h : E → ℝ, netApproxOn σ K h ∧ ∀ x ∈ K, |f x - h x| < ε) :
    netApproxOn σ K f := by
  intro ε hε
  have hε2 : (0:ℝ) < ε / 2 := by linarith
  obtain ⟨hfun, hhapprox, hnear⟩ := h (ε/2) hε2
  obtain ⟨m, c, W, b, happ⟩ := hhapprox (ε/2) hε2
  refine ⟨m, c, W, b, fun x hx => ?_⟩
  have e1 := hnear x hx
  have e2 := happ x hx
  calc |f x - ∑ i, c i * σ (inner ℝ (W i) x + b i)|
      = |(f x - hfun x) + (hfun x - ∑ i, c i * σ (inner ℝ (W i) x + b i))| := by congr 1; ring
    _ ≤ _ + _ := abs_add_le _ _
    _ < ε/2 + ε/2 := add_lt_add e1 e2
    _ = ε := by ring

private theorem netApproxOn_ridge (σ g : ℝ → ℝ) (hg : sigmaApprox σ g)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} (hK : IsCompact K) (v : E) :
    netApproxOn σ K (fun x ↦ g (inner ℝ v x)) := by
  intro ε hε
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun x : E => x) continuousOn_id
  set R := ‖v‖ * max C 0 with hR
  obtain ⟨m, c, w, b, h⟩ := hg R ε hε
  refine ⟨m, c, fun i => w i • v, b, fun x hx => ?_⟩
  have hxnorm : ‖x‖ ≤ C := hC x hx
  have hmem : |inner ℝ v x| ≤ R := by
    calc |inner ℝ v x| ≤ ‖v‖ * ‖x‖ := abs_real_inner_le_norm v x
      _ ≤ ‖v‖ * max C 0 := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg v)
          exact le_max_of_le_left hxnorm
  have e := h (inner ℝ v x) hmem
  have hsum : (∑ i : Fin m, c i * σ (inner ℝ ((fun i => w i • v) i) x + b i))
      = (∑ i : Fin m, c i * σ (w i * inner ℝ v x + b i)) := by
    apply Finset.sum_congr rfl; intro i _
    congr 1; congr 1
    rw [real_inner_smul_left]
  rw [hsum]
  exact e

private theorem polynomial_of_tendsto_degreeLT (k : ℕ) (P : ℕ → Polynomial ℝ) (σ : ℝ → ℝ)
    (hdeg : ∀ j, (P j).degree < (k : WithBot ℕ))
    (hlim : ∀ x, Filter.Tendsto (fun j => (P j).eval x) Filter.atTop (nhds (σ x))) :
    ∃ p : Polynomial ℝ, ∀ x, σ x = p.eval x := by
  classical
  set v : Fin k → ℝ := fun i => (i.val : ℝ) with hv
  have hinj : Set.InjOn v (Finset.univ : Finset (Fin k)) := by
    intro a _ b _ hab
    simp only [hv, Nat.cast_inj] at hab
    exact Fin.val_injective hab
  have hcard : (Finset.univ : Finset (Fin k)).card = k := by simp
  have heq : ∀ j, P j = Lagrange.interpolate Finset.univ v (fun i => (P j).eval (v i)) := by
    intro j
    exact Lagrange.eq_interpolate hinj (by rw [hcard]; exact hdeg j)
  set p : Polynomial ℝ := Lagrange.interpolate Finset.univ v (fun i => σ (v i)) with hp
  refine ⟨p, fun x => ?_⟩
  have hlimx : Filter.Tendsto (fun j => (P j).eval x) Filter.atTop (nhds (σ x)) := hlim x
  have heval : ∀ j, (P j).eval x
      = ∑ i : Fin k, (P j).eval (v i) * ((Lagrange.basis Finset.univ v i).eval x) := by
    intro j
    conv_lhs => rw [heq j]
    rw [Lagrange.interpolate_apply]
    simp [Polynomial.eval_finsetSum]
  have hlim2 : Filter.Tendsto (fun j => (P j).eval x) Filter.atTop (nhds (p.eval x)) := by
    simp_rw [heval]
    have hnode : ∀ i ∈ (Finset.univ : Finset (Fin k)),
        Filter.Tendsto (fun j => (P j).eval (v i) * ((Lagrange.basis Finset.univ v i).eval x))
          Filter.atTop (nhds (σ (v i) * ((Lagrange.basis Finset.univ v i).eval x))) := by
      intro i _
      exact (hlim (v i)).mul_const _
    have hsum := tendsto_finsetSum Finset.univ (fun i hi => hnode i hi)
    simpa [hp, Lagrange.interpolate_apply, Polynomial.eval_finsetSum] using hsum
  exact tendsto_nhds_unique hlimx hlim2

private theorem natCast_lt_top_smooth (k : ℕ) :
    (k : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  rw [← WithTop.coe_natCast, WithTop.coe_lt_coe]
  exact WithTop.coe_lt_top k

private theorem natCast_le_top_smooth (k : ℕ) :
    (k : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  rw [← WithTop.coe_natCast, WithTop.coe_le_coe]
  exact le_top

private theorem sigmaApprox_weight_step (σ G : ℝ → ℝ)
    (hG1 : Differentiable ℝ G) (hG1' : Continuous (deriv G))
    (k : ℕ) (b : ℝ)
    (IH : ∀ w : ℝ, sigmaApprox σ (fun t ↦ t ^ k * G (w * t + b))) (w : ℝ) :
    sigmaApprox σ (fun t ↦ t ^ (k + 1) * deriv G (w * t + b)) := by
  apply sigmaApprox_of_near σ _ (fun R ε hε => ?_)
  set e' : ℝ := ε / (|R| ^ (k + 1) + 1) with he'
  have hRnn : (0 : ℝ) ≤ |R| ^ (k + 1) := pow_nonneg (abs_nonneg R) _
  have hden : (0 : ℝ) < |R| ^ (k + 1) + 1 := by linarith
  have he'pos : 0 < e' := div_pos hε hden
  set M : ℝ := |w| * |R| + |b| with hM
  obtain ⟨η, hηpos, hη⟩ := uniform_first_order_taylor G hG1 hG1' M he'pos
  have hR1 : (0 : ℝ) < |R| + 1 := by
    have habs := abs_nonneg R
    linarith
  set δ : ℝ := η / (|R| + 1) with hδ
  have hδpos : 0 < δ := div_pos hηpos hR1
  have hδne : δ ≠ 0 := ne_of_gt hδpos
  have hg1 : sigmaApprox σ (fun t ↦ t ^ k * G ((w + δ) * t + b)) := IH (w + δ)
  have hg2 : sigmaApprox σ (fun t ↦ t ^ k * G (w * t + b)) := IH w
  have hg2n : sigmaApprox σ (fun t ↦ (-1) * (t ^ k * G (w * t + b))) :=
    sigmaApprox_const_mul σ _ (-1) hg2
  have hsum := sigmaApprox_add σ _ _ hg1 hg2n
  have hQ : sigmaApprox σ
      (fun t ↦ (1 / δ)
        * (t ^ k * G ((w + δ) * t + b) + (-1) * (t ^ k * G (w * t + b)))) :=
    sigmaApprox_const_mul σ _ (1 / δ) hsum
  refine ⟨_, hQ, fun t ht => ?_⟩
  have htR : |t| ≤ |R| := le_trans ht (le_abs_self R)
  have htk : |t| ^ k ≤ |R| ^ k := pow_le_pow_left₀ (abs_nonneg t) htR k
  have hys : (w + δ) * t + b = (w * t + b) + δ * t := by ring
  have hyM : |w * t + b| ≤ M := by
    simp only [hM]
    calc |w * t + b| ≤ |w * t| + |b| := abs_add_le _ _
      _ = |w| * |t| + |b| := by rw [abs_mul]
      _ ≤ |w| * |R| + |b| := by gcongr
  have hsη : |δ * t| ≤ η := by
    have hδe : (0 : ℝ) < η / (|R| + 1) := div_pos hηpos hR1
    have h2 : (η / (|R| + 1)) * |t| ≤ (η / (|R| + 1)) * |R| :=
      mul_le_mul_of_nonneg_left htR (le_of_lt hδe)
    have h3 : (η / (|R| + 1)) * |R| ≤ η := by
      have h4 : (η / (|R| + 1)) * |R| = η * (|R| / (|R| + 1)) := by ring
      have h5 : |R| / (|R| + 1) ≤ 1 := by
        rw [div_le_one hR1]
        have habs := abs_nonneg R
        linarith
      calc (η / (|R| + 1)) * |R| = η * (|R| / (|R| + 1)) := h4
        _ ≤ η * 1 := mul_le_mul_of_nonneg_left h5 (le_of_lt hηpos)
        _ = η := mul_one η
    have hdt : |δ * t| = (η / (|R| + 1)) * |t| := by
      rw [hδ, abs_mul, abs_of_pos hδe]
    rw [hdt]
    exact le_trans h2 h3
  have hest := hη (w * t + b) (δ * t) hyM hsη
  rw [← hys] at hest
  set A : ℝ := G ((w + δ) * t + b) with hA
  set B : ℝ := G (w * t + b) with hB
  set D : ℝ := deriv G (w * t + b) with hD
  have hest' : |A - B - D * (δ * t)| ≤ e' * |δ * t| := hest
  have heq : (1 / δ) * (t ^ k * A + (-1) * (t ^ k * B)) - t ^ (k + 1) * D
      = t ^ k * ((A - B - D * (δ * t)) / δ) := by
    rw [pow_succ]
    field_simp
    ring
  have hE : |(A - B - D * (δ * t)) / δ| ≤ e' * |t| := by
    have hδabs : (0 : ℝ) < |δ| := abs_pos.mpr hδne
    rw [abs_div]
    rw [div_le_iff₀ hδabs]
    calc |A - B - D * (δ * t)| ≤ e' * (|δ| * |t|) := by
            rw [← abs_mul]
            exact hest'
      _ = (e' * |t|) * |δ| := by ring
  have hElt : |t| ^ k * |(A - B - D * (δ * t)) / δ| ≤ |R| ^ k * (e' * |t|) :=
    mul_le_mul htk hE (abs_nonneg _) (pow_nonneg (abs_nonneg R) k)
  have hfin : |R| ^ k * (e' * |t|) < ε := by
    have hfrac : |R| ^ (k + 1) / (|R| ^ (k + 1) + 1) < 1 := by
      rw [div_lt_one hden]
      linarith [hRnn]
    have heq2 : |R| ^ k * (e' * |t|) ≤ e' * |R| ^ (k + 1) := by
      have hmul : |R| ^ k * |t| ≤ |R| ^ k * |R| :=
        mul_le_mul_of_nonneg_left htR (pow_nonneg (abs_nonneg R) k)
      calc |R| ^ k * (e' * |t|) = e' * (|R| ^ k * |t|) := by ring
        _ ≤ e' * (|R| ^ k * |R|) :=
          mul_le_mul_of_nonneg_left hmul (le_of_lt he'pos)
        _ = e' * |R| ^ (k + 1) := by rw [pow_succ]
    have heq3 : e' * |R| ^ (k + 1)
        = ε * (|R| ^ (k + 1) / (|R| ^ (k + 1) + 1)) := by
      rw [he']
      ring
    calc |R| ^ k * (e' * |t|) ≤ e' * |R| ^ (k + 1) := heq2
      _ = ε * (|R| ^ (k + 1) / (|R| ^ (k + 1) + 1)) := heq3
      _ < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
      _ = ε := mul_one ε
  change |t ^ (k + 1) * D - (1 / δ) * (t ^ k * A + (-1) * (t ^ k * B))| < ε
  rw [abs_sub_comm, heq, abs_mul, abs_pow]
  exact lt_of_le_of_lt hElt hfin

private theorem sigmaApprox_weight_derivative (σ g : ℝ → ℝ)
    (hg : sigmaApprox σ g) (hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (k : ℕ) (w b : ℝ) :
    sigmaApprox σ (fun t ↦ t ^ k * iteratedDeriv k g (w * t + b)) := by
  induction k generalizing w b with
  | zero =>
    have heq : (fun t ↦ t ^ 0 * iteratedDeriv 0 g (w * t + b))
        = (fun t ↦ g (w * t + b)) := by
      funext t
      simp only [pow_zero, iteratedDeriv_zero, one_mul]
    rw [heq]
    exact sigmaApprox_affine_comp σ g hg w b
  | succ k IH =>
    have hG1 : Differentiable ℝ (iteratedDeriv k g) :=
      ContDiff.differentiable_iteratedDeriv k hgs (natCast_lt_top_smooth k)
    have hG1' : Continuous (deriv (iteratedDeriv k g)) := by
      rw [← iteratedDeriv_succ]
      exact ContDiff.continuous_iteratedDeriv (k + 1) hgs
        (natCast_le_top_smooth (k + 1))
    have hstep := sigmaApprox_weight_step σ (iteratedDeriv k g) hG1 hG1' k b
      (fun w => IH w b) w
    have heq : (fun t ↦ t ^ (k + 1) * deriv (iteratedDeriv k g) (w * t + b))
        = (fun t ↦ t ^ (k + 1) * iteratedDeriv (k + 1) g (w * t + b)) := by
      funext t
      rw [iteratedDeriv_succ]
    rwa [heq] at hstep

private noncomputable def mollify (φ : ContDiffBump (0 : ℝ)) (σ : ℝ → ℝ) :
    ℝ → ℝ :=
  MeasureTheory.convolution (φ.normed MeasureTheory.volume) σ
    (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume

private theorem mollify_smooth (σ : ℝ → ℝ) (hσ : Continuous σ)
    (φ : ContDiffBump (0 : ℝ)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mollify φ σ) :=
  HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (ContDiffBump.hasCompactSupport_normed φ) (ContDiffBump.contDiff_normed φ)
    hσ.locallyIntegrable

private theorem mollify_eq_integral (σ : ℝ → ℝ) (φ : ContDiffBump (0 : ℝ))
    (t : ℝ) :
    mollify φ σ t
      = ∫ s in (-φ.rOut)..φ.rOut,
        (φ.normed MeasureTheory.volume) s * σ (t - s) := by
  set ψ : ℝ → ℝ := φ.normed MeasureTheory.volume with hψ
  set r : ℝ := φ.rOut with hr
  have hrpos : 0 < r := φ.rOut_pos
  have hle : -r ≤ r := by linarith
  have hsupp : ∀ s ∉ Metric.ball (0 : ℝ) r, ψ s = 0 := by
    intro s hs
    have hmem : s ∉ Function.support ψ := by
      rw [hψ, ContDiffBump.support_normed_eq, ← hr]
      exact hs
    by_contra hne
    exact hmem (Function.mem_support.mpr hne)
  have hconv : mollify φ σ t = ∫ s, ψ s * σ (t - s) := by
    simp only [mollify, hψ, MeasureTheory.convolution_lsmul, smul_eq_mul]
  have hIoc : (∫ s, ψ s * σ (t - s))
      = ∫ s in Set.Ioc (-r) r, ψ s * σ (t - s) := by
    apply (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
    intro s hs
    have hbeq : Metric.ball (0 : ℝ) r = Set.Ioo (-r) r := by
      rw [Real.ball_eq_Ioo]
      simp only [zero_sub, zero_add]
    have hball : s ∉ Metric.ball (0 : ℝ) r := by
      rw [hbeq]
      exact fun hmem => hs (Set.Ioo_subset_Ioc_self hmem)
    rw [hsupp s hball, zero_mul]
  rw [hconv, intervalIntegral.integral_of_le hle]
  exact hIoc

private theorem mollify_sigmaApprox (σ : ℝ → ℝ) (hσ : Continuous σ)
    (φ : ContDiffBump (0 : ℝ)) : sigmaApprox σ (mollify φ σ) := by
  set ψ : ℝ → ℝ := φ.normed MeasureTheory.volume with hψ
  set r : ℝ := φ.rOut with hr
  have hrpos : 0 < r := φ.rOut_pos
  have hab : -r ≤ r := by linarith
  have hψcont : Continuous ψ := ContDiffBump.continuous_normed φ
  have hF : Continuous
      (Function.uncurry (fun t s => ψ s * σ (t - s))) :=
    (hψcont.comp continuous_snd).mul (hσ.comp (continuous_fst.sub continuous_snd))
  intro R ε hε
  obtain ⟨N, hNpos, herr⟩ :=
    riemann_sum_uniform (fun t s => ψ s * σ (t - s)) hF hab R hε
  set h : ℝ := (r - -r) / N with hh
  have hgint : ∀ t, mollify φ σ t = ∫ s in (-r)..r, ψ s * σ (t - s) :=
    fun t => mollify_eq_integral σ φ t
  refine ⟨N, fun j => h * ψ (-r + (j : ℝ) * h), fun _ => 1,
    fun j => -(-r + (j : ℝ) * h), fun t ht => ?_⟩
  have e := herr t ht
  have hsum_eq :
      (∑ i : Fin N, (h * ψ (-r + (i : ℝ) * h))
          * σ (1 * t + -(-r + (i : ℝ) * h)))
        = ∑ j ∈ Finset.range N,
          h * (ψ (-r + (j : ℝ) * h) * σ (t - (-r + (j : ℝ) * h))) := by
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _
    have h1t : 1 * t + -(-r + (i : ℝ) * h) = t - (-r + (i : ℝ) * h) := by ring
    rw [h1t]
    ring
  have e2 : |mollify φ σ t
      - ∑ j ∈ Finset.range N,
        h * (ψ (-r + (j : ℝ) * h) * σ (t - (-r + (j : ℝ) * h)))| < ε := by
    rw [hgint t]
    exact e
  change |mollify φ σ t
    - ∑ i : Fin N, (h * ψ (-r + (i : ℝ) * h))
      * σ (1 * t + -(-r + (i : ℝ) * h))| < ε
  rw [hsum_eq]
  exact e2

private theorem mollify_tendsto (σ : ℝ → ℝ) (hσ : Continuous σ)
    (φ : ℕ → ContDiffBump (0 : ℝ))
    (hφ : Filter.Tendsto (fun j => (φ j).rOut) Filter.atTop (nhds 0)) (x : ℝ) :
    Filter.Tendsto (fun j => mollify (φ j) σ x) Filter.atTop (nhds (σ x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous hφ hσ x

private theorem eq_polynomial_of_iteratedDeriv_eq_zero (g : ℝ → ℝ)
    (hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (k : ℕ)
    (hder : ∀ x, iteratedDeriv k g x = 0) :
    ∃ p : Polynomial ℝ, p.degree < (k : WithBot ℕ) ∧ ∀ x, g x = p.eval x := by
  rcases k with _ | n
  · have hdeg0 : (0 : Polynomial ℝ).degree < ((0 : ℕ) : WithBot ℕ) := by
      rw [Polynomial.degree_zero]
      exact WithBot.bot_lt_coe 0
    refine ⟨0, hdeg0, fun x => ?_⟩
    have h := hder x
    rw [iteratedDeriv_zero] at h
    simp only [h, Polynomial.eval_zero]
  · set f : Fin (n + 1) → ℝ :=
      fun i => iteratedDeriv (i : ℕ) g 0 / (((i : ℕ).factorial : ℕ) : ℝ) with hf
    set p : Polynomial ℝ :=
      ∑ i, Polynomial.C (f i) * Polynomial.X ^ (i : ℕ) with hp
    have hdeg : p.degree < ((n + 1 : ℕ) : WithBot ℕ) :=
      Polynomial.degree_sum_fin_lt f
    have hpeval : ∀ x, p.eval x = ∑ i : Fin (n + 1), f i * x ^ (i : ℕ) := by
      intro x
      simp only [hp, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    refine ⟨p, hdeg, fun x => ?_⟩
    by_cases hx0 : x = 0
    · subst hx0
      have hrest :
          (∑ i : Fin n, f i.succ * (0 : ℝ) ^ ((i.succ : Fin (n + 1)) : ℕ))
          = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        have hexp : ((i.succ : Fin (n + 1)) : ℕ) ≠ 0 := by
          have hvs : ((i.succ : Fin (n + 1)) : ℕ) = (i : ℕ) + 1 := rfl
          omega
        rw [zero_pow hexp, mul_zero]
      have hf0 : f 0 = g 0 := by
        simp only [hf]
        have hv0 : ((0 : Fin (n + 1)) : ℕ) = 0 := rfl
        rw [hv0, iteratedDeriv_zero]
        rw [Nat.factorial_zero, Nat.cast_one, div_one]
      rw [hpeval, Fin.sum_univ_succ, hrest, add_zero]
      have hv0 : ((0 : Fin (n + 1)) : ℕ) = 0 := rfl
      rw [hv0, pow_zero, mul_one]
      exact hf0.symm
    · have hle : ((n : WithTop ℕ∞) + 1) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by
          rw [Nat.cast_add, Nat.cast_one]
        rw [← hcast]
        exact natCast_le_top_smooth (n + 1)
      have hco : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) g (Set.uIcc 0 x) :=
        (hgs.of_le hle).contDiffOn
      obtain ⟨x', hx', hrem⟩ :=
        taylor_mean_remainder_lagrange_iteratedDeriv (x₀ := 0) (x := x) (n := n)
          (Ne.symm hx0) hco
      have hvan : iteratedDeriv (n + 1) g x' = 0 := hder x'
      rw [hvan, zero_mul, zero_div] at hrem
      have hgx : g x = taylorWithinEval g n (Set.uIcc 0 x) 0 x :=
        sub_eq_zero.mp hrem
      have huniq : UniqueDiffOn ℝ (Set.uIcc 0 x) := by
        rcases lt_or_gt_of_ne hx0 with hneg | hpos
        · rw [Set.uIcc_of_ge (le_of_lt hneg)]
          exact uniqueDiffOn_Icc hneg
        · rw [Set.uIcc_of_le (le_of_lt hpos)]
          exact uniqueDiffOn_Icc hpos
      have htaylor : taylorWithinEval g n (Set.uIcc 0 x) 0 x = p.eval x := by
        rw [taylor_within_apply, hpeval x, Finset.sum_range]
        apply Finset.sum_congr rfl
        intro i _
        have hAt : ContDiffAt ℝ ((i : ℕ) : WithTop ℕ∞) g 0 :=
          (hgs.of_le (natCast_le_top_smooth (i : ℕ))).contDiffAt
        have hiW : iteratedDerivWithin (i : ℕ) g (Set.uIcc 0 x) 0
            = iteratedDeriv (i : ℕ) g 0 :=
          iteratedDerivWithin_eq_iteratedDeriv huniq hAt Set.left_mem_uIcc
        rw [hiW]
        simp only [hf]
        rw [sub_zero, smul_eq_mul, div_eq_mul_inv]
        ring
      rw [hgx, htaylor]

private theorem sigmaApprox_monomial (σ : ℝ → ℝ) (hσ : Continuous σ)
    (hnp : ¬ ∃ p : Polynomial ℝ, ∀ x, σ x = p.eval x) (k : ℕ) :
    sigmaApprox σ (fun t ↦ t ^ k) := by
  set φ : ℕ → ContDiffBump (0 : ℝ) := fun j =>
    ⟨1 / ((j : ℝ) + 2), 1 / ((j : ℝ) + 1), by positivity, by
      have h1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have h2 : (j : ℝ) + 1 < (j : ℝ) + 2 := by linarith
      exact one_div_lt_one_div_of_lt h1 h2⟩ with hφ
  have hrOut : Filter.Tendsto (fun j => (φ j).rOut) Filter.atTop (nhds 0) := by
    simp only [hφ]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  by_cases hcase : ∃ j b, iteratedDeriv k (mollify (φ j) σ) b ≠ 0
  · obtain ⟨j, b, hne⟩ := hcase
    have hg := mollify_sigmaApprox σ hσ (φ j)
    have hgs := mollify_smooth σ hσ (φ j)
    have hmain : sigmaApprox σ
        (fun t ↦ t ^ k * iteratedDeriv k (mollify (φ j) σ) (0 * t + b)) :=
      sigmaApprox_weight_derivative σ (mollify (φ j) σ) hg hgs k 0 b
    set c : ℝ := iteratedDeriv k (mollify (φ j) σ) b with hc
    have hfun : (fun t ↦ t ^ k * iteratedDeriv k (mollify (φ j) σ) (0 * t + b))
        = (fun t ↦ t ^ k * c) := by
      funext t
      rw [zero_mul, zero_add, hc]
    rw [hfun] at hmain
    have hcne : c ≠ 0 := hne
    have hmono := sigmaApprox_const_mul σ (fun t ↦ t ^ k * c) c⁻¹ hmain
    have hfun2 : (fun t ↦ c⁻¹ * (t ^ k * c)) = (fun t ↦ t ^ k) := by
      funext t
      calc c⁻¹ * (t ^ k * c) = (c⁻¹ * c) * t ^ k := by ring
        _ = 1 * t ^ k := by rw [inv_mul_cancel₀ hcne]
        _ = t ^ k := one_mul _
    rw [hfun2] at hmono
    exact hmono
  · push Not at hcase
    have hP : ∀ j, ∃ P : Polynomial ℝ,
        P.degree < (k : WithBot ℕ) ∧ ∀ x, mollify (φ j) σ x = P.eval x := by
      intro j
      exact eq_polynomial_of_iteratedDeriv_eq_zero (mollify (φ j) σ)
        (mollify_smooth σ hσ (φ j)) k (hcase j)
    choose P hPdeg hPeq using hP
    have hlim : ∀ x, Filter.Tendsto (fun j => (P j).eval x) Filter.atTop
        (nhds (σ x)) := by
      intro x
      have hconv := mollify_tendsto σ hσ φ hrOut x
      have heq : (fun j => (P j).eval x) = (fun j => mollify (φ j) σ x) := by
        funext j
        exact (hPeq j x).symm
      rw [heq]
      exact hconv
    obtain ⟨p, hp⟩ := polynomial_of_tendsto_degreeLT k P σ hPdeg hlim
    exact absurd ⟨p, hp⟩ hnp

private theorem sigmaApprox_polynomial (σ : ℝ → ℝ)
    (hmon : ∀ k : ℕ, sigmaApprox σ (fun t ↦ t ^ k)) (p : Polynomial ℝ) :
    sigmaApprox σ (fun t ↦ p.eval t) := by
  have heq : (fun t ↦ p.eval t)
      = (fun t ↦ ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * t ^ i) := by
    funext t
    exact Polynomial.eval_eq_sum_range t
  rw [heq]
  refine sigmaApprox_sum σ (Finset.range (p.natDegree + 1))
    (fun i t => p.coeff i * t ^ i) ?_
  intro i _
  exact sigmaApprox_const_mul σ _ _ (hmon i)

private theorem sigmaApprox_of_continuous (σ : ℝ → ℝ) (hσ : Continuous σ)
    (hnp : ¬ ∃ p : Polynomial ℝ, ∀ x, σ x = p.eval x) (g : ℝ → ℝ)
    (hg : Continuous g) : sigmaApprox σ g := by
  apply sigmaApprox_of_near σ _ (fun R ε hε => ?_)
  have hcont : ContinuousOn g (Set.Icc (-R) R) := hg.continuousOn
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-R) R g hcont ε hε
  refine ⟨fun t => p.eval t,
    sigmaApprox_polynomial σ (sigmaApprox_monomial σ hσ hnp) p, fun t ht => ?_⟩
  have hmem : t ∈ Set.Icc (-R) R := abs_le.mp ht
  have h := hp t hmem
  rw [abs_sub_comm]
  exact h

private theorem netApproxOn_sum {ι : Type*} (σ : ℝ → ℝ) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (K : Set E) (s : Finset ι)
    (g : ι → E → ℝ) (hg : ∀ i ∈ s, netApproxOn σ K (g i)) :
    netApproxOn σ K (fun x ↦ ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : (fun x => ∑ i ∈ (∅ : Finset ι), g i x) = 0 := by funext x; simp
    rw [this]
    exact netApproxOn_zero σ K
  | insert a s ha ih =>
    have ha' : ∀ i ∈ s, netApproxOn σ K (g i) :=
      fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hga : netApproxOn σ K (g a) := hg a (Finset.mem_insert_self a s)
    have ih' := ih ha'
    have hadd := netApproxOn_add σ hga ih'
    have heq : (fun x => ∑ i ∈ insert a s, g i x)
        = ((g a) + (fun x => ∑ i ∈ s, g i x)) := by
      funext x
      simp [Finset.sum_insert ha, Pi.add_apply]
    rw [heq]
    exact hadd

private theorem exists_expSum_near {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {K : Set E} (hK : IsCompact K) {f : E → ℝ}
    (hf : ContinuousOn f K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (a : Fin m → ℝ) (v : Fin m → E),
      ∀ x ∈ K, |f x - ∑ j, a j * Real.exp (inner ℝ (v j) x)| < ε := by
  set e : E → C(K, ℝ) := fun v =>
    { toFun := fun x => Real.exp (inner ℝ v (x : E)),
      continuous_toFun := Real.continuous_exp.comp
        (continuous_const.inner continuous_subtype_val) } with he
  set S : Submodule ℝ C(K, ℝ) := Submodule.span ℝ (Set.range e) with hS
  have h1 : (1 : C(K, ℝ)) ∈ S := by
    have he0 : e 0 = 1 := by
      apply ContinuousMap.ext
      intro x
      simp only [he, ContinuousMap.coe_mk, inner_zero_left, Real.exp_zero,
        ContinuousMap.one_apply]
    rw [← he0]
    exact Submodule.subset_span (Set.mem_range_self 0)
  have hsub : Set.range e * Set.range e ⊆ Set.range e := by
    rw [Set.mul_subset_iff]
    intro u hu v hv
    obtain ⟨a, rfl⟩ := hu
    obtain ⟨b, rfl⟩ := hv
    have hadd : e a * e b = e (a + b) := by
      apply ContinuousMap.ext
      intro x
      simp only [he, ContinuousMap.mul_apply, ContinuousMap.coe_mk,
        inner_add_left, Real.exp_add]
    rw [hadd]
    exact Set.mem_range_self (a + b)
  have hmul : ∀ x y : C(K, ℝ), x ∈ S → y ∈ S → x * y ∈ S := by
    intro x y hx hy
    have hmem : x * y ∈ S * S := Submodule.mul_mem_mul hx hy
    have hle : S * S ≤ S := by
      rw [hS, Submodule.span_mul_span]
      exact Submodule.span_mono hsub
    exact hle hmem
  set A : Subalgebra ℝ C(K, ℝ) := S.toSubalgebra h1 hmul with hA
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    set v : E := (x : E) - (y : E) with hv
    have hxyE : (x : E) ≠ (y : E) := fun h => hxy (Subtype.ext h)
    have hne : (x : E) - (y : E) ≠ 0 := sub_ne_zero.mpr hxyE
    have hnorm : ‖(x : E) - (y : E)‖ ≠ 0 := fun h => hne (norm_eq_zero.mp h)
    have hpos : (0 : ℝ) < ‖(x : E) - (y : E)‖ ^ 2 := by positivity
    have hdiff : inner ℝ v (x : E) - inner ℝ v (y : E)
        = ‖(x : E) - (y : E)‖ ^ 2 := by
      have h1 : inner ℝ v (x : E) - inner ℝ v (y : E) = inner ℝ v v := by
        rw [hv, inner_sub_right]
      rw [h1]
      exact real_inner_self_eq_norm_sq v
    have hinner : inner ℝ v (x : E) ≠ inner ℝ v (y : E) := by
      intro heq
      rw [heq, sub_self] at hdiff
      linarith
    have hexp : Real.exp (inner ℝ v (x : E))
        ≠ Real.exp (inner ℝ v (y : E)) := fun h => hinner (Real.exp_injective h)
    have hmemS : e v ∈ S := Submodule.subset_span (Set.mem_range_self v)
    have hmemA : e v ∈ (A : Set C(K, ℝ)) := hmemS
    refine ⟨_, Set.mem_image_of_mem _ hmemA, ?_⟩
    simp only [he, ContinuousMap.coe_mk]
    exact hexp
  have hfcont : Continuous (K.domRestrict f) := hf.domRestrict
  obtain ⟨g, hg⟩ :=
    @ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints _ _
      (isCompact_iff_compactSpace.mp hK) A hsep (K.domRestrict f) hfcont ε hε
  have hgS : (g : C(K, ℝ)) ∈ S := g.property
  rw [hS, Submodule.mem_span_set'] at hgS
  obtain ⟨m, a, v, hsum⟩ := hgS
  have hw : ∀ i, ∃ w : E, e w = (v i : C(K, ℝ)) := by
    intro i
    obtain ⟨w, hww⟩ := (v i).property
    exact ⟨w, hww⟩
  choose w hw using hw
  refine ⟨m, a, w, fun x hx => ?_⟩
  have hpt := hg ⟨x, hx⟩
  rw [Real.norm_eq_abs] at hpt
  have hcoe : (((∑ i, a i • ((v i : C(K, ℝ)))) : C(K, ℝ)) : K → ℝ)
      = ∑ i, (((a i • ((v i : C(K, ℝ)))) : C(K, ℝ)) : K → ℝ) :=
    map_sum ContinuousMap.coeFnAddMonoidHom _ _
  have happly := congrArg (fun F : K → ℝ => F ⟨x, hx⟩) hcoe
  simp only [Finset.sum_apply] at happly
  have hval : (g : C(K, ℝ)) ⟨x, hx⟩
      = ∑ j, a j * Real.exp (inner ℝ (w j) x) := by
    calc (g : C(K, ℝ)) ⟨x, hx⟩
        = (∑ i, a i • ((v i : C(K, ℝ)))) ⟨x, hx⟩ := by rw [hsum]
      _ = ∑ i, (a i • ((v i : C(K, ℝ)))) ⟨x, hx⟩ := happly
      _ = ∑ j, a j * Real.exp (inner ℝ (w j) x) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [ContinuousMap.smul_apply, smul_eq_mul]
          congr 1
          rw [← hw i]
          simp only [he, ContinuousMap.coe_mk]
  rw [hval] at hpt
  have hdom : K.domRestrict f ⟨x, hx⟩ = f x := rfl
  rw [hdom, abs_sub_comm] at hpt
  exact hpt

end MetaMathlibExt.UniversalApprox

namespace MetaMathlibExt

/-- **Universal approximation theorem.** Let $n$ be a natural number, let $\mathbb{R}^n$ carry its
standard inner product $\langle \cdot, \cdot \rangle$, let $K \subseteq \mathbb{R}^n$ be compact,
and let $\sigma : \mathbb{R} \to \mathbb{R}$ be continuous and not a polynomial, that is, there is
no real polynomial $p$ with $\sigma(x) = p(x)$ for all real $x$. Then for every function
$f : \mathbb{R}^n \to \mathbb{R}$ that is continuous on $K$ and every $\varepsilon > 0$ there exist
$m \in \mathbb{N}$, real numbers $c_1, \dots, c_m$ and $b_1, \dots, b_m$, and vectors
$w_1, \dots, w_m \in \mathbb{R}^n$ such that
$\left| f(x) - \sum_{i=1}^{m} c_i \, \sigma(\langle w_i, x \rangle + b_i) \right| < \varepsilon$
for every $x \in K$.

In words: single-hidden-layer feedforward networks with a continuous, non-polynomial activation
approximate every continuous function uniformly on every compact set.

Proves `Wanted` entry `universal_approximation`.

Source: `universal-approximation-s1` from
https://en.wikipedia.org/wiki/Universal_approximation_theorem; the continuous-activation case of
M. Leshno, V. Ya. Lin, A. Pinkus and S. Schocken, *Multilayer feedforward networks with a
nonpolynomial activation function can approximate any function*, Neural Networks 6(6) (1993),
861–867, doi:10.1016/S0893-6080(05)80131-5, which allows any locally bounded, piecewise
continuous activation that is not almost everywhere equal to a polynomial; for continuous
activations this is the same as the pointwise non-polynomial hypothesis.
-/
theorem universal_approximation :
    ∀ {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (_hK : IsCompact K)
      {σ : ℝ → ℝ} (_hσ : Continuous σ)
      (_hnp : ¬ ∃ p : Polynomial ℝ, ∀ x, σ x = p.eval x)
      {f : EuclideanSpace ℝ (Fin n) → ℝ} (_hf : ContinuousOn f K)
      {ε : ℝ} (_hε : 0 < ε),
      ∃ (m : ℕ) (c : Fin m → ℝ) (W : Fin m → EuclideanSpace ℝ (Fin n))
        (b : Fin m → ℝ),
        ∀ x ∈ K, |f x - ∑ i, c i * σ (@inner ℝ _ _ (W i) x + b i)| < ε := by
  intro n K hK σ hσ hnp f hf ε hε
  have hexp : UniversalApprox.sigmaApprox σ Real.exp :=
    UniversalApprox.sigmaApprox_of_continuous σ hσ hnp Real.exp
      Real.continuous_exp
  have hnet : UniversalApprox.netApproxOn σ K f := by
    refine UniversalApprox.netApproxOn_of_near σ (fun ε' hε' => ?_)
    obtain ⟨m, a, v, herr⟩ := UniversalApprox.exists_expSum_near hK hf hε'
    refine ⟨fun x => ∑ j, a j * Real.exp (inner ℝ (v j) x), ?_, fun x hx => ?_⟩
    · refine UniversalApprox.netApproxOn_sum σ K Finset.univ
        (fun j x => a j * Real.exp (inner ℝ (v j) x)) ?_
      intro j _
      have hridge := UniversalApprox.netApproxOn_ridge σ Real.exp hexp hK (v j)
      exact UniversalApprox.netApproxOn_const_mul σ (a j) hridge
    · exact herr x hx
  obtain ⟨m, c, W, b, h⟩ := hnet ε hε
  exact ⟨m, c, W, b, h⟩

end MetaMathlibExt
end
