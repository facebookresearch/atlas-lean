/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.HolomorphicFamilyEquicontinuity
import Code.FrontierA.LeeYangRealAnchor

open Filter Metric Set Topology
open scoped UniformConvergence

namespace StatMech.FrontierA

open StatMech.FK



structure CompactExhaustion (U : Set ℂ) where
  sets : ℕ → Set ℂ
  isCompact : ∀ n, IsCompact (sets n)
  subset : ∀ n, sets n ⊆ U
  cofinal : ∀ K : Set ℂ, IsCompact K → K ⊆ U → ∃ n, K ⊆ sets n




theorem holomorphicFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion
    (F : ℕ → ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hbounded : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ n z, z ∈ K → ‖F n z‖ ≤ C)
    (E : CompactExhaustion U) :
    IsLocallyUniformlySequentiallyPrecompact F U := by
  classical
  intro φ hφ
  let X : ℕ → Type := fun n => E.sets n →ᵤ ℂ
  let S : ∀ n, Set (X n) := fun n => closure (Set.range (fun k =>
    UniformFun.ofFun (fun z : E.sets n => F (φ k) z)))
  have hS : ∀ n, IsCompact (S n) := by
    intro n
    simpa only [S, X] using
      (holomorphicFamily_restrictionClosure_compact
        (fun k => F (φ k)) U hU (fun k => hF (φ k))
        (fun K hK hKU => by
          obtain ⟨C, hC⟩ := hbounded K hK hKU
          exact ⟨C, fun k => hC (φ k)⟩)
        (E.sets n) (E.isCompact n) (E.subset n))
  let P : Set (∀ n, X n) := Set.univ.pi S
  have hP : IsCompact P := by
    simpa only [P] using isCompact_univ_pi hS
  let x : ℕ → ∀ n, X n := fun k n =>
    UniformFun.ofFun (fun z : E.sets n => F (φ k) z)
  have hx : ∀ k, x k ∈ P := by
    intro k n _hn
    exact subset_closure ⟨k, rfl⟩
  obtain ⟨a, ha, ψ, hψ, hlim⟩ := hP.tendsto_subseq hx
  have hcoord : ∀ n, TendstoUniformly
      (fun k (z : E.sets n) => F (φ (ψ k)) z)
      (fun z => a n z) atTop := by
    intro n
    have hn : Tendsto (fun k => x (ψ k) n) atTop (nhds (a n)) :=
      (tendsto_pi_nhds.mp hlim) n
    have hu := UniformFun.tendsto_iff_tendstoUniformly.mp hn
    simpa only [x, Function.comp_apply] using hu
  let pick : ∀ z : ℂ, z ∈ U → ℕ := fun z hz =>
    Classical.choose (E.cofinal {z} isCompact_singleton (by simpa using hz))
  have hpick : ∀ (z : ℂ) (hz : z ∈ U), z ∈ E.sets (pick z hz) := by
    intro z hz
    exact Classical.choose_spec
      (E.cofinal {z} isCompact_singleton (by simpa using hz)) (by simp)
  let g : ℂ → ℂ := fun z => if hz : z ∈ U then
    a (pick z hz) ⟨z, hpick z hz⟩ else 0
  have hg_coord : ∀ n z (hz : z ∈ E.sets n), g z = a n ⟨z, hz⟩ := by
    intro n z hz
    have hzU : z ∈ U := E.subset n hz
    simp only [g, dif_pos hzU]
    have hp := (hcoord (pick z hzU)).tendsto_at ⟨z, hpick z hzU⟩
    have hn := (hcoord n).tendsto_at ⟨z, hz⟩
    apply tendsto_nhds_unique
      (show Tendsto (fun k => F (φ (ψ k)) z) atTop
        (nhds (a (pick z hzU) ⟨z, hpick z hzU⟩)) by simpa using hp)
    exact (show Tendsto (fun k => F (φ (ψ k)) z) atTop
      (nhds (a n ⟨z, hz⟩)) by simpa using hn)
  refine ⟨ψ, hψ, g, ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  obtain ⟨n, hKn⟩ := E.cofinal K hK hKU
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have hevent := (Metric.tendstoUniformly_iff.mp (hcoord n)) epsilon hepsilon
  filter_upwards [hevent] with k hk
  intro z hz
  rw [hg_coord n z (hKn hz)]
  exact hk ⟨z, hKn hz⟩



def rightHalfPlaneCompact (n : ℕ) : Set ℂ :=
  closedBall 0 (n + 1 : ℝ) ∩ {z : ℂ | (1 : ℝ) / (n + 1) ≤ z.re}

theorem rightHalfPlaneCompact_isCompact (n : ℕ) :
    IsCompact (rightHalfPlaneCompact n) := by
  apply (isCompact_closedBall (0 : ℂ) (n + 1 : ℝ)).inter_right
  exact isClosed_le continuous_const Complex.continuous_re

theorem rightHalfPlaneCompact_subset (n : ℕ) :
    rightHalfPlaneCompact n ⊆ {z : ℂ | 0 < z.re} := by
  intro z hz
  have hden : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  exact (div_pos zero_lt_one hden).trans_le hz.2

theorem rightHalfPlaneCompact_cofinal
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ {z : ℂ | 0 < z.re}) :
    ∃ n, K ⊆ rightHalfPlaneCompact n := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, empty_subset _⟩
  obtain ⟨z₀, hz₀K, hz₀min⟩ :=
    hK.exists_isMinOn hKne Complex.continuous_re.continuousOn
  have hz₀pos : 0 < z₀.re := hKU hz₀K
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  obtain ⟨n, hn⟩ := exists_nat_gt (max C (1 / z₀.re))
  refine ⟨n, fun z hz => ⟨?_, ?_⟩⟩
  · rw [mem_closedBall, dist_zero_right]
    have hnorm : ‖z‖ ≤ C := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)] using hC z hz
    exact hnorm.trans ((le_max_left C (1 / z₀.re)).trans hn.le |>.trans (by norm_num))
  · have hrecip : (1 : ℝ) / (n + 1) ≤ z₀.re := by
      rw [one_div_le (by positivity) hz₀pos]
      exact ((le_max_right C (1 / z₀.re)).trans hn.le).trans (by norm_num)
    exact hrecip.trans (isMinOn_iff.mp hz₀min z hz)


def rightHalfPlaneCompactExhaustion :
    CompactExhaustion {z : ℂ | 0 < z.re} where
  sets := rightHalfPlaneCompact
  isCompact := rightHalfPlaneCompact_isCompact
  subset := rightHalfPlaneCompact_subset
  cofinal := rightHalfPlaneCompact_cofinal


def leftHalfPlaneCompact (n : ℕ) : Set ℂ :=
  closedBall 0 (n + 1 : ℝ) ∩ {z : ℂ | z.re ≤ -((1 : ℝ) / (n + 1))}

theorem leftHalfPlaneCompact_isCompact (n : ℕ) :
    IsCompact (leftHalfPlaneCompact n) := by
  apply (isCompact_closedBall (0 : ℂ) (n + 1 : ℝ)).inter_right
  exact isClosed_le Complex.continuous_re continuous_const

theorem leftHalfPlaneCompact_subset (n : ℕ) :
    leftHalfPlaneCompact n ⊆ {z : ℂ | z.re < 0} := by
  intro z hz
  have hden : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  exact hz.2.trans_lt (neg_neg_of_pos (div_pos zero_lt_one hden))

theorem leftHalfPlaneCompact_cofinal
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ {z : ℂ | z.re < 0}) :
    ∃ n, K ⊆ leftHalfPlaneCompact n := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, empty_subset _⟩
  obtain ⟨z₀, hz₀K, hz₀max⟩ :=
    hK.exists_isMaxOn hKne Complex.continuous_re.continuousOn
  have hz₀neg : z₀.re < 0 := hKU hz₀K
  have hdelta : 0 < -z₀.re := neg_pos.mpr hz₀neg
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  obtain ⟨n, hn⟩ := exists_nat_gt (max C (1 / (-z₀.re)))
  refine ⟨n, fun z hz => ⟨?_, ?_⟩⟩
  · rw [mem_closedBall, dist_zero_right]
    have hnorm : ‖z‖ ≤ C := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)] using hC z hz
    exact hnorm.trans ((le_max_left C (1 / (-z₀.re))).trans hn.le |>.trans (by norm_num))
  · have hrecip : (1 : ℝ) / (n + 1) ≤ -z₀.re := by
      rw [one_div_le (by positivity) hdelta]
      exact ((le_max_right C (1 / (-z₀.re))).trans hn.le).trans (by norm_num)
    have hzmax : z.re ≤ z₀.re := isMaxOn_iff.mp hz₀max z hz
    exact hzmax.trans (by simpa only [neg_neg] using neg_le_neg hrecip)


def leftHalfPlaneCompactExhaustion :
    CompactExhaustion {z : ℂ | z.re < 0} where
  sets := leftHalfPlaneCompact
  isCompact := leftHalfPlaneCompact_isCompact
  subset := leftHalfPlaneCompact_subset
  cofinal := leftHalfPlaneCompact_cofinal



theorem leeYangBox_normalizedFieldLogDerivative_precompact_rightHalfPlane
    (d : ℕ) {beta : ℝ} (hbeta : 0 < beta) :
    IsLocallyUniformlySequentiallyPrecompact
      (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
      {z : ℂ | 0 < z.re} := by
  let F : ℕ → ℂ → ℂ := fun n =>
    leeYangNormalizedFieldLogDerivative (boxGraph d n) beta
  have hdata :=
    leeYangBox_normalizedFieldLogDerivative_normalFamilyData_rightHalfPlane d hbeta
  exact holomorphicFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion
    F {z : ℂ | 0 < z.re}
    (isOpen_lt continuous_const Complex.continuous_re)
    hdata.1 hdata.2 rightHalfPlaneCompactExhaustion


theorem leeYangBox_normalizedFieldLogDerivative_precompact_leftHalfPlane
    (d : ℕ) {beta : ℝ} (hbeta : 0 < beta) :
    IsLocallyUniformlySequentiallyPrecompact
      (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
      {z : ℂ | z.re < 0} := by
  let F : ℕ → ℂ → ℂ := fun n =>
    leeYangNormalizedFieldLogDerivative (boxGraph d n) beta
  have hdata :=
    leeYangBox_normalizedFieldLogDerivative_normalFamilyData_leftHalfPlane d hbeta
  exact holomorphicFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion
    F {z : ℂ | z.re < 0}
    (isOpen_lt Complex.continuous_re continuous_const)
    hdata.1 hdata.2 leftHalfPlaneCompactExhaustion



theorem leeYangBox_normalizedFieldLogDerivative_rightHalfPlane
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta) :
    ∃ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn
        (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        g atTop {z : ℂ | 0 < z.re} ∧
      DifferentiableOn ℂ g {z : ℂ | 0 < z.re} ∧
      TendstoLocallyUniformlyOn
        (deriv ∘ fun n =>
          leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        (deriv g) atTop {z : ℂ | 0 < z.re} :=
  leeYangBox_normalizedFieldLogDerivative_rightHalfPlane_of_precompact
    d hd hbeta
    (leeYangBox_normalizedFieldLogDerivative_precompact_rightHalfPlane d hbeta)



theorem leeYangBox_normalizedFieldLogDerivative_leftHalfPlane
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta) :
    ∃ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn
        (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        g atTop {z : ℂ | z.re < 0} ∧
      DifferentiableOn ℂ g {z : ℂ | z.re < 0} ∧
      TendstoLocallyUniformlyOn
        (deriv ∘ fun n =>
          leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        (deriv g) atTop {z : ℂ | z.re < 0} :=
  leeYangBox_normalizedFieldLogDerivative_leftHalfPlane_of_precompact
    d hd hbeta
    (leeYangBox_normalizedFieldLogDerivative_precompact_leftHalfPlane d hbeta)

end StatMech.FrontierA
