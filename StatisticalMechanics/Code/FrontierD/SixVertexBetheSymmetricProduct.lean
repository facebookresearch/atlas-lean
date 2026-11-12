/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierD.SixVertexBetheScattering
import Code.FrontierD.SixVertexBetheThermodynamicReduction

open Finset Matrix Filter Topology

namespace StatMech.FrontierD


noncomputable def sixVertexBethePhase (p : ℝ) : ℂ :=
  Complex.exp (Complex.I * p)


noncomputable def sixVertexBetheL (c : ℝ) (z : ℂ) : ℂ :=
  1 + (c : ℂ) ^ 2 * z / (1 - z)


noncomputable def sixVertexBetheM (c : ℝ) (z : ℂ) : ℂ :=
  1 - (c : ℂ) ^ 2 / (1 - z)

theorem sixVertexBethePhase_norm (p : ℝ) :
    ‖sixVertexBethePhase p‖ = 1 := by
  simp [sixVertexBethePhase, Complex.norm_exp]

theorem sixVertexBethePhase_neg (p : ℝ) :
    sixVertexBethePhase (-p) = star (sixVertexBethePhase p) := by
  unfold sixVertexBethePhase
  simpa using Complex.exp_conj (Complex.I * (p : ℂ))


theorem sixVertexBetheM_phase_neg (c p : ℝ) :
    sixVertexBetheM c (sixVertexBethePhase (-p)) =
      star (sixVertexBetheM c (sixVertexBethePhase p)) := by
  rw [sixVertexBethePhase_neg]
  simp [sixVertexBetheM]



theorem sixVertexBetheL_phase_eq_conj_M (c p : ℝ) :
    sixVertexBetheL c (sixVertexBethePhase p) =
      star (sixVertexBetheM c (sixVertexBethePhase p)) := by
  let z := sixVertexBethePhase p
  have hn : ‖z‖ = 1 := sixVertexBethePhase_norm p
  have hz : z ≠ 0 := norm_ne_zero_iff.mp (by simp [hn])
  change sixVertexBetheL c z = (starRingEnd ℂ) (sixVertexBetheM c z)
  by_cases h1 : z = 1
  · simp [sixVertexBetheL, sixVertexBetheM, h1]
  · simp only [sixVertexBetheM, map_sub, map_one, map_div₀, map_pow,
      Complex.conj_ofReal]
    rw [← Complex.inv_eq_conj hn]
    simp only [sixVertexBetheL]
    have hden : 1 - z⁻¹ = (z - 1) / z := by
      field_simp [hz]
    rw [hden, div_div_eq_mul_div]
    rw [show z - 1 = -(1 - z) by ring, div_neg]
    ring

theorem sixVertexBetheM_symmetric_pair (c p : ℝ) :
    sixVertexBetheM c (sixVertexBethePhase p) *
        sixVertexBetheM c (sixVertexBethePhase (-p)) =
      (Complex.normSq (sixVertexBetheM c (sixVertexBethePhase p)) : ℂ) := by
  rw [sixVertexBetheM_phase_neg]
  exact Complex.mul_conj _

theorem sixVertexBetheL_symmetric_pair (c p : ℝ) :
    sixVertexBetheL c (sixVertexBethePhase p) *
        sixVertexBetheL c (sixVertexBethePhase (-p)) =
      (Complex.normSq (sixVertexBetheM c (sixVertexBethePhase p)) : ℂ) := by
  rw [sixVertexBetheL_phase_eq_conj_M,
    sixVertexBetheL_phase_eq_conj_M, sixVertexBetheM_phase_neg]
  simp only [star_star]
  rw [mul_comm]
  exact Complex.mul_conj _



noncomputable def sixVertexSymmetricBetheEigenvalueCandidate
    {k : ℕ} (c : ℝ) (p : Fin k → ℝ) : ℂ :=
  (∏ j, sixVertexBetheL c (sixVertexBethePhase (p j)) *
      sixVertexBetheL c (sixVertexBethePhase (-p j))) +
    ∏ j, sixVertexBetheM c (sixVertexBethePhase (p j)) *
      sixVertexBetheM c (sixVertexBethePhase (-p j))


noncomputable def sixVertexSymmetricBetheEigenvalueValue
    {k : ℕ} (c : ℝ) (p : Fin k → ℝ) : ℝ :=
  2 * ∏ j, ‖sixVertexBetheM c (sixVertexBethePhase (p j))‖ ^ 2



theorem sixVertexSymmetricBetheEigenvalueCandidate_eq_value
    {k : ℕ} (c : ℝ) (p : Fin k → ℝ) :
    sixVertexSymmetricBetheEigenvalueCandidate c p =
      (sixVertexSymmetricBetheEigenvalueValue c p : ℂ) := by
  unfold sixVertexSymmetricBetheEigenvalueCandidate
  unfold sixVertexSymmetricBetheEigenvalueValue
  simp_rw [sixVertexBetheL_symmetric_pair,
    sixVertexBetheM_symmetric_pair, Complex.normSq_eq_norm_sq]
  push_cast
  ring



theorem sixVertexSymmetricBetheEigenvalueValue_log
    {k : ℕ} (c : ℝ) (p : Fin k → ℝ)
    (hM : ∀ j, sixVertexBetheM c (sixVertexBethePhase (p j)) ≠ 0) :
    Real.log (sixVertexSymmetricBetheEigenvalueValue c p) =
      Real.log 2 +
        2 * ∑ j, Real.log ‖sixVertexBetheM c
          (sixVertexBethePhase (p j))‖ := by
  have hnorm (j : Fin k) :
      ‖sixVertexBetheM c (sixVertexBethePhase (p j))‖ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hM j))
  have hprod :
      (∏ j, ‖sixVertexBetheM c (sixVertexBethePhase (p j))‖ ^ 2) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun j hj => hnorm j
  rw [sixVertexSymmetricBetheEigenvalueValue,
    Real.log_mul (by norm_num) hprod,
    Real.log_prod (fun j hj => hnorm j)]
  simp_rw [Real.log_pow]
  rw [← Finset.mul_sum]
  norm_num



theorem sixVertexBetheM_phase_ne_zero {c : ℝ} (hc : 2 < c) (p : ℝ) :
    sixVertexBetheM c (sixVertexBethePhase p) ≠ 0 := by
  let z := sixVertexBethePhase p
  have hn : ‖z‖ = 1 := sixVertexBethePhase_norm p
  by_cases h1 : z = 1
  · simp [sixVertexBetheM, z, h1]
  · have hden : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    intro hM
    change 1 - (c : ℂ) ^ 2 / (1 - z) = 0 at hM
    field_simp [hden] at hM
    have hM' : 1 - z - (c : ℂ) ^ 2 = 0 := by simpa using hM
    have heq : z = 1 - (c : ℂ) ^ 2 := by
      linear_combination -hM'
    have hre : z.re = 1 - c ^ 2 := by
      have h := congrArg Complex.re heq
      have hcRe : ((c : ℂ) ^ 2).re = c ^ 2 := by
        simp [pow_two]
      simpa only [Complex.sub_re, Complex.one_re, hcRe] using h
    have habs : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    rw [hn, hre] at habs
    have hc2 : 3 < c ^ 2 := by nlinarith
    rw [abs_of_neg (by nlinarith : 1 - c ^ 2 < 0)] at habs
    nlinarith



theorem sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt
    {k : ℕ} {c : ℝ} (hc : 2 < c) (p : Fin k → ℝ) :
    Real.log (sixVertexSymmetricBetheEigenvalueValue c p) =
      Real.log 2 +
        2 * ∑ j, Real.log ‖sixVertexBetheM c
          (sixVertexBethePhase (p j))‖ := by
  exact sixVertexSymmetricBetheEigenvalueValue_log c p
    (fun j => sixVertexBetheM_phase_ne_zero hc (p j))

theorem sixVertexSymmetricBetheEigenvalueValue_pos
    {k : ℕ} {c : ℝ} (hc : 2 < c) (p : Fin k → ℝ) :
    0 < sixVertexSymmetricBetheEigenvalueValue c p := by
  unfold sixVertexSymmetricBetheEigenvalueValue
  apply mul_pos (by norm_num)
  apply Finset.prod_pos
  intro j hj
  exact pow_pos (norm_pos_iff.mpr
    (sixVertexBetheM_phase_ne_zero hc (p j))) 2



theorem sixVertexSymmetricBetheEigenvalueCandidate_isPositiveReal
    {k : ℕ} {c : ℝ} (hc : 2 < c) (p : Fin k → ℝ) :
    (sixVertexSymmetricBetheEigenvalueCandidate c p).im = 0 ∧
      0 < (sixVertexSymmetricBetheEigenvalueCandidate c p).re := by
  rw [sixVertexSymmetricBetheEigenvalueCandidate_eq_value]
  simp [sixVertexSymmetricBetheEigenvalueValue_pos hc p]


theorem sixVertexBetheM_phase_normSq
    (c p : ℝ) (hp : sixVertexBethePhase p ≠ 1) :
    Complex.normSq (sixVertexBetheM c (sixVertexBethePhase p)) =
      ((c ^ 2 - 1) ^ 2 + 1 +
          2 * (c ^ 2 - 1) * Real.cos p) /
        (2 - 2 * Real.cos p) := by
  let z := sixVertexBethePhase p
  have hden : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  have hM : sixVertexBetheM c z =
      (1 - z - (c : ℂ) ^ 2) / (1 - z) := by
    unfold sixVertexBetheM
    field_simp [hden]
  rw [hM, Complex.normSq_div]
  rw [Complex.normSq_apply, Complex.normSq_apply]
  have hzre : z.re = Real.cos p := by
    simp [z, sixVertexBethePhase, Complex.exp_re]
  have hzim : z.im = Real.sin p := by
    simp [z, sixVertexBethePhase, Complex.exp_im]
  have hcRe : ((c : ℂ) ^ 2).re = c ^ 2 := by
    simp [pow_two]
  have hcIm : ((c : ℂ) ^ 2).im = 0 := by
    simp [pow_two]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  rw [hcRe, hcIm, hzre, hzim]
  ring_nf
  rw [Real.sin_sq]
  ring



theorem sixVertexBetheM_phase_log_norm
    (c p : ℝ) (hp : sixVertexBethePhase p ≠ 1) :
    Real.log ‖sixVertexBetheM c (sixVertexBethePhase p)‖ =
      (1 / 2 : ℝ) * Real.log
        (((c ^ 2 - 1) ^ 2 + 1 +
            2 * (c ^ 2 - 1) * Real.cos p) /
          (2 - 2 * Real.cos p)) := by
  let w := sixVertexBetheM c (sixVertexBethePhase p)
  calc
    Real.log ‖w‖ = (1 / 2 : ℝ) * (2 * Real.log ‖w‖) := by ring
    _ = (1 / 2 : ℝ) * Real.log (‖w‖ ^ 2) := by
      rw [Real.log_pow]
      norm_num
    _ = (1 / 2 : ℝ) * Real.log
        (((c ^ 2 - 1) ^ 2 + 1 +
            2 * (c ^ 2 - 1) * Real.cos p) /
          (2 - 2 * Real.cos p)) := by
      rw [← Complex.normSq_eq_norm_sq]
      exact congrArg (fun x : ℝ => (1 / 2 : ℝ) * Real.log x)
        (sixVertexBetheM_phase_normSq c p hp)


abbrev SixVertexSymmetricHalfFilledRoots :=
  (k : ℕ) → Fin (k + 1) → ℝ



noncomputable def sixVertexSymmetricBetheRootAverage
    (c : ℝ) (roots : SixVertexSymmetricHalfFilledRoots) (k : ℕ) : ℝ :=
  (2 * ∑ j, Real.log ‖sixVertexBetheM c
      (sixVertexBethePhase (roots k j))‖) /
    (sixVertexFourWidth 0 k : ℝ)



def SixVertexHasSymmetricBetheIdentification
    (c : ℝ) (roots : SixVertexSymmetricHalfFilledRoots) : Prop :=
  ∀ k, sixVertexLambdaAlongFour c 0 k =
    sixVertexSymmetricBetheEigenvalueValue c (roots k)



theorem sixVertexCentralWidthRate_eq_symmetricBetheRootAverage
    {c : ℝ} (hc : 2 < c) (roots : SixVertexSymmetricHalfFilledRoots)
    (hroots : SixVertexHasSymmetricBetheIdentification c roots) (k : ℕ) :
    sixVertexCentralWidthRate c k =
      Real.log 2 / (sixVertexFourWidth 0 k : ℝ) +
        sixVertexSymmetricBetheRootAverage c roots k := by
  rw [sixVertexCentralWidthRate, hroots k,
    sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt hc]
  unfold sixVertexSymmetricBetheRootAverage
  ring

private theorem sixVertex_log_two_div_fourWidth_tendsto_zero :
    Tendsto (fun k : ℕ =>
      Real.log 2 / (sixVertexFourWidth 0 k : ℝ)) atTop (nhds 0) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2 / 4)).comp
    (tendsto_add_atTop_nat 1)
  convert h using 1
  funext k
  simp [sixVertexFourWidth]
  field_simp




theorem sixVertexCentralWidthRate_tendsto_iff_symmetricBetheRootAverage
    {c a : ℝ} (hc : 2 < c) (roots : SixVertexSymmetricHalfFilledRoots)
    (hroots : SixVertexHasSymmetricBetheIdentification c roots) :
    Tendsto (sixVertexCentralWidthRate c) atTop (nhds a) ↔
      Tendsto (sixVertexSymmetricBetheRootAverage c roots) atTop (nhds a) := by
  have heq : sixVertexCentralWidthRate c = fun k =>
      Real.log 2 / (sixVertexFourWidth 0 k : ℝ) +
        sixVertexSymmetricBetheRootAverage c roots k := by
    funext k
    exact sixVertexCentralWidthRate_eq_symmetricBetheRootAverage
      hc roots hroots k
  rw [heq]
  constructor
  · intro h
    have hsub := h.sub sixVertex_log_two_div_fourWidth_tendsto_zero
    simpa using hsub
  · intro h
    simpa using sixVertex_log_two_div_fourWidth_tendsto_zero.add h




theorem sixVertexSector_eigenvalue_eq_top_of_positive_eigenvector
    {N n : ℕ} (hn : n ≤ N) {c μ : ℝ} (hc : 0 < c)
    (v : SixVertexSector N n → ℝ) (hv : ∀ i, 0 < v i)
    (heig : sixVertexSectorTransfer N n c *ᵥ v = μ • v) :
    μ = sixVertexSectorTopEigenvalue N n hn c := by
  classical
  letI : Nonempty (SixVertexSector N n) := sixVertexSector_nonempty hn
  obtain ⟨u, hupos, hueig⟩ :=
    sixVertexSectorTop_exists_positive_eigenvector hn hc
  let A := sixVertexSectorTransfer N n c
  let top := sixVertexSectorTopEigenvalue N n hn c
  let S := ∑ i, u i * v i
  have hS : 0 < S := by
    apply Finset.sum_pos
    · intro i hi
      exact mul_pos (hupos i) (hv i)
    · exact Finset.univ_nonempty
  have hadj : ∑ i, u i * (A *ᵥ v) i =
      ∑ i, (A *ᵥ (fun i => u i)) i * v i := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [show A j i = A i j by
      exact sixVertexTransfer_symmetric N c _ _]
    ring
  have hleft : ∑ i, u i * (A *ᵥ v) i = μ * S := by
    rw [show A *ᵥ v = μ • v from heig]
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (∑ i, u i * (μ * v i)) = ∑ i, μ * (u i * v i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = μ * ∑ i, u i * v i := by rw [Finset.mul_sum]
      _ = μ * S := rfl
  have hright : ∑ i, (A *ᵥ (fun i => u i)) i * v i = top * S := by
    rw [show A *ᵥ (fun i => u i) = top • (fun i => u i) from hueig]
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (∑ i, top * u i * v i) = ∑ i, top * (u i * v i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = top * ∑ i, u i * v i := by rw [Finset.mul_sum]
      _ = top * S := rfl
  rw [hleft, hright] at hadj
  nlinarith

end StatMech.FrontierD
