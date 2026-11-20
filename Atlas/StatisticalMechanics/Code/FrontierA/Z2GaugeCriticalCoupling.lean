/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.Z2GaugeDualCoupling
import Mathlib.Analysis.SpecialFunctions.Artanh

open Set

namespace StatMech.FrontierA


noncomputable def gaugeCriticalCoupling (betaIsing : Real) : Real :=
  Real.artanh (Real.exp (-2 * betaIsing))

private theorem exp_neg_two_mem_Ioo_zero_one
    {beta : Real} (hbeta : 0 < beta) :
    Real.exp (-2 * beta) ∈ Ioo (0 : Real) 1 := by
  constructor
  · exact Real.exp_pos _
  · rw [← Real.exp_zero, Real.exp_lt_exp]
    linarith

theorem gaugeCriticalCoupling_pos
    {betaIsing : Real} (hbeta : 0 < betaIsing) :
    0 < gaugeCriticalCoupling betaIsing := by
  exact Real.artanh_pos (exp_neg_two_mem_Ioo_zero_one hbeta)



theorem gaugeDualCoupling_gaugeCriticalCoupling
    {betaIsing : Real} (hbeta : 0 < betaIsing) :
    gaugeDualCoupling (gaugeCriticalCoupling betaIsing) = betaIsing := by
  have hq := exp_neg_two_mem_Ioo_zero_one hbeta
  unfold gaugeDualCoupling gaugeCriticalCoupling
  rw [Real.tanh_artanh (show Real.exp (-2 * betaIsing) ∈ Ioo (-1 : Real) 1 by
    exact ⟨by linarith [hq.1], hq.2⟩), Real.log_exp]
  ring



theorem coth_gaugeCriticalCoupling
    {betaIsing : Real} (hbeta : 0 < betaIsing) :
    Real.cosh (gaugeCriticalCoupling betaIsing) /
        Real.sinh (gaugeCriticalCoupling betaIsing) =
      Real.exp (2 * betaIsing) := by
  have h := exp_two_mul_gaugeDualCoupling
    (gaugeCriticalCoupling_pos hbeta)
  rw [gaugeDualCoupling_gaugeCriticalCoupling hbeta] at h
  exact h.symm




theorem gaugeDualCoupling_lt_iff_gaugeCriticalCoupling_lt
    {K betaIsing : Real} (hK : 0 < K) (hbeta : 0 < betaIsing) :
    gaugeDualCoupling K < betaIsing ↔
      gaugeCriticalCoupling betaIsing < K := by
  let q := Real.exp (-2 * betaIsing)
  have hq : q ∈ Ioo (0 : Real) 1 := exp_neg_two_mem_Ioo_zero_one hbeta
  have htanh : Real.tanh K ∈ Ioo (-1 : Real) 1 :=
    ⟨Real.neg_one_lt_tanh K, Real.tanh_lt_one K⟩
  have horder : gaugeCriticalCoupling betaIsing < K ↔ q < Real.tanh K := by
    constructor
    · intro h
      have h' : Real.artanh q < Real.artanh (Real.tanh K) := by
        simpa [gaugeCriticalCoupling, q, Real.artanh_tanh] using h
      exact (Real.artanh_lt_artanh_iff
        (by exact ⟨by linarith [hq.1], hq.2⟩) htanh).mp h'
    · intro h
      have h' : Real.artanh q < Real.artanh (Real.tanh K) :=
        (Real.artanh_lt_artanh_iff
          (by exact ⟨by linarith [hq.1], hq.2⟩) htanh).mpr h
      simpa [gaugeCriticalCoupling, q, Real.artanh_tanh] using h'
  have hbetaLog : betaIsing = -Real.log q / 2 := by
    dsimp [q]
    rw [Real.log_exp]
    ring
  rw [horder, hbetaLog]
  unfold gaugeDualCoupling
  constructor
  · intro h
    have hlog : Real.log q < Real.log (Real.tanh K) := by linarith
    exact (Real.strictMonoOn_log.lt_iff_lt hq.1
      (tanh_pos_of_pos hK)).mp hlog
  · intro h
    have hlog : Real.log q < Real.log (Real.tanh K) :=
      (Real.strictMonoOn_log.lt_iff_lt hq.1
        (tanh_pos_of_pos hK)).mpr h
    linarith


theorem lt_gaugeDualCoupling_iff_lt_gaugeCriticalCoupling
    {K betaIsing : Real} (hK : 0 < K) (hbeta : 0 < betaIsing) :
    betaIsing < gaugeDualCoupling K ↔
      K < gaugeCriticalCoupling betaIsing := by
  let q := Real.exp (-2 * betaIsing)
  have hq : q ∈ Ioo (0 : Real) 1 := exp_neg_two_mem_Ioo_zero_one hbeta
  have htanh : Real.tanh K ∈ Ioo (-1 : Real) 1 :=
    ⟨Real.neg_one_lt_tanh K, Real.tanh_lt_one K⟩
  have horder : K < gaugeCriticalCoupling betaIsing ↔ Real.tanh K < q := by
    constructor
    · intro h
      have h' : Real.artanh (Real.tanh K) < Real.artanh q := by
        simpa [gaugeCriticalCoupling, q, Real.artanh_tanh] using h
      exact (Real.artanh_lt_artanh_iff htanh
        (by exact ⟨by linarith [hq.1], hq.2⟩)).mp h'
    · intro h
      have h' : Real.artanh (Real.tanh K) < Real.artanh q :=
        (Real.artanh_lt_artanh_iff htanh
          (by exact ⟨by linarith [hq.1], hq.2⟩)).mpr h
      simpa [gaugeCriticalCoupling, q, Real.artanh_tanh] using h'
  have hbetaLog : betaIsing = -Real.log q / 2 := by
    dsimp [q]
    rw [Real.log_exp]
    ring
  rw [horder, hbetaLog]
  unfold gaugeDualCoupling
  constructor
  · intro h
    have hlog : Real.log (Real.tanh K) < Real.log q := by linarith
    exact (Real.strictMonoOn_log.lt_iff_lt
      (tanh_pos_of_pos hK) hq.1).mp hlog
  · intro h
    have hlog : Real.log (Real.tanh K) < Real.log q :=
      (Real.strictMonoOn_log.lt_iff_lt
        (tanh_pos_of_pos hK) hq.1).mpr h
    linarith

end StatMech.FrontierA
