/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOddAnalyticStabilitySheet
import Code.FrontierD.SixVertexBetheZeroPhaseSingle





open Finset Filter Topology Matrix

namespace StatMech.FrontierD

noncomputable section

theorem sixVertexZeroPhaseBetheEigenvalueCandidate_oddSymmetric_eq_value
    {c : Real} (hc : 2 < c) {N m : Nat} (q : Fin m → Real)
    (hopen : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q)) :
    sixVertexZeroPhaseBetheEigenvalueCandidate c N
        (sixVertexOddSymmetricLift m q) (sixVertexOddCentralIndex m) =
      (sixVertexZeroPhaseBetheEigenvalueValue c N
        (sixVertexOddSymmetricLift m q) (sixVertexOddCentralIndex m) : Complex) := by
  let p := sixVertexOddSymmetricLift m q
  let ell := sixVertexOddCentralIndex m
  have hell : p ell = 0 := sixVertexOddSymmetricLift_central m q
  have hunique : ∀ j, p j = 0 → j = ell := by
    intro j hj
    exact hopen.1.injective (hj.trans hell.symm)
  have hprod := sixVertexZeroPhaseMProduct_eq_normProduct_of_symmetric
    hc p ell (sixVertexOddSymmetricLift_symmetric m q)
      (sixVertexOddCentralIndex_rev m) hunique
  unfold sixVertexZeroPhaseBetheEigenvalueCandidate
    sixVertexZeroPhaseBetheEigenvalueValue
  change (sixVertexZeroPhaseBethePrefactor c N p ell : Complex) * _ = _
  rw [hprod, Complex.ofReal_mul]

theorem analyticOnNhd_sixVertexOddZeroPhaseBetheEigenvalueValue
    {N m : Nat} {U : Set Real} (hUopen : IsOpen U)
    (hUtwo : U ⊆ Set.Ioi 2)
    (roots : C(Real, Fin ((m + 1) + m) → Real))
    (hrootAnalytic : AnalyticOnNhd Real roots U)
    (hopen : ∀ t ∈ U, SixVertexOpenRootSimplex (roots t)) :
    AnalyticOnNhd Real
      (fun t => sixVertexZeroPhaseBetheEigenvalueValue t N (roots t)
        (sixVertexOddCentralIndex m)) U := by
  intro c hcU
  let ell := sixVertexOddCentralIndex m
  have hc : 2 < c := hUtwo hcU
  have hcoord (j : Fin ((m + 1) + m)) :
      AnalyticAt Real (fun t => roots t j) c := by
    simpa only [Function.comp_apply] using
      ((ContinuousLinearMap.proj (R := Real) j).analyticAt (roots c)).comp
        (hrootAnalytic c hcU)
  have htheta (j : Fin ((m + 1) + m)) :
      AnalyticAt Real
        (fun t => sixVertexThetaLeftDerivAtZero t (roots t j)) c := by
    unfold sixVertexThetaLeftDerivAtZero sixVertexDelta
      sixVertexBetheIntegratingFactor sixVertexThetaDerivativeDenominator
      sixVertexThetaDenominator
    simp only [sixVertexDelta]
    apply AnalyticAt.div
    · fun_prop
    · fun_prop
    · exact ne_of_gt (sixVertexThetaDerivativeDenominator_pos hc 0 (roots c j))
  have hpref : AnalyticAt Real
      (fun t => sixVertexZeroPhaseBethePrefactor t N (roots t) ell) c := by
    unfold sixVertexZeroPhaseBethePrefactor
    apply AnalyticAt.add
    · apply AnalyticAt.add <;> fun_prop
    · apply AnalyticAt.mul
      · fun_prop
      · exact Finset.analyticAt_fun_sum _ (fun j _ => htheta j)
  have hother (j : Fin ((m + 1) + m)) (hj : j ≠ ell) :
      sixVertexBethePhase (roots c j) ≠ 1 := by
    apply sixVertexBethePhase_ne_one_of_mem_Ioo ((hopen c hcU).2.2 j)
    intro hjzero
    apply hj
    exact (hopen c hcU).1.injective
      (hjzero.trans (by
        have hs := (hopen c hcU).2.1 ell
        rw [sixVertexOddCentralIndex_rev] at hs
        linarith))
  have hM (j : Fin ((m + 1) + m)) (hj : j ≠ ell) :
      AnalyticAt Real
        (fun t => sixVertexBetheM t (sixVertexBethePhase (roots t j))) c := by
    have hcast : AnalyticAt Real (fun t : Real => (t : Complex)) c := by
      simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.analyticAt c
    have hphase : AnalyticAt Real
        (fun t => sixVertexBethePhase (roots t j)) c := by
      unfold sixVertexBethePhase
      have hrootCast : AnalyticAt Real
          (fun t => (roots t j : Complex)) c := by
        simpa only [Complex.ofRealCLM_apply, Function.comp_apply] using
          (Complex.ofRealCLM.analyticAt (roots c j)).comp (x := c) (hcoord j)
      exact analyticAt_cexp.restrictScalars.comp
        (analyticAt_const.mul hrootCast)
    unfold sixVertexBetheM
    apply AnalyticAt.sub
    · exact analyticAt_const
    · apply AnalyticAt.div
      · exact hcast.pow 2
      · exact analyticAt_const.sub hphase
      · exact sub_ne_zero.mpr (Ne.symm (hother j hj))
  have hcand : AnalyticAt Real
      (fun t => sixVertexZeroPhaseBetheEigenvalueCandidate t N (roots t) ell) c := by
    unfold sixVertexZeroPhaseBetheEigenvalueCandidate
    apply AnalyticAt.mul
    · simpa only [Complex.ofRealCLM_apply, Function.comp_apply] using
        (Complex.ofRealCLM.analyticAt _).comp hpref
    · exact Finset.analyticAt_fun_prod _ (fun j hj =>
        hM j (Finset.ne_of_mem_erase hj))
  have hre : AnalyticAt Real
      (fun t =>
        (sixVertexZeroPhaseBetheEigenvalueCandidate t N (roots t) ell).re) c := by
    exact (Complex.reCLM.analyticAt _).comp hcand
  apply hre.congr
  filter_upwards [hUopen.mem_nhds hcU] with t ht
  have hlift : sixVertexOddSymmetricLift m
      (sixVertexOddPositiveHalfProjection m (roots t)) = roots t :=
    sixVertexOddSymmetricLift_projection m (hopen t ht).2.1
  have heq := sixVertexZeroPhaseBetheEigenvalueCandidate_oddSymmetric_eq_value
    (N := N) (hUtwo ht)
      (sixVertexOddPositiveHalfProjection m (roots t))
      (by rw [hlift]; exact hopen t ht)
  rw [hlift] at heq
  simpa using congrArg Complex.re heq



theorem sixVertexZeroPhase_characteristicDet_eq_zero_of_nonzero
    {N n : Nat} {c mu : Real} {p : Fin n → Real} {ell : Fin n}
    (heigen : SixVertexCoordinateBetheZeroPhaseEigenrelation (N := N) c p ell)
    (hcandidate : sixVertexZeroPhaseBetheEigenvalueCandidate c N p ell =
      (mu : Complex))
    (hwave : sixVertexCoordinateBetheWave (N := N) c p ≠ 0) :
    Matrix.det
      (mu • (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) -
        sixVertexSectorTransfer N n c) = 0 := by
  let w := sixVertexCoordinateBetheWave (N := N) c p
  obtain ⟨x, hx⟩ : ∃ x, w x ≠ 0 := by
    by_contra h
    push Not at h
    exact hwave (funext h)
  have hcomponent : (w x).re ≠ 0 ∨ (w x).im ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (Complex.ext h.1 h.2)
  rcases hcomponent with hre | him
  · let v : SixVertexSector N n → Real := fun y => (w y).re
    have hvEigen : sixVertexSectorTransfer N n c *ᵥ v = mu • v := by
      funext y
      have hy := congrFun heigen y
      have hyre := congrArg Complex.re hy
      simp only [sixVertexSectorTransferComplex_mulVec_apply, hcandidate,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, Pi.smul_apply, smul_eq_mul] at hyre
      simpa [v, w, Matrix.mulVec, dotProduct, smul_eq_mul] using hyre
    apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
      (v := v) (i := x)
    · simp [Matrix.sub_mulVec, Matrix.smul_mulVec, hvEigen]
    · exact mem_nonZeroDivisors_iff_ne_zero.mpr hre
  · let v : SixVertexSector N n → Real := fun y => (w y).im
    have hvEigen : sixVertexSectorTransfer N n c *ᵥ v = mu • v := by
      funext y
      have hy := congrFun heigen y
      have hyim := congrArg Complex.im hy
      simp only [sixVertexSectorTransferComplex_mulVec_apply, hcandidate,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        add_zero, Pi.smul_apply, smul_eq_mul] at hyim
      simpa [v, w, Matrix.mulVec, dotProduct, smul_eq_mul] using hyim
    apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
      (v := v) (i := x)
    · simp [Matrix.sub_mulVec, Matrix.smul_mulVec, hvEigen]
    · exact mem_nonZeroDivisors_iff_ne_zero.mpr him

theorem sixVertexAnalyticOddSymmetricBetheCandidate_eqOn_top
    {N m : Nat} (hm : 0 < m) (hn : (m + 1) + m ≤ N)
    {U : Set Real} (hU : IsPreconnected U) (hUopen : IsOpen U)
    (hUtwo : U ⊆ Set.Ioi 2)
    (roots : C(Real, Fin ((m + 1) + m) → Real))
    (hopen : ∀ t ∈ U, SixVertexOpenRootSimplex (roots t))
    (hsol : ∀ t ∈ U,
      SixVertexSatisfiesBetheEquations t N ((m + 1) + m) (roots t))
    (hrootAnalytic : AnalyticOnNhd Real roots U)
    {c₀ : Real} (hc₀U : c₀ ∈ U)
    (hwave : sixVertexCoordinateBetheWave (N := N) c₀ (roots c₀) ≠ 0)
    (hbase : sixVertexZeroPhaseBetheEigenvalueValue c₀ N (roots c₀)
        (sixVertexOddCentralIndex m) =
      sixVertexSectorTopEigenvalue N ((m + 1) + m) hn c₀) :
    Set.EqOn
      (fun t => sixVertexZeroPhaseBetheEigenvalueValue t N (roots t)
        (sixVertexOddCentralIndex m))
      (sixVertexSectorTopEigenvalue N ((m + 1) + m) hn) U := by
  let ell := sixVertexOddCentralIndex m
  let f : Real → Real := fun t =>
    sixVertexZeroPhaseBetheEigenvalueValue t N (roots t) ell
  have hfAnalytic : AnalyticOnNhd Real f U :=
    analyticOnNhd_sixVertexOddZeroPhaseBetheEigenvalueValue
      hUopen hUtwo roots hrootAnalytic hopen
  have heigen : ∀ t ∈ U,
      SixVertexCoordinateBetheZeroPhaseEigenrelation (N := N) t
        (roots t) ell := by
    intro t ht
    have hell : roots t ell = 0 := by
      have hs := (hopen t ht).2.1 ell
      rw [sixVertexOddCentralIndex_rev] at hs
      linarith
    apply (hsol t ht).multiplicative
      |>.physicalZeroPhaseEigenrelation_of_two_le
        (hUtwo ht) (by omega) (roots t) ell hell (hopen t ht).2.2
    intro j hj
    apply sixVertexBethePhase_ne_one_of_mem_Ioo ((hopen t ht).2.2 j)
    intro hjzero
    exact hj ((hopen t ht).1.injective (hjzero.trans hell.symm))
  have hcandidate : ∀ t ∈ U,
      sixVertexZeroPhaseBetheEigenvalueCandidate t N (roots t) ell =
        (f t : Complex) := by
    intro t ht
    have hlift : sixVertexOddSymmetricLift m
        (sixVertexOddPositiveHalfProjection m (roots t)) = roots t :=
      sixVertexOddSymmetricLift_projection m (hopen t ht).2.1
    change sixVertexZeroPhaseBetheEigenvalueCandidate t N (roots t)
        (sixVertexOddCentralIndex m) =
      (sixVertexZeroPhaseBetheEigenvalueValue t N (roots t)
        (sixVertexOddCentralIndex m) : Complex)
    rw [← hlift]
    exact sixVertexZeroPhaseBetheEigenvalueCandidate_oddSymmetric_eq_value
      (N := N) (hUtwo ht) _ (by rw [hlift]; exact hopen t ht)
  have hwaveContinuous : ContinuousAt
      (fun t => sixVertexCoordinateBetheWave (N := N) t (roots t)) c₀ :=
    (continuous_sixVertexCoordinateBetheWave_branch roots roots.continuous).continuousAt
  let D : Real → Real := fun t => Matrix.det
    (f t • (1 : Matrix (SixVertexSector N ((m + 1) + m))
      (SixVertexSector N ((m + 1) + m)) Real) -
      sixVertexSectorTransfer N ((m + 1) + m) t)
  have hDanalytic : AnalyticOnNhd Real D U := by
    intro t ht
    have hgraph : AnalyticAt Real (fun s => (s, f s)) t :=
      analyticAt_id.prod (hfAnalytic t ht)
    simpa only [D] using
      (analyticAt_sixVertexSectorCharacteristicDet N ((m + 1) + m)
        (t, f t)).comp (f := fun s => (s, f s)) (x := t) hgraph
  have hwaveEventually : ∀ᶠ t in nhds c₀,
      sixVertexCoordinateBetheWave (N := N) t (roots t) ≠ 0 :=
    hwaveContinuous.tendsto.eventually_ne hwave
  have hUEventually : ∀ᶠ t in nhds c₀, t ∈ U :=
    hUopen.mem_nhds hc₀U
  have hDzeroEventually : D =ᶠ[nhds c₀] 0 := by
    filter_upwards [hwaveEventually, hUEventually] with t hwt ht
    exact sixVertexZeroPhase_characteristicDet_eq_zero_of_nonzero
      (heigen t ht) (hcandidate t ht) hwt
  have hDzero : Set.EqOn D 0 U :=
    hDanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hU hc₀U hDzeroEventually
  have hUzero : U ⊆ Set.Ioi 0 := by
    intro t ht
    change 0 < t
    exact lt_trans (by norm_num : (0 : Real) < 2)
      (show 2 < t from hUtwo ht)
  have hc₀pos : 0 < c₀ := hUzero hc₀U
  apply sixVertexSectorTopEigenvalue_eqOn_of_analytic_characteristicRoot
    hn hU hUopen hUzero hc₀U hc₀pos hfAnalytic
  · exact fun t ht => hDzero ht
  · exact hbase

end

end StatMech.FrontierD
