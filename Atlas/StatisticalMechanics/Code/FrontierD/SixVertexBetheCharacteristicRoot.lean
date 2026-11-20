/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexPerronRootSheet
import Code.FrontierD.SixVertexBetheSelectedPerron










open Finset Matrix

namespace StatMech.FrontierD

noncomputable section



theorem sixVertexCoordinateBethe_characteristicDet_eq_zero_of_nonzero
    {N n : Nat} {c mu : Real} {p : Fin n → Real}
    (heigen : SixVertexCoordinateBetheEigenrelation (N := N) c p)
    (hcandidate : sixVertexBetheEigenvalueCandidate c p = (mu : Complex))
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



theorem sixVertexBetheCandidate_eqOn_top_of_analyticSheet
    {N n : Nat} (hn : n ≤ N) {U : Set Real}
    (hU : IsPreconnected U) (hUopen : IsOpen U)
    (hUpos : U ⊆ Set.Ioi 0) {c : Real} (hcU : c ∈ U) (hc : 0 < c)
    (p : Real → Fin n → Real) (f : Real → Real)
    (hanalytic : AnalyticOnNhd Real f U)
    (heigen : ∀ t ∈ U,
      SixVertexCoordinateBetheEigenrelation (N := N) t (p t))
    (hcandidate : ∀ t ∈ U,
      sixVertexBetheEigenvalueCandidate t (p t) = (f t : Complex))
    (hwave : ∀ t ∈ U,
      sixVertexCoordinateBetheWave (N := N) t (p t) ≠ 0)
    (hbase : f c = sixVertexSectorTopEigenvalue N n hn c) :
    Set.EqOn f (sixVertexSectorTopEigenvalue N n hn) U := by
  apply sixVertexSectorTopEigenvalue_eqOn_of_analytic_characteristicRoot
    hn hU hUopen hUpos hcU hc hanalytic
  · intro t ht
    exact sixVertexCoordinateBethe_characteristicDet_eq_zero_of_nonzero
      (heigen t ht) (hcandidate t ht) (hwave t ht)
  · exact hbase




theorem sixVertexBetheCandidate_eqOn_top_of_analyticSheet_of_nonzero_at
    {N n : Nat} (hn : n ≤ N) {U : Set Real}
    (hU : IsPreconnected U) (hUopen : IsOpen U)
    (hUpos : U ⊆ Set.Ioi 0) {c : Real} (hcU : c ∈ U) (hc : 0 < c)
    (p : Real → Fin n → Real) (f : Real → Real)
    (hanalytic : AnalyticOnNhd Real f U)
    (heigen : ∀ t ∈ U,
      SixVertexCoordinateBetheEigenrelation (N := N) t (p t))
    (hcandidate : ∀ t ∈ U,
      sixVertexBetheEigenvalueCandidate t (p t) = (f t : Complex))
    (hwaveContinuous : ContinuousAt
      (fun t => sixVertexCoordinateBetheWave (N := N) t (p t)) c)
    (hwave : sixVertexCoordinateBetheWave (N := N) c (p c) ≠ 0)
    (hbase : f c = sixVertexSectorTopEigenvalue N n hn c) :
    Set.EqOn f (sixVertexSectorTopEigenvalue N n hn) U := by
  let D : Real → Real := fun t => Matrix.det
    (f t • (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) -
      sixVertexSectorTransfer N n t)
  have hDanalytic : AnalyticOnNhd Real D U := by
    intro t ht
    have hgraph : AnalyticAt Real (fun s => (s, f s)) t :=
      analyticAt_id.prod (hanalytic t ht)
    simpa only [D] using
      (analyticAt_sixVertexSectorCharacteristicDet N n (t, f t)).comp
        (f := fun s => (s, f s)) (x := t) hgraph
  have hwaveEventually : ∀ᶠ t in nhds c,
      sixVertexCoordinateBetheWave (N := N) t (p t) ≠ 0 :=
    hwaveContinuous.tendsto.eventually_ne hwave
  have hUEventually : ∀ᶠ t in nhds c, t ∈ U := hUopen.mem_nhds hcU
  have hDzeroEventually : D =ᶠ[nhds c] 0 := by
    filter_upwards [hwaveEventually, hUEventually] with t hwt ht
    exact sixVertexCoordinateBethe_characteristicDet_eq_zero_of_nonzero
      (heigen t ht) (hcandidate t ht) hwt
  have hDzero : Set.EqOn D 0 U :=
    hDanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hU hcU hDzeroEventually
  apply sixVertexSectorTopEigenvalue_eqOn_of_analytic_characteristicRoot
    hn hU hUopen hUpos hcU hc hanalytic
  · intro t ht
    exact hDzero ht
  · exact hbase



theorem sixVertexSymmetricBethe_characteristicDet_eq_zero_of_nonzero
    {N k : Nat} {c : Real} {p : Fin k → Real}
    (heigen : SixVertexCoordinateBetheEigenrelation (N := N) c
      (sixVertexPairedRootFamily p))
    (hwave : sixVertexCoordinateBetheWave (N := N) c
      (sixVertexPairedRootFamily p) ≠ 0) :
    Matrix.det
      (sixVertexSymmetricBetheEigenvalueValue c p •
          (1 : Matrix (SixVertexSector N (k + k))
            (SixVertexSector N (k + k)) Real) -
        sixVertexSectorTransfer N (k + k) c) = 0 := by
  apply sixVertexCoordinateBethe_characteristicDet_eq_zero_of_nonzero
    heigen ?_ hwave
  rw [sixVertexBetheEigenvalueCandidate_paired,
    sixVertexSymmetricBetheEigenvalueCandidate_eq_value]




theorem sixVertexSymmetricBetheCandidate_eqOn_top_of_analyticSheet
    {N k : Nat} (hn : k + k ≤ N) {U : Set Real}
    (hU : IsPreconnected U) (hUopen : IsOpen U)
    (hUpos : U ⊆ Set.Ioi 0) {c : Real} (hcU : c ∈ U) (hc : 0 < c)
    (p : Real → Fin k → Real)
    (hanalytic : AnalyticOnNhd Real
      (fun t => sixVertexSymmetricBetheEigenvalueValue t (p t)) U)
    (heigen : ∀ t ∈ U, SixVertexCoordinateBetheEigenrelation (N := N) t
      (sixVertexPairedRootFamily (p t)))
    (hwave : ∀ t ∈ U, sixVertexCoordinateBetheWave (N := N) t
      (sixVertexPairedRootFamily (p t)) ≠ 0)
    (hbase : sixVertexSymmetricBetheEigenvalueValue c (p c) =
      sixVertexSectorTopEigenvalue N (k + k) hn c) :
    Set.EqOn (fun t => sixVertexSymmetricBetheEigenvalueValue t (p t))
      (sixVertexSectorTopEigenvalue N (k + k) hn) U := by
  apply sixVertexSectorTopEigenvalue_eqOn_of_analytic_characteristicRoot
    hn hU hUopen hUpos hcU hc hanalytic
  · intro t ht
    exact sixVertexSymmetricBethe_characteristicDet_eq_zero_of_nonzero
      (heigen t ht) (hwave t ht)
  · exact hbase

end

end StatMech.FrontierD
