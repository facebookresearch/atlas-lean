/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexPerronAnalytic
import Mathlib.Analysis.Analytic.Uniqueness










open Filter Topology

namespace StatMech.FrontierD

noncomputable section



theorem eventuallyEq_sixVertexSectorTopEigenvalue_of_characteristicRoot
    {N n : Nat} (hn : n ≤ N) {c : Real} (hc : 0 < c)
    {f : Real → Real} (hf : ContinuousAt f c)
    (hfc : f c = sixVertexSectorTopEigenvalue N n hn c)
    (hroot : ∀ᶠ t : Real in nhds c,
      Matrix.det
        (f t •
            (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) -
          sixVertexSectorTransfer N n t) = 0) :
    f =ᶠ[nhds c] sixVertexSectorTopEigenvalue N n hn := by
  let top : Real → Real := sixVertexSectorTopEigenvalue N n hn
  let detAt : Real × Real → Real := fun q =>
    Matrix.det
      (q.2 •
          (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) -
        sixVertexSectorTransfer N n q.1)
  let H : Real × Real → Real × Real := fun q => (q.1, detAt q)
  let q₀ : Real × Real := (c, top c)
  let L := fderiv Real H q₀
  have hH : AnalyticAt Real H q₀ := by
    apply analyticAt_fst.prod
    dsimp only [detAt, H]
    exact analyticAt_sixVertexSectorCharacteristicDet N n q₀
  have htopDerivative :
      (sixVertexSectorTransfer N n c).charpoly.derivative.eval (top c) ≠ 0 :=
    sixVertexSectorTop_charpoly_derivative_ne_zero hn hc
  have hLinj : Function.Injective L := by
    let b := (sixVertexSectorTransfer N n c).charpoly.derivative.eval (top c)
    have hb : b ≠ 0 := htopDerivative
    have hfirstDeriv : HasFDerivAt (fun q => (H q).1)
        ((ContinuousLinearMap.fst Real Real Real).comp L) q₀ :=
      hH.hasStrictFDerivAt.hasFDerivAt.fst
    have hfirst : (ContinuousLinearMap.fst Real Real Real).comp L =
        ContinuousLinearMap.fst Real Real Real := by
      apply HasFDerivAt.unique hfirstDeriv
      simpa only [H] using (hasFDerivAt_fst (p := q₀))
    have hdetEq (t : Real) : detAt (c, t) =
        (sixVertexSectorTransfer N n c).charpoly.eval t := by
      rw [Matrix.eval_charpoly]
      dsimp only [detAt]
      congr 1
      ext i j
      simp [Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    have hcurve : HasDerivAt (fun t : Real => H (c, t)) (0, b) (top c) := by
      apply (hasDerivAt_const (top c) c).prodMk
      convert (sixVertexSectorTransfer N n c).charpoly.hasDerivAt (top c) using 1
      funext t
      exact hdetEq t
    have hline : HasDerivAt (fun t : Real => (c, t)) (0, 1) (top c) :=
      (hasDerivAt_const (top c) c).prodMk (hasDerivAt_id (top c))
    have hcurve' := hH.hasStrictFDerivAt.hasFDerivAt.comp (top c) hline
    have hvertical : L (0, 1) = (0, b) := by
      have heq := hcurve'.unique hcurve.hasFDerivAt
      have happ := congrArg (fun K : Real →L[Real] Real × Real => K 1) heq
      simpa [L, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply] using happ
    intro v w hvw
    apply sub_eq_zero.mp
    let z := v - w
    have hz : L z = 0 := by simp [z, hvw]
    have hLzfirst : (L z).1 = z.1 := by
      have happ := congrArg (fun K : (Real × Real) →L[Real] Real => K z) hfirst
      exact happ
    have hzfirst : z.1 = 0 := by rw [← hLzfirst, hz]; rfl
    have hzdecomp : z = z.2 • ((0, 1) : Real × Real) := by
      ext <;> simp [hzfirst]
    have hzsecond : z.2 * b = 0 := by
      have hzsnd := congrArg Prod.snd hz
      rw [hzdecomp, map_smul, hvertical] at hzsnd
      simpa [mul_comm] using hzsnd
    have hzsecondZero : z.2 = 0 :=
      (mul_eq_zero.mp hzsecond).resolve_right hb
    exact Prod.ext hzfirst hzsecondZero
  have hker : L.ker = ⊥ := LinearMap.ker_eq_bot.mpr hLinj
  have hrange : L.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    exact LinearMap.injective_iff_surjective.mp hLinj
  let e : (Real × Real) ≃L[Real] (Real × Real) :=
    ContinuousLinearEquiv.ofBijective L hker hrange
  have hHe : HasStrictFDerivAt H
      (e : (Real × Real) →L[Real] (Real × Real)) q₀ := by
    simpa [L, e, ContinuousLinearEquiv.coe_ofBijective] using
      hH.hasStrictFDerivAt
  let R : OpenPartialHomeomorph (Real × Real) (Real × Real) :=
    hHe.toOpenPartialHomeomorph H
  have hqsource : q₀ ∈ R.source := hHe.mem_toOpenPartialHomeomorph_source
  have htopContinuous : ContinuousAt top c :=
    (continuous_sixVertexSectorTopEigenvalue hn).continuousAt
  have hfgraph : Tendsto (fun t => (t, f t)) (nhds c) (nhds q₀) := by
    have h := continuousAt_id.prodMk hf
    change Tendsto (fun t => (t, f t)) (nhds c) (nhds (c, top c))
    have hfc' : f c = top c := hfc
    rwa [← hfc']
  have htopgraph : Tendsto (fun t => (t, top t)) (nhds c) (nhds q₀) :=
    continuousAt_id.prodMk htopContinuous
  have hfsource : ∀ᶠ t in nhds c, (t, f t) ∈ R.source :=
    hfgraph.eventually (R.open_source.mem_nhds hqsource)
  have htopsource : ∀ᶠ t in nhds c, (t, top t) ∈ R.source :=
    htopgraph.eventually (R.open_source.mem_nhds hqsource)
  filter_upwards [hroot, hfsource, htopsource] with t hfroot hfmem htmem
  have htoproot : detAt (t, top t) = 0 := by
    exact sixVertexSectorCharacteristicDet_top_eq_zero hn t
  have hfH : H (t, f t) = (t, 0) := by simp [H, detAt, hfroot]
  have htopH : H (t, top t) = (t, 0) := by simp [H, htoproot]
  have hfinv := R.left_inv hfmem
  have htopinv := R.left_inv htmem
  have hfinv' : R.symm (t, 0) = (t, f t) := by
    rw [← hfH]
    simpa [R] using hfinv
  have htopinv' : R.symm (t, 0) = (t, top t) := by
    rw [← htopH]
    simpa [R] using htopinv
  have hpairs : (t, f t) = (t, top t) := by
    exact hfinv'.symm.trans htopinv'
  exact congrArg Prod.snd hpairs



theorem sixVertexSectorTopEigenvalue_eqOn_of_analytic_characteristicRoot
    {N n : Nat} (hn : n ≤ N) {U : Set Real} (hU : IsPreconnected U)
    (hUopen : IsOpen U)
    (hUpos : U ⊆ Set.Ioi 0)
    {c : Real} (hcU : c ∈ U) (hc : 0 < c) {f : Real → Real}
    (hf : AnalyticOnNhd Real f U)
    (hroot : ∀ t ∈ U,
      Matrix.det
        (f t •
            (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) -
          sixVertexSectorTransfer N n t) = 0)
    (hfc : f c = sixVertexSectorTopEigenvalue N n hn c) :
    Set.EqOn f (sixVertexSectorTopEigenvalue N n hn) U := by
  have htop : AnalyticOnNhd Real
      (sixVertexSectorTopEigenvalue N n hn) U := by
    intro t ht
    exact analyticAt_sixVertexSectorTopEigenvalue hn (hUpos ht)
  apply hf.eqOn_of_preconnected_of_eventuallyEq htop hU hcU
  apply eventuallyEq_sixVertexSectorTopEigenvalue_of_characteristicRoot
    hn hc (hf c hcU).continuousAt hfc
  filter_upwards [hUopen.mem_nhds hcU] with t ht
  exact hroot t ht

end

end StatMech.FrontierD
