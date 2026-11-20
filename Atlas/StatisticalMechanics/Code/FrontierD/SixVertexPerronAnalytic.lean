/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheVandermonde
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.Deriv.Polynomial









open Finset Matrix Filter Topology

namespace StatMech.FrontierD

noncomputable section

theorem analyticAt_sixVertexSectorTransfer_apply
    (N n : Nat) (x y : SixVertexSector N n) (c : Real) :
    AnalyticAt Real (fun t ↦ sixVertexSectorTransfer N n t x y) c := by
  unfold sixVertexSectorTransfer sixVertexTransfer
  split_ifs <;> fun_prop


theorem analyticAt_sixVertexSectorCharacteristicDet
    (N n : Nat) (z : Real × Real) :
    AnalyticAt Real (fun q : Real × Real ↦ Matrix.det
      (q.2 • (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) -
        sixVertexSectorTransfer N n q.1)) z := by
  rw [show (fun q : Real × Real ↦ Matrix.det
        (q.2 • (1 : Matrix (SixVertexSector N n)
            (SixVertexSector N n) Real) -
          sixVertexSectorTransfer N n q.1)) =
      fun q ↦ ∑ sigma : Equiv.Perm (SixVertexSector N n),
        Equiv.Perm.sign sigma * ∏ i,
          (q.2 • (1 : Matrix (SixVertexSector N n)
              (SixVertexSector N n) Real) -
            sixVertexSectorTransfer N n q.1) (sigma i) i by
    funext q
    rw [Matrix.det_apply']]
  rw [show (fun q : Real × Real ↦
      ∑ sigma : Equiv.Perm (SixVertexSector N n),
        (((Equiv.Perm.sign sigma : Int) : Real)) * ∏ i,
          (q.2 • (1 : Matrix (SixVertexSector N n)
              (SixVertexSector N n) Real) -
            sixVertexSectorTransfer N n q.1) (sigma i) i) =
      ∑ sigma : Equiv.Perm (SixVertexSector N n), fun q : Real × Real ↦
        (((Equiv.Perm.sign sigma : Int) : Real)) * ∏ i,
          (q.2 • (1 : Matrix (SixVertexSector N n)
              (SixVertexSector N n) Real) -
            sixVertexSectorTransfer N n q.1) (sigma i) i by
    funext q
    simp]
  apply Finset.analyticAt_sum
  intro sigma _
  apply AnalyticAt.mul
  · fun_prop
  · rw [show (fun q : Real × Real ↦ ∏ i : SixVertexSector N n,
        (q.2 • (1 : Matrix (SixVertexSector N n)
            (SixVertexSector N n) Real) -
          sixVertexSectorTransfer N n q.1) (sigma i) i) =
      ∏ i : SixVertexSector N n, fun q : Real × Real ↦
        (q.2 • (1 : Matrix (SixVertexSector N n)
            (SixVertexSector N n) Real) -
          sixVertexSectorTransfer N n q.1) (sigma i) i by
      funext q
      simp]
    apply Finset.analyticAt_prod
    intro i _
    have hentry : AnalyticAt Real
        (fun q : Real × Real ↦
          sixVertexSectorTransfer N n q.1 (sigma i) i) z := by
      simpa only [Function.comp_apply] using
        (analyticAt_sixVertexSectorTransfer_apply N n (sigma i) i z.1).comp
          analyticAt_fst
    exact (analyticAt_snd.mul analyticAt_const).sub hentry

theorem analyticOnNhd_sixVertexSectorCharacteristicDet (N n : Nat) :
    AnalyticOnNhd Real (fun q : Real × Real ↦ Matrix.det
      (q.2 • (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) -
        sixVertexSectorTransfer N n q.1)) Set.univ := by
  intro z _
  exact analyticAt_sixVertexSectorCharacteristicDet N n z




theorem sixVertexSectorTop_charpoly_rootMultiplicity
    {N n : Nat} (hn : n ≤ N) {c : Real} (hc : 0 < c) :
    (sixVertexSectorTransfer N n c).charpoly.rootMultiplicity
      (sixVertexSectorTopEigenvalue N n hn c) = 1 := by
  let A := sixVertexSectorTransfer N n c
  let hA := sixVertexSectorTransfer_isHermitian N n c
  let T := Matrix.toEuclideanLin A
  let μ := sixVertexSectorTopEigenvalue N n hn c
  rw [← Polynomial.count_roots]
  rw [hA.roots_charpoly_eq_eigenvalues₀]
  change (Multiset.map hA.eigenvalues₀ Finset.univ.val).count μ = 1
  rw [Multiset.count_map]
  rw [← Finset.filter_val]
  change (Finset.univ.filter (fun i ↦ μ = hA.eigenvalues₀ i)).card = 1
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hcard := hT.card_filter_eigenvalues_eq finrank_euclideanSpace μ
  change (Finset.univ.filter fun i ↦ hA.eigenvalues₀ i = μ).card = _
    at hcard
  rw [show (Finset.univ.filter fun i ↦ μ = hA.eigenvalues₀ i) =
      Finset.univ.filter (fun i ↦ hA.eigenvalues₀ i = μ) by
    ext i
    simp [eq_comm]]
  rw [hcard]
  exact sixVertexSectorTop_eigenspace_finrank hn hc



theorem sixVertexSectorTop_charpoly_derivative_ne_zero
    {N n : Nat} (hn : n ≤ N) {c : Real} (hc : 0 < c) :
    (sixVertexSectorTransfer N n c).charpoly.derivative.eval
      (sixVertexSectorTopEigenvalue N n hn c) ≠ 0 := by
  let p := (sixVertexSectorTransfer N n c).charpoly
  let μ := sixVertexSectorTopEigenvalue N n hn c
  have hp : p ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hmult : p.rootMultiplicity μ = 1 :=
    sixVertexSectorTop_charpoly_rootMultiplicity hn hc
  intro hder
  have hroot : p.IsRoot μ :=
    (Polynomial.rootMultiplicity_pos hp).mp (by rw [hmult]; omega)
  have hmultiple : 1 < p.rootMultiplicity μ :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).mpr ⟨hroot, hder⟩
  rw [hmult] at hmultiple
  omega




theorem sixVertexSectorTopEigenvalue_eq_sSup
    {N n : Nat} (hn : n ≤ N) (c : Real) :
    sixVertexSectorTopEigenvalue N n hn c = sSup
      ((fun x : EuclideanSpace Real (SixVertexSector N n) ↦
        (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c)).toContinuousLinearMap
          |>.reApplyInnerSelf x) '' Metric.sphere 0 1) := by
  let A := sixVertexSectorTransfer N n c
  let T := Matrix.toEuclideanLin A
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (sixVertexSectorTransfer_isHermitian N n c)
  let T' := hT.toSelfAdjoint
  let p := sixVertexPackedSector N n hn
  let e : EuclideanSpace Real (SixVertexSector N n) := EuclideanSpace.single p 1
  have he : ‖e‖ = 1 := by simp [e]
  have hsphere : (Metric.sphere
      (0 : EuclideanSpace Real (SixVertexSector N n)) 1).Nonempty :=
    ⟨e, by simp [he]⟩
  obtain ⟨v, hv, hmax⟩ := (isCompact_sphere
    (0 : EuclideanSpace Real (SixVertexSector N n)) 1).exists_isMaxOn hsphere
      T'.val.reApplyInnerSelf_continuous.continuousOn
  have hvnorm : ‖v‖ = 1 := by simpa using hv
  have hvne : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hvnorm
    norm_num at hvnorm
  let μ : Real := T'.val.rayleighQuotient v
  have heig : Module.End.HasEigenvector T μ v := by
    have hmax' : IsMaxOn T'.val.reApplyInnerSelf (Metric.sphere 0 ‖v‖) v := by
      simpa only [hvnorm] using hmax
    exact T'.prop.hasEigenvector_of_isLocalExtrOn hvne (Or.inr hmax'.localize)
  have hmu : μ = T'.val.reApplyInnerSelf v := by
    simp [μ, ContinuousLinearMap.rayleighQuotient, hvnorm]
  have hmuEig : Module.End.HasEigenvalue T μ :=
    Module.End.hasEigenvalue_of_hasEigenvector heig
  obtain ⟨i, hi⟩ := hT.exists_eigenvalues_eq finrank_euclideanSpace hmuEig
  have hμtop : μ ≤ sixVertexSectorTopEigenvalue N n hn c := by
    rw [← hi]
    exact sixVertexSectorTopEigenvalue_ge N n hn c i
  let i0 := sixVertexSectorTopIndex N n hn
  let u := hT.eigenvectorBasis finrank_euclideanSpace i0
  have hunorm : ‖u‖ = 1 :=
    hT.eigenvectorBasis finrank_euclideanSpace |>.orthonormal.1 i0
  have hu : u ∈ Metric.sphere
      (0 : EuclideanSpace Real (SixVertexSector N n)) 1 := by
    simp [hunorm]
  have huq : T'.val.reApplyInnerSelf u =
      sixVertexSectorTopEigenvalue N n hn c := by
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    change @inner Real _ _ (T u) u = _
    rw [hT.apply_eigenvectorBasis finrank_euclideanSpace i0]
    rw [inner_smul_left, real_inner_self_eq_norm_sq, hunorm]
    simp only [one_pow, mul_one]
    change hT.eigenvalues finrank_euclideanSpace i0 =
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (sixVertexSectorTransfer_isHermitian N n c)).eigenvalues
          finrank_euclideanSpace i0
    exact congrArg (fun h : T.IsSymmetric ↦
      h.eigenvalues finrank_euclideanSpace i0) (Subsingleton.elim _ _)
  have htopmu : sixVertexSectorTopEigenvalue N n hn c ≤ μ := by
    rw [hmu, ← huq]
    exact hmax hu
  have hmueq : μ = sixVertexSectorTopEigenvalue N n hn c :=
    le_antisymm hμtop htopmu
  symm
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · exact hsphere.image _
  · rintro y ⟨x, hx, rfl⟩
    change T'.val.reApplyInnerSelf x ≤ _
    rw [← hmueq, hmu]
    exact hmax hx
  · intro y hy
    refine ⟨T'.val.reApplyInnerSelf v, ⟨v, hv, rfl⟩, ?_⟩
    rwa [← hmu, hmueq]

theorem continuous_sixVertexSectorRayleighFamily (N n : Nat) :
    Continuous (Function.uncurry fun c : Real ↦
      fun x : EuclideanSpace Real (SixVertexSector N n) ↦
        (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c)).toContinuousLinearMap.reApplyInnerSelf x) := by
  rw [show (Function.uncurry fun c : Real ↦
      fun x : EuclideanSpace Real (SixVertexSector N n) ↦
        (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c)).toContinuousLinearMap.reApplyInnerSelf x) =
      fun q : Real × EuclideanSpace Real (SixVertexSector N n) ↦
        ∑ i, ∑ j, sixVertexSectorTransfer N n q.1 i j * q.2 j * q.2 i by
    funext q
    change
      (Matrix.toEuclideanLin (sixVertexSectorTransfer N n q.1)).toContinuousLinearMap.reApplyInnerSelf q.2 = _
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    change @inner Real _ _
      (Matrix.toEuclideanLin (sixVertexSectorTransfer N n q.1) q.2) q.2 = _
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [Matrix.ofLp_toLpLin, star_trivial, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    change q.2 i * (∑ j, sixVertexSectorTransfer N n q.1 i j * q.2 j) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring]
  rw [continuous_iff_continuousAt]
  intro q
  have hentry (i j : SixVertexSector N n) : ContinuousAt
      (fun q : Real × EuclideanSpace Real (SixVertexSector N n) ↦
        sixVertexSectorTransfer N n q.1 i j) q :=
    (analyticAt_sixVertexSectorTransfer_apply N n i j q.1).continuousAt.comp
      continuousAt_fst
  fun_prop


theorem continuous_sixVertexSectorTopEigenvalue
    {N n : Nat} (hn : n ≤ N) :
    Continuous (sixVertexSectorTopEigenvalue N n hn) := by
  rw [show sixVertexSectorTopEigenvalue N n hn = fun c ↦ sSup
      ((fun x : EuclideanSpace Real (SixVertexSector N n) ↦
        (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c)).toContinuousLinearMap.reApplyInnerSelf x) ''
          Metric.sphere 0 1) by
    funext c
    exact sixVertexSectorTopEigenvalue_eq_sSup hn c]
  exact (isCompact_sphere
    (0 : EuclideanSpace Real (SixVertexSector N n)) 1).continuous_sSup
      (continuous_sixVertexSectorRayleighFamily N n)

theorem sixVertexSectorCharacteristicDet_top_eq_zero
    {N n : Nat} (hn : n ≤ N) (c : Real) :
    Matrix.det
      (sixVertexSectorTopEigenvalue N n hn c •
          (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) -
        sixVertexSectorTransfer N n c) = 0 := by
  rw [show sixVertexSectorTopEigenvalue N n hn c •
      (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) =
      Matrix.scalar (SixVertexSector N n)
        (sixVertexSectorTopEigenvalue N n hn c) by
    ext i j
    simp [Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal_apply]]
  rw [← Matrix.eval_charpoly]
  let hA := sixVertexSectorTransfer_isHermitian N n c
  apply Polynomial.IsRoot.def.mp
  have hmem : sixVertexSectorTopEigenvalue N n hn c ∈
      (sixVertexSectorTransfer N n c).charpoly.roots := by
    rw [hA.roots_charpoly_eq_eigenvalues₀]
    apply Multiset.mem_map.mpr
    exact ⟨sixVertexSectorTopIndex N n hn, by simp, rfl⟩
  exact (Polynomial.mem_roots').mp hmem |>.2

private noncomputable def sixVertexSectorCharacteristicDet
    (N n : Nat) (q : Real × Real) : Real :=
  Matrix.det
    (q.2 • (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) -
      sixVertexSectorTransfer N n q.1)

private noncomputable def sixVertexSectorCharacteristicGraph
    (N n : Nat) (q : Real × Real) : Real × Real :=
  (q.1, sixVertexSectorCharacteristicDet N n q)

private theorem sixVertexSectorCharacteristicDet_prodMk
    (N n : Nat) (c t : Real) :
    sixVertexSectorCharacteristicDet N n (c, t) =
      (sixVertexSectorTransfer N n c).charpoly.eval t := by
  rw [Matrix.eval_charpoly]
  unfold sixVertexSectorCharacteristicDet
  congr 1
  ext i j
  simp [Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal_apply]

private theorem analyticAt_sixVertexSectorCharacteristicGraph
    (N n : Nat) (q : Real × Real) :
    AnalyticAt Real (sixVertexSectorCharacteristicGraph N n) q := by
  apply analyticAt_fst.prod
  simpa only [sixVertexSectorCharacteristicDet] using
    analyticAt_sixVertexSectorCharacteristicDet N n q

private theorem sixVertexSectorCharacteristicGraph_fderiv_injective
    {N n : Nat} (hn : n ≤ N) {c : Real} (hc : 0 < c) :
    Function.Injective (fderiv Real (sixVertexSectorCharacteristicGraph N n)
      (c, sixVertexSectorTopEigenvalue N n hn c)) := by
  let μ := sixVertexSectorTopEigenvalue N n hn c
  let q₀ : Real × Real := (c, μ)
  let L := fderiv Real (sixVertexSectorCharacteristicGraph N n) q₀
  let b := (sixVertexSectorTransfer N n c).charpoly.derivative.eval μ
  have hb : b ≠ 0 := sixVertexSectorTop_charpoly_derivative_ne_zero hn hc
  have hH : AnalyticAt Real (sixVertexSectorCharacteristicGraph N n) q₀ :=
    analyticAt_sixVertexSectorCharacteristicGraph N n q₀
  have hfirstDeriv : HasFDerivAt
      (fun q ↦ (sixVertexSectorCharacteristicGraph N n q).1)
      ((ContinuousLinearMap.fst Real Real Real).comp L) q₀ :=
    hH.hasStrictFDerivAt.hasFDerivAt.fst
  have hfirst : (ContinuousLinearMap.fst Real Real Real).comp L =
      ContinuousLinearMap.fst Real Real Real := by
    apply HasFDerivAt.unique hfirstDeriv
    simpa only [sixVertexSectorCharacteristicGraph] using
      (hasFDerivAt_fst (p := q₀))
  have hcurve : HasDerivAt
      (fun t : Real ↦ sixVertexSectorCharacteristicGraph N n (c, t))
      (0, b) μ := by
    apply (hasDerivAt_const μ c).prodMk
    simpa only [sixVertexSectorCharacteristicGraph,
      sixVertexSectorCharacteristicDet_prodMk, b] using
        (sixVertexSectorTransfer N n c).charpoly.hasDerivAt μ
  have hline : HasDerivAt (fun t : Real ↦ (c, t)) (0, 1) μ :=
    (hasDerivAt_const μ c).prodMk (hasDerivAt_id μ)
  have hcurve' := hH.hasStrictFDerivAt.hasFDerivAt.comp μ hline
  have hvertical : L (0, 1) = (0, b) := by
    have heq := hcurve'.unique hcurve.hasFDerivAt
    have happ := congrArg (fun K : Real →L[Real] Real × Real ↦ K 1) heq
    simpa [L, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply] using happ
  change Function.Injective L
  intro v w hvw
  apply sub_eq_zero.mp
  let z := v - w
  have hz : L z = 0 := by simp [z, hvw]
  have hLzfirst : (L z).1 = z.1 := by
    have happ := congrArg (fun K : (Real × Real) →L[Real] Real ↦ K z) hfirst
    exact happ
  have hzfirst : z.1 = 0 := by rw [← hLzfirst, hz]; rfl
  have hzdecomp : z = z.2 • ((0, 1) : Real × Real) := by
    ext <;> simp [hzfirst]
  have hzsecond : z.2 * b = 0 := by
    have hzsnd := congrArg Prod.snd hz
    rw [hzdecomp, map_smul, hvertical] at hzsnd
    simpa [mul_comm] using hzsnd
  have : z.2 = 0 := (mul_eq_zero.mp hzsecond).resolve_right hb
  exact Prod.ext hzfirst this



theorem analyticAt_sixVertexSectorTopEigenvalue
    {N n : Nat} (hn : n ≤ N) {c : Real} (hc : 0 < c) :
    AnalyticAt Real (sixVertexSectorTopEigenvalue N n hn) c := by
  let μ := sixVertexSectorTopEigenvalue N n hn c
  let q₀ : Real × Real := (c, μ)
  let H := sixVertexSectorCharacteristicGraph N n
  let L := fderiv Real H q₀
  have hH : AnalyticAt Real H q₀ :=
    analyticAt_sixVertexSectorCharacteristicGraph N n q₀
  have hLinj : Function.Injective L :=
    sixVertexSectorCharacteristicGraph_fderiv_injective hn hc
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
  have hR : AnalyticAt Real R.symm (H q₀) := by
    apply R.analyticAt_symm' hqsource
    · simpa [R] using hH
    · simpa [R] using hHe.hasFDerivAt.fderiv
  have hdet0 : sixVertexSectorCharacteristicDet N n q₀ = 0 := by
    exact sixVertexSectorCharacteristicDet_top_eq_zero hn c
  have hHq₀ : H q₀ = (c, (0 : Real)) := by simp [H, q₀, μ, hdet0,
    sixVertexSectorCharacteristicGraph]
  let g : Real → Real := fun t => (R.symm (t, (0 : Real))).2
  have hg : AnalyticAt Real g c := by
    rw [hHq₀] at hR
    have hinput : AnalyticAt Real (fun t : Real => (t, (0 : Real))) c :=
      analyticAt_id.prod analyticAt_const
    have hcomp : AnalyticAt Real
        (R.symm ∘ fun t : Real => (t, (0 : Real))) c :=
      hR.comp (f := fun t : Real => (t, (0 : Real))) (x := c) hinput
    have hsnd : AnalyticAt Real
        (Prod.snd ∘ R.symm ∘ fun t : Real => (t, (0 : Real))) c :=
      analyticAt_snd.comp hcomp
    simpa only [Function.comp_apply] using hsnd
  apply hg.congr
  have htopContinuous : ContinuousAt
      (sixVertexSectorTopEigenvalue N n hn) c :=
    (continuous_sixVertexSectorTopEigenvalue hn).continuousAt
  have hgraph : Tendsto
      (fun t => (t, sixVertexSectorTopEigenvalue N n hn t))
      (𝓝 c) (𝓝 q₀) := by
    exact continuousAt_id.prodMk htopContinuous
  have hsource : ∀ᶠ t in 𝓝 c,
      (t, sixVertexSectorTopEigenvalue N n hn t) ∈ R.source :=
    hgraph.eventually (R.open_source.mem_nhds hqsource)
  filter_upwards [hsource] with t ht
  have hleft := R.left_inv ht
  have hdet := sixVertexSectorCharacteristicDet_top_eq_zero hn t
  have hdet' : sixVertexSectorCharacteristicDet N n
      (t, sixVertexSectorTopEigenvalue N n hn t) = 0 := hdet
  have hHtop : H (t, sixVertexSectorTopEigenvalue N n hn t) =
      (t, (0 : Real)) := by
    simp [H, sixVertexSectorCharacteristicGraph, hdet']
  have hinv : R.symm (t, (0 : Real)) =
      (t, sixVertexSectorTopEigenvalue N n hn t) := by
    rw [← hHtop]
    simpa [R] using hleft
  exact congrArg Prod.snd hinv

theorem analyticOnNhd_sixVertexSectorTopEigenvalue
    {N n : Nat} (hn : n ≤ N) :
    AnalyticOnNhd Real (sixVertexSectorTopEigenvalue N n hn) (Set.Ioi 0) := by
  intro c hc
  exact analyticAt_sixVertexSectorTopEigenvalue hn hc

end

end StatMech.FrontierD
