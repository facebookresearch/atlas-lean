/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOddAnalyticCandidateSheet
import Code.FrontierD.SixVertexBetheFixedChargeStability
import Code.FrontierD.SixVertexBetheTailUniqueness





open Filter Topology

namespace StatMech.FrontierD

noncomputable section

private theorem oddCoveringMap_injective_of_unique_fiber_Icc
    {a b : Real} (hab : a ≤ b) {E : Type*} [TopologicalSpace E]
    (p : E -> Set.Icc a b) (hcov : IsCoveringMap p)
    (x0 : Set.Icc a b) (e0 : E) (he0 : p e0 = x0)
    (hfiber : ∀ e, p e = x0 -> e = e0) : Function.Injective p := by
  intro e1 e2 heq
  let x := p e1
  let f : C(Real, Set.Icc a b) :=
    ⟨fun t => Set.projIcc a b hab ((1 - t) * x0.1 + t * x.1), by fun_prop⟩
  have hf0 : f 0 = x0 := by
    apply Subtype.ext
    simp [f, Set.projIcc_of_mem hab x0.2]
  have hf1 : f 1 = x := by
    apply Subtype.ext
    simp [f, Set.projIcc_of_mem hab x.2]
  letI : ContractibleSpace Real :=
    (contractible_iff_id_nullhomotopic Real).mpr
      ⟨0, ⟨ContinuousMap.Homotopy.affine
        (ContinuousMap.id Real) (ContinuousMap.const Real 0)⟩⟩
  have uniqueLift := hcov.existsUnique_continuousMap_lifts f 0 e0
    (he0.trans hf0.symm)
  obtain ⟨F, hF0, hFlift⟩ := uniqueLift.exists
  have endpoint (e : E) (he : p e = x) : F 1 = e := by
    have uniqueFromE := hcov.existsUnique_continuousMap_lifts f 1 e
      (he.trans hf1.symm)
    obtain ⟨G, hG1, hGlift⟩ := uniqueFromE.exists
    have hG0proj : p (G 0) = x0 := by
      have h := congrFun hGlift 0
      simpa only [Function.comp_apply, hf0] using h
    have hG0 : G 0 = e0 := hfiber (G 0) hG0proj
    have hGF : G = F := uniqueLift.unique
      ⟨hG0, hGlift⟩ ⟨hF0, hFlift⟩
    rw [← hGF, hG1]
  have he1 : p e1 = x := rfl
  have he2 : p e2 = x := heq.symm.trans he1
  exact (endpoint e1 he1).symm.trans (endpoint e2 he2)

set_option maxHeartbeats 800000 in



theorem sixVertexOddSymmetricCandidate_eq_top_of_uniqueTailFixedChargeDensityGauge
    {a b c0 c1 : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc0 : c0 ∈ Set.Icc a b) (hc1 : c1 ∈ Set.Icc a b)
    (hc0int : c0 ∈ Set.Ioo a b) (hc1int : c1 ∈ Set.Ioo a b)
    {N m charge : Nat} (hm : 0 < m) (hN : 0 < N)
    (hcharge : N = 2 * ((m + 1) + m) + 2 * charge)
    (rho : C(Set.Icc a b × Real, Real))
    (hrhoEq : ∀ t : Set.Icc a b,
      SixVertexSatisfiesContinuousDensityEquation t.1
        (sixVertexContinuumDensityAt rho t))
    (hrhoMass : ∀ t : Set.Icc a b,
      ∫ y in -Real.pi..Real.pi, sixVertexContinuumDensityAt rho t y = 1 / 2)
    {rhoLower inner outer : Real} (hrhoLower : 0 < rhoLower)
    (hrho : ∀ (t : Set.Icc a b) x,
      rhoLower ≤ sixVertexContinuumDensityAt rho t x)
    (hio : inner < outer)
    (houter : ∀ t : Set.Icc a b, outer ≤ rhoLower *
      ((sixVertexAnisotropyMagnitude t.1 - 1) /
        sixVertexRootDensityScale t.1) / 2)
    (hinner : ∀ t : Set.Icc a b,
      sixVertexRootDensityContractionRate t.1 * outer +
          sixVertexFixedChargeDensityStabilityErrorOfLower
            t.1 N charge (rhoLower / 2) ≤ inner)
    (hmargin : ∀ t : Set.Icc a b,
      sixVertexSymmetricScatteringBoundaryBound t.1 +
        2 * sixVertexSymmetricJacobianTotalErrorOfLower
          t.1 N (rhoLower / 2) < 2 * Real.pi)
    (z0 z1 : SixVertexBetheContinuationSpace a b N ((m + 1) + m))
    (hz0g : sixVertexContinuationWeightedFiniteDensityGauge
      ha N ((m + 1) + m) rho z0 < outer)
    (hz1g : sixVertexContinuationWeightedFiniteDensityGauge
      ha N ((m + 1) + m) rho z1 < outer)
    (hz0 : sixVertexBetheContinuationProjection z0 = ⟨c0, hc0⟩)
    (hz1 : sixVertexBetheContinuationProjection z1 = ⟨c1, hc1⟩)
    (htail : ((((m + 1) + m : Nat) : Real)) <
      sixVertexAnisotropyMagnitude c0)
    (hbase : sixVertexZeroPhaseBetheEigenvalueValue c0 N z0.1.2
        (sixVertexOddCentralIndex m) =
      sixVertexSectorTopEigenvalue N ((m + 1) + m) (by omega) c0)
    (hwave : sixVertexCoordinateBetheWave (N := N) c0 z0.1.2 ≠ 0) :
    sixVertexZeroPhaseBetheEigenvalueValue c1 N z1.1.2
        (sixVertexOddCentralIndex m) =
      sixVertexSectorTopEigenvalue N ((m + 1) + m) (by omega) c1 := by
  let g : SixVertexBetheContinuationSpace a b N ((m + 1) + m) -> Real :=
    sixVertexContinuationWeightedFiniteDensityGauge ha N ((m + 1) + m) rho
  let C : Set (SixVertexBetheContinuationSpace a b N ((m + 1) + m)) :=
    {z | g z < outer}
  have hg : Continuous g :=
    continuous_sixVertexContinuationWeightedFiniteDensityGauge
      ha N ((m + 1) + m) rho
  have hgap : ∀ z, ¬(inner < g z ∧ g z < outer) := by
    intro z
    have hgap' :=
      sixVertexContinuationWeightedFiniteDensityGauge_solutionFreeAnnulus_fixedCharge
        ha hN (n := (m + 1) + m - 1) (q := (m + 1) + m)
          (r := charge) (by omega) (by omega) rho hrhoEq hrhoMass
            hrhoLower hrho houter hinner
    simpa only [g] using hgap' z
  have hcover : 2 * ((m + 1) + m) ≤ N := by omega
  have hcount : (m + 1) + m ≤ N := by omega
  have hjac : ∀ z, g z < outer -> Function.Injective
      (sixVertexOddSymmetricBetheRootJacobian N m z.1.1
        (sixVertexOddPositiveHalfProjection m z.1.2)) := by
    intro z hzg
    exact sixVertexContinuationWeightedFiniteDensityGauge_oddJacobianInjective
      ha hm hN hcover hcount rho hrhoLower hrho houter hmargin z hzg
  have hCopen : IsOpen C := isOpen_lt hg continuous_const
  have hCeq : C = {z | g z ≤ inner} :=
    sixVertex_stabilityGauge_lt_eq_le g hio hgap
  have hCcompact : IsCompact C := by
    rw [hCeq]
    letI : CompactSpace
        (SixVertexBetheContinuationSpace a b N ((m + 1) + m)) :=
      isCompact_iff_compactSpace.mp
        (isCompact_sixVertexBetheContinuationSet ha hN)
    exact (isClosed_le hg continuous_const).isCompact
  let zC0 : C := ⟨z0, hz0g⟩
  let zC1 : C := ⟨z1, hz1g⟩
  have hzC0 : sixVertexBetheContinuationProjectionOn C zC0 = ⟨c0, hc0⟩ := by
    simpa [zC0, sixVertexBetheContinuationProjectionOn] using hz0
  have hzC1 : sixVertexBetheContinuationProjectionOn C zC1 = ⟨c1, hc1⟩ := by
    simpa [zC1, sixVertexBetheContinuationProjectionOn] using hz1
  have hlocal : IsLocalHomeomorph
      (sixVertexBetheContinuationProjectionOn C) :=
    isLocalHomeomorph_sixVertexBetheContinuationProjectionOn_of_oddSymmetricJacobian
      ha hN hcover C hCopen (fun z hz => hjac z hz)
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hCcompact
  have hproj : Continuous (sixVertexBetheContinuationProjectionOn C) :=
    continuous_sixVertexBetheContinuationProjectionOn C
  have hcovOn : IsCoveringMapOn
      (sixVertexBetheContinuationProjectionOn C) Set.univ :=
    IsCoveringMapOn.of_openPartialHomeomorph hproj
      (fun e _ => by
        obtain ⟨phi, he, hphi⟩ := hlocal e
        exact ⟨phi, he, hphi.symm⟩)
  have hcov : IsCoveringMap (sixVertexBetheContinuationProjectionOn C) :=
    isCoveringMap_iff_isCoveringMapOn_univ.mpr hcovOn
  have hfiber : ∀ z : C,
      sixVertexBetheContinuationProjectionOn C z = ⟨c0, hc0⟩ -> z = zC0 := by
    intro z hz
    have hparam : z.1.1.1 = c0 := by
      have h := congrArg Subtype.val hz
      simpa [sixVertexBetheContinuationProjectionOn,
        sixVertexBetheContinuationProjection] using h
    have hzsol : SixVertexSatisfiesBetheEquations c0 N ((m + 1) + m)
        z.1.1.2 := by
      have h := (sixVertexBetheUpdate_eq_self_iff hN z.1.1.2).mp z.1.2.2.2
      simpa [hparam] using h
    have hz0sol : SixVertexSatisfiesBetheEquations c0 N ((m + 1) + m)
        z0.1.2 := by
      have h := (sixVertexBetheUpdate_eq_self_iff hN z0.1.2).mp z0.2.2.2
      have hparam0 : z0.1.1 = c0 := by
        have hp := congrArg Subtype.val hz0
        simpa [sixVertexBetheContinuationProjection] using hp
      simpa [hparam0] using h
    have hroots : z.1.1.2 = z0.1.2 :=
      sixVertexBetheSolution_unique_of_anisotropyMagnitude
        (ha.trans_le hc0.1) (by omega) htail hzsol hz0sol
    have hparam0 : z0.1.1 = c0 := by
      have hp := congrArg Subtype.val hz0
      simpa [sixVertexBetheContinuationProjection] using hp
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (hparam.trans hparam0.symm) hroots
  have hinj : Function.Injective (sixVertexBetheContinuationProjectionOn C) :=
    oddCoveringMap_injective_of_unique_fiber_Icc hab _ hcov ⟨c0, hc0⟩ zC0
      hzC0 hfiber
  obtain ⟨roots, hroots0, hrootsMem⟩ :=
    exists_sixVertexContinuousBetheBranch_of_compactComponent_mem
      hab hc0 C hCcompact hlocal zC0 hzC0
  have hrootsData : ∀ t ∈ Set.Icc a b,
      SixVertexOpenRootSimplex (roots t) ∧
      SixVertexSatisfiesBetheEquations t N ((m + 1) + m) (roots t) := by
    intro t ht
    obtain ⟨z, hzC', hzt, hzroots⟩ := hrootsMem t ht
    have hzopen : SixVertexOpenRootSimplex z.1.2 :=
      sixVertexBetheContinuationSet_subset_open ha hcover z.2
    have hzsol : SixVertexSatisfiesBetheEquations z.1.1 N ((m + 1) + m)
        z.1.2 :=
      (sixVertexBetheUpdate_eq_self_iff hN z.1.2).mp z.2.2.2
    constructor
    · simpa [← hzroots] using hzopen
    · simpa [hzt, hzroots] using hzsol
  have hrootsJac : ∀ t ∈ Set.Ioo a b, Function.Injective
      (sixVertexOddSymmetricBetheRootJacobian N m t
        (sixVertexOddPositiveHalfProjection m (roots t))) := by
    intro t ht
    obtain ⟨z, hzC', hzt, hzroots⟩ :=
      hrootsMem t ⟨ht.1.le, ht.2.le⟩
    simpa [hzt, hzroots] using hjac z hzC'
  have hrootsAnalytic : AnalyticOnNhd Real roots (Set.Ioo a b) :=
    analyticOnNhd_sixVertexContinuousOddSymmetricBetheBranch ha roots
      (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).1)
      (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).2) hrootsJac
  have hrootsTarget : roots c1 = z1.1.2 := by
    obtain ⟨z, hzC', hzt, hzroots⟩ := hrootsMem c1 hc1
    let zC : C := ⟨z, hzC'⟩
    have hzproj : sixVertexBetheContinuationProjectionOn C zC = ⟨c1, hc1⟩ := by
      apply Subtype.ext
      exact hzt
    have hzeq : zC = zC1 := hinj (hzproj.trans hzC1.symm)
    simpa [zC, zC1, ← hzroots] using
      congrArg (fun w : C => w.1.1.2) hzeq
  have hrootsBase : roots c0 = z0.1.2 := hroots0
  have hperron := sixVertexAnalyticOddSymmetricBetheCandidate_eqOn_top
    (N := N) (m := m) hm (by omega) isPreconnected_Ioo isOpen_Ioo
    (fun t ht => by change 2 < t; linarith [ht.1]) roots
    (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).1)
    (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).2)
    hrootsAnalytic hc0int (by simpa [hrootsBase] using hwave) (by
      simpa [hrootsBase] using hbase)
  simpa [hrootsTarget] using hperron hc1int

end

end StatMech.FrontierD
