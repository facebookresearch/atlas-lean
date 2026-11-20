/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheTailUniqueness
import Code.FrontierD.SixVertexBetheFixedChargeStability





open Filter Topology

namespace StatMech.FrontierD

noncomputable section

private theorem coveringMap_injective_of_unique_fiber_Icc
    {a b : Real} (hab : a ≤ b) {E : Type*} [TopologicalSpace E]
    (p : E → Set.Icc a b) (hcov : IsCoveringMap p)
    (x₀ : Set.Icc a b) (e₀ : E) (he₀ : p e₀ = x₀)
    (hfiber : ∀ e, p e = x₀ → e = e₀) : Function.Injective p := by
  intro e₁ e₂ heq
  let x := p e₁
  let f : C(Real, Set.Icc a b) :=
    ⟨fun t => Set.projIcc a b hab
        ((1 - t) * x₀.1 + t * x.1), by fun_prop⟩
  have hf0 : f 0 = x₀ := by
    apply Subtype.ext
    simp [f, Set.projIcc_of_mem hab x₀.2]
  have hf1 : f 1 = x := by
    apply Subtype.ext
    simp [f, Set.projIcc_of_mem hab x.2]
  letI : ContractibleSpace Real :=
    (contractible_iff_id_nullhomotopic Real).mpr
      ⟨0, ⟨ContinuousMap.Homotopy.affine
        (ContinuousMap.id Real) (ContinuousMap.const Real 0)⟩⟩
  have uniqueLift := hcov.existsUnique_continuousMap_lifts f 0 e₀
    (he₀.trans hf0.symm)
  obtain ⟨F, hF0, hFlift⟩ := uniqueLift.exists
  have endpoint (e : E) (he : p e = x) : F 1 = e := by
    have uniqueFromE := hcov.existsUnique_continuousMap_lifts f 1 e
      (he.trans hf1.symm)
    obtain ⟨G, hG1, hGlift⟩ := uniqueFromE.exists
    have hG0proj : p (G 0) = x₀ := by
      have h := congrFun hGlift 0
      simpa only [Function.comp_apply, hf0] using h
    have hG0 : G 0 = e₀ := hfiber (G 0) hG0proj
    have hGF : G = F := uniqueLift.unique
      ⟨hG0, hGlift⟩ ⟨hF0, hFlift⟩
    rw [← hGF, hG1]
  have he₁ : p e₁ = x := rfl
  have he₂ : p e₂ = x := heq.symm.trans he₁
  exact (endpoint e₁ he₁).symm.trans (endpoint e₂ he₂)

set_option maxHeartbeats 800000 in




theorem sixVertexEvenSymmetricCandidate_eq_top_of_uniqueTailDensityGauge
    {a b c₀ c₁ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Icc a b) (hc₁ : c₁ ∈ Set.Icc a b)
    (hc₀int : c₀ ∈ Set.Ioo a b) (hc₁int : c₁ ∈ Set.Ioo a b)
    {N m : Nat} (hm : 0 < m) (hN : 0 < N)
    (hhalf : N = 2 * (m + m))
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
          sixVertexFiniteDensityContinuumErrorOfLower t.1 N (rhoLower / 2) ≤ inner)
    (hmargin : ∀ t : Set.Icc a b,
      sixVertexSymmetricScatteringBoundaryBound t.1 +
        2 * sixVertexSymmetricJacobianTotalErrorOfLower
          t.1 N (rhoLower / 2) < 2 * Real.pi)
    (z₀ z₁ : SixVertexBetheContinuationSpace a b N (m + m))
    (hz₀g : sixVertexContinuationWeightedFiniteDensityGauge
      ha N (m + m) rho z₀ < outer)
    (hz₁g : sixVertexContinuationWeightedFiniteDensityGauge
      ha N (m + m) rho z₁ < outer)
    (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩)
    (hz₁ : sixVertexBetheContinuationProjection z₁ = ⟨c₁, hc₁⟩)
    (htail : ((m + m : Nat) : Real) < sixVertexAnisotropyMagnitude c₀)
    (hbase : sixVertexSymmetricBetheEigenvalueKernel c₀
        (sixVertexEvenPositiveHalfProjection m z₀.1.2) =
      sixVertexSectorTopEigenvalue N (m + m) (by omega) c₀)
    (hwave : sixVertexCoordinateBetheWave (N := N) c₀ z₀.1.2 ≠ 0) :
    sixVertexSymmetricBetheEigenvalueKernel c₁
        (sixVertexEvenPositiveHalfProjection m z₁.1.2) =
      sixVertexSectorTopEigenvalue N (m + m) (by omega) c₁ := by
  let g : SixVertexBetheContinuationSpace a b N (m + m) → Real :=
    sixVertexContinuationWeightedFiniteDensityGauge ha N (m + m) rho
  let C : Set (SixVertexBetheContinuationSpace a b N (m + m)) :=
    {z | g z < outer}
  have hg : Continuous g :=
    continuous_sixVertexContinuationWeightedFiniteDensityGauge ha N (m + m) rho
  have hgap : ∀ z, ¬(inner < g z ∧ g z < outer) := by
    intro z
    have hgap' :=
      sixVertexContinuationWeightedFiniteDensityGauge_solutionFreeAnnulus
        ha hN (n := m + m - 1) (r := m + m) (by omega)
          (by omega) (by omega) rho hrhoEq hrhoMass
          hrhoLower hrho houter hinner
    simpa only [g] using hgap' z
  have hcover : 2 * (m + m) ≤ N := by omega
  have hcount : m + m ≤ N := by omega
  have hjac : ∀ z, g z < outer → Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m z.1.1
        (sixVertexEvenPositiveHalfProjection m z.1.2)) := by
    intro z hzg
    exact sixVertexContinuationWeightedFiniteDensityGauge_jacobianInjective
      ha hm hN hcover hcount rho hrhoLower hrho houter hmargin z hzg
  have hCopen : IsOpen C := isOpen_lt hg continuous_const
  have hCeq : C = {z | g z ≤ inner} :=
    sixVertex_stabilityGauge_lt_eq_le g hio hgap
  have hCcompact : IsCompact C := by
    rw [hCeq]
    letI : CompactSpace (SixVertexBetheContinuationSpace a b N (m + m)) :=
      isCompact_iff_compactSpace.mp (isCompact_sixVertexBetheContinuationSet ha hN)
    exact (isClosed_le hg continuous_const).isCompact
  let zC₀ : C := ⟨z₀, hz₀g⟩
  let zC₁ : C := ⟨z₁, hz₁g⟩
  have hzC₀ : sixVertexBetheContinuationProjectionOn C zC₀ = ⟨c₀, hc₀⟩ := by
    simpa [zC₀, sixVertexBetheContinuationProjectionOn] using hz₀
  have hzC₁ : sixVertexBetheContinuationProjectionOn C zC₁ = ⟨c₁, hc₁⟩ := by
    simpa [zC₁, sixVertexBetheContinuationProjectionOn] using hz₁
  have hlocal : IsLocalHomeomorph
      (sixVertexBetheContinuationProjectionOn C) :=
    isLocalHomeomorph_sixVertexBetheContinuationProjectionOn_of_evenSymmetricJacobian
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
      sixVertexBetheContinuationProjectionOn C z = ⟨c₀, hc₀⟩ → z = zC₀ := by
    intro z hz
    have hparam : z.1.1.1 = c₀ := by
      have := congrArg Subtype.val hz
      simpa [sixVertexBetheContinuationProjectionOn,
        sixVertexBetheContinuationProjection] using this
    have hzsol : SixVertexSatisfiesBetheEquations c₀ N (m + m) z.1.1.2 := by
      have h := (sixVertexBetheUpdate_eq_self_iff hN z.1.1.2).mp z.1.2.2.2
      simpa [hparam] using h
    have hz₀sol : SixVertexSatisfiesBetheEquations c₀ N (m + m) z₀.1.2 := by
      have h := (sixVertexBetheUpdate_eq_self_iff hN z₀.1.2).mp z₀.2.2.2
      have hparam₀ : z₀.1.1 = c₀ := by
        have := congrArg Subtype.val hz₀
        simpa [sixVertexBetheContinuationProjection] using this
      simpa [hparam₀] using h
    have hroots : z.1.1.2 = z₀.1.2 :=
      sixVertexBetheSolution_unique_of_anisotropyMagnitude
        (ha.trans_le hc₀.1) (by omega) htail hzsol hz₀sol
    have hparam₀ : z₀.1.1 = c₀ := by
      have := congrArg Subtype.val hz₀
      simpa [sixVertexBetheContinuationProjection] using this
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (hparam.trans hparam₀.symm) hroots
  have hinj : Function.Injective (sixVertexBetheContinuationProjectionOn C) :=
    coveringMap_injective_of_unique_fiber_Icc hab _ hcov ⟨c₀, hc₀⟩ zC₀
      hzC₀ hfiber
  obtain ⟨roots, hroots₀, hrootsMem⟩ :=
    exists_sixVertexContinuousBetheBranch_of_compactComponent_mem
      hab hc₀ C hCcompact hlocal zC₀ hzC₀
  have hrootsData : ∀ t ∈ Set.Icc a b,
      SixVertexOpenRootSimplex (roots t) ∧
      SixVertexSatisfiesBetheEquations t N (m + m) (roots t) := by
    intro t ht
    obtain ⟨z, hzC', hzt, hzroots⟩ := hrootsMem t ht
    have hzopen : SixVertexOpenRootSimplex z.1.2 :=
      sixVertexBetheContinuationSet_subset_open ha hcover z.2
    have hzsol : SixVertexSatisfiesBetheEquations z.1.1 N (m + m) z.1.2 :=
      (sixVertexBetheUpdate_eq_self_iff hN z.1.2).mp z.2.2.2
    constructor
    · simpa [← hzroots] using hzopen
    · simpa [hzt, hzroots] using hzsol
  have hrootsJac : ∀ t ∈ Set.Ioo a b, Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m t
        (sixVertexEvenPositiveHalfProjection m (roots t))) := by
    intro t ht
    obtain ⟨z, hzC', hzt, hzroots⟩ := hrootsMem t ⟨ht.1.le, ht.2.le⟩
    simpa [hzt, hzroots] using hjac z hzC'
  have hrootsAnalytic : AnalyticOnNhd Real roots (Set.Ioo a b) :=
    analyticOnNhd_sixVertexContinuousEvenSymmetricBetheBranch ha roots
      (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).1)
      (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).2) hrootsJac
  have hrootsTarget : roots c₁ = z₁.1.2 := by
    obtain ⟨z, hzC', hzt, hzroots⟩ := hrootsMem c₁ hc₁
    let zC : C := ⟨z, hzC'⟩
    have hzproj : sixVertexBetheContinuationProjectionOn C zC = ⟨c₁, hc₁⟩ := by
      apply Subtype.ext
      exact hzt
    have hzeq : zC = zC₁ := hinj (hzproj.trans hzC₁.symm)
    simpa [zC, zC₁, ← hzroots] using congrArg (fun w : C => w.1.1.2) hzeq
  have hrootsBase : roots c₀ = z₀.1.2 := hroots₀
  have hperron := sixVertexAnalyticEvenSymmetricBetheCandidate_eqOn_top
    (N := N) (m := m) hm (by omega) isPreconnected_Ioo isOpen_Ioo
    (fun t ht => by change 2 < t; linarith [ht.1]) roots
    (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).1)
    (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).2)
    hrootsAnalytic hc₀int (by simpa [hrootsBase] using hwave) (by
      simpa [hrootsBase] using hbase)
  simpa [hrootsTarget] using hperron hc₁int

set_option maxHeartbeats 800000 in


theorem sixVertexEvenSymmetricCandidate_eq_top_of_uniqueTailFixedChargeDensityGauge
    {a b c₀ c₁ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Icc a b) (hc₁ : c₁ ∈ Set.Icc a b)
    (hc₀int : c₀ ∈ Set.Ioo a b) (hc₁int : c₁ ∈ Set.Ioo a b)
    {N m charge : Nat} (hm : 0 < m) (hN : 0 < N)
    (hcharge : N = 2 * (m + m) + 2 * charge)
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
    (z₀ z₁ : SixVertexBetheContinuationSpace a b N (m + m))
    (hz₀g : sixVertexContinuationWeightedFiniteDensityGauge
      ha N (m + m) rho z₀ < outer)
    (hz₁g : sixVertexContinuationWeightedFiniteDensityGauge
      ha N (m + m) rho z₁ < outer)
    (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩)
    (hz₁ : sixVertexBetheContinuationProjection z₁ = ⟨c₁, hc₁⟩)
    (htail : ((m + m : Nat) : Real) < sixVertexAnisotropyMagnitude c₀)
    (hbase : sixVertexSymmetricBetheEigenvalueKernel c₀
        (sixVertexEvenPositiveHalfProjection m z₀.1.2) =
      sixVertexSectorTopEigenvalue N (m + m) (by omega) c₀)
    (hwave : sixVertexCoordinateBetheWave (N := N) c₀ z₀.1.2 ≠ 0) :
    sixVertexSymmetricBetheEigenvalueKernel c₁
        (sixVertexEvenPositiveHalfProjection m z₁.1.2) =
      sixVertexSectorTopEigenvalue N (m + m) (by omega) c₁ := by
  let g : SixVertexBetheContinuationSpace a b N (m + m) → Real :=
    sixVertexContinuationWeightedFiniteDensityGauge ha N (m + m) rho
  let C : Set (SixVertexBetheContinuationSpace a b N (m + m)) :=
    {z | g z < outer}
  have hg : Continuous g :=
    continuous_sixVertexContinuationWeightedFiniteDensityGauge ha N (m + m) rho
  have hgap : ∀ z, ¬(inner < g z ∧ g z < outer) := by
    intro z
    have hgap' :=
      sixVertexContinuationWeightedFiniteDensityGauge_solutionFreeAnnulus_fixedCharge
        ha hN (n := m + m - 1) (q := m + m) (r := charge) (by omega)
          (by omega) rho hrhoEq hrhoMass hrhoLower hrho houter hinner
    simpa only [g] using hgap' z
  have hcover : 2 * (m + m) ≤ N := by omega
  have hcount : m + m ≤ N := by omega
  have hjac : ∀ z, g z < outer → Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m z.1.1
        (sixVertexEvenPositiveHalfProjection m z.1.2)) := by
    intro z hzg
    exact sixVertexContinuationWeightedFiniteDensityGauge_jacobianInjective
      ha hm hN hcover hcount rho hrhoLower hrho houter hmargin z hzg
  have hCopen : IsOpen C := isOpen_lt hg continuous_const
  have hCeq : C = {z | g z ≤ inner} :=
    sixVertex_stabilityGauge_lt_eq_le g hio hgap
  have hCcompact : IsCompact C := by
    rw [hCeq]
    letI : CompactSpace (SixVertexBetheContinuationSpace a b N (m + m)) :=
      isCompact_iff_compactSpace.mp (isCompact_sixVertexBetheContinuationSet ha hN)
    exact (isClosed_le hg continuous_const).isCompact
  let zC₀ : C := ⟨z₀, hz₀g⟩
  let zC₁ : C := ⟨z₁, hz₁g⟩
  have hzC₀ : sixVertexBetheContinuationProjectionOn C zC₀ = ⟨c₀, hc₀⟩ := by
    simpa [zC₀, sixVertexBetheContinuationProjectionOn] using hz₀
  have hzC₁ : sixVertexBetheContinuationProjectionOn C zC₁ = ⟨c₁, hc₁⟩ := by
    simpa [zC₁, sixVertexBetheContinuationProjectionOn] using hz₁
  have hlocal : IsLocalHomeomorph
      (sixVertexBetheContinuationProjectionOn C) :=
    isLocalHomeomorph_sixVertexBetheContinuationProjectionOn_of_evenSymmetricJacobian
      ha hN hcover C hCopen (fun z hz ↦ hjac z hz)
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hCcompact
  have hproj : Continuous (sixVertexBetheContinuationProjectionOn C) :=
    continuous_sixVertexBetheContinuationProjectionOn C
  have hcovOn : IsCoveringMapOn
      (sixVertexBetheContinuationProjectionOn C) Set.univ :=
    IsCoveringMapOn.of_openPartialHomeomorph hproj
      (fun e _ ↦ by
        obtain ⟨phi, he, hphi⟩ := hlocal e
        exact ⟨phi, he, hphi.symm⟩)
  have hcov : IsCoveringMap (sixVertexBetheContinuationProjectionOn C) :=
    isCoveringMap_iff_isCoveringMapOn_univ.mpr hcovOn
  have hfiber : ∀ z : C,
      sixVertexBetheContinuationProjectionOn C z = ⟨c₀, hc₀⟩ → z = zC₀ := by
    intro z hz
    have hparam : z.1.1.1 = c₀ := by
      have h := congrArg Subtype.val hz
      simpa [sixVertexBetheContinuationProjectionOn,
        sixVertexBetheContinuationProjection] using h
    have hzsol : SixVertexSatisfiesBetheEquations c₀ N (m + m) z.1.1.2 := by
      have h := (sixVertexBetheUpdate_eq_self_iff hN z.1.1.2).mp z.1.2.2.2
      simpa [hparam] using h
    have hz₀sol : SixVertexSatisfiesBetheEquations c₀ N (m + m) z₀.1.2 := by
      have h := (sixVertexBetheUpdate_eq_self_iff hN z₀.1.2).mp z₀.2.2.2
      have hparam₀ : z₀.1.1 = c₀ := by
        have hp := congrArg Subtype.val hz₀
        simpa [sixVertexBetheContinuationProjection] using hp
      simpa [hparam₀] using h
    have hroots : z.1.1.2 = z₀.1.2 :=
      sixVertexBetheSolution_unique_of_anisotropyMagnitude
        (ha.trans_le hc₀.1) (by omega) htail hzsol hz₀sol
    have hparam₀ : z₀.1.1 = c₀ := by
      have hp := congrArg Subtype.val hz₀
      simpa [sixVertexBetheContinuationProjection] using hp
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (hparam.trans hparam₀.symm) hroots
  have hinj : Function.Injective (sixVertexBetheContinuationProjectionOn C) :=
    coveringMap_injective_of_unique_fiber_Icc hab _ hcov ⟨c₀, hc₀⟩ zC₀
      hzC₀ hfiber
  obtain ⟨roots, hroots₀, hrootsMem⟩ :=
    exists_sixVertexContinuousBetheBranch_of_compactComponent_mem
      hab hc₀ C hCcompact hlocal zC₀ hzC₀
  have hrootsData : ∀ t ∈ Set.Icc a b,
      SixVertexOpenRootSimplex (roots t) ∧
      SixVertexSatisfiesBetheEquations t N (m + m) (roots t) := by
    intro t ht
    obtain ⟨z, hzC', hzt, hzroots⟩ := hrootsMem t ht
    have hzopen : SixVertexOpenRootSimplex z.1.2 :=
      sixVertexBetheContinuationSet_subset_open ha hcover z.2
    have hzsol : SixVertexSatisfiesBetheEquations z.1.1 N (m + m) z.1.2 :=
      (sixVertexBetheUpdate_eq_self_iff hN z.1.2).mp z.2.2.2
    constructor
    · simpa [← hzroots] using hzopen
    · simpa [hzt, hzroots] using hzsol
  have hrootsJac : ∀ t ∈ Set.Ioo a b, Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m t
        (sixVertexEvenPositiveHalfProjection m (roots t))) := by
    intro t ht
    obtain ⟨z, hzC', hzt, hzroots⟩ := hrootsMem t ⟨ht.1.le, ht.2.le⟩
    simpa [hzt, hzroots] using hjac z hzC'
  have hrootsAnalytic : AnalyticOnNhd Real roots (Set.Ioo a b) :=
    analyticOnNhd_sixVertexContinuousEvenSymmetricBetheBranch ha roots
      (fun t ht ↦ (hrootsData t ⟨ht.1.le, ht.2.le⟩).1)
      (fun t ht ↦ (hrootsData t ⟨ht.1.le, ht.2.le⟩).2) hrootsJac
  have hrootsTarget : roots c₁ = z₁.1.2 := by
    obtain ⟨z, hzC', hzt, hzroots⟩ := hrootsMem c₁ hc₁
    let zC : C := ⟨z, hzC'⟩
    have hzproj : sixVertexBetheContinuationProjectionOn C zC = ⟨c₁, hc₁⟩ := by
      apply Subtype.ext
      exact hzt
    have hzeq : zC = zC₁ := hinj (hzproj.trans hzC₁.symm)
    simpa [zC, zC₁, ← hzroots] using
      congrArg (fun w : C ↦ w.1.1.2) hzeq
  have hrootsBase : roots c₀ = z₀.1.2 := hroots₀
  have hperron := sixVertexAnalyticEvenSymmetricBetheCandidate_eqOn_top
    (N := N) (m := m) hm (by omega) isPreconnected_Ioo isOpen_Ioo
    (fun t ht ↦ by change 2 < t; linarith [ht.1]) roots
    (fun t ht ↦ (hrootsData t ⟨ht.1.le, ht.2.le⟩).1)
    (fun t ht ↦ (hrootsData t ⟨ht.1.le, ht.2.le⟩).2)
    hrootsAnalytic hc₀int (by simpa [hrootsBase] using hwave) (by
      simpa [hrootsBase] using hbase)
  simpa [hrootsTarget] using hperron hc₁int

end

end StatMech.FrontierD
