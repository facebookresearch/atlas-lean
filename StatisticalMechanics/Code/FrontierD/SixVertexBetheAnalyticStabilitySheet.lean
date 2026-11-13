/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate
import Code.FrontierD.SixVertexBetheCharacteristicRoot











open Filter Topology

namespace StatMech.FrontierD

noncomputable section


theorem exists_sixVertexContinuousBetheBranch_of_compactComponent_mem
    {a b c₀ : Real} (hab : a ≤ b) (hc₀ : c₀ ∈ Set.Icc a b)
    {N n : Nat}
    (C : Set (SixVertexBetheContinuationSpace a b N n))
    (hcompact : IsCompact C)
    (hlocal : IsLocalHomeomorph
      (sixVertexBetheContinuationProjectionOn C))
    (z₀ : C)
    (hz₀ : sixVertexBetheContinuationProjectionOn C z₀ = ⟨c₀, hc₀⟩) :
    ∃ roots : C(Real, Fin n → Real),
      roots c₀ = z₀.1.1.2 ∧
      ∀ t ∈ Set.Icc a b, ∃ z : SixVertexBetheContinuationSpace a b N n,
        z ∈ C ∧ z.1.1 = t ∧ z.1.2 = roots t := by
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hcompact
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
  let clamp : Real → Set.Icc a b := fun t =>
    ⟨min b (max a t),
      ⟨le_min hab (le_max_left _ _), min_le_left _ _⟩⟩
  have hclamp : Continuous clamp :=
    Continuous.subtype_mk (by fun_prop) _
  let f : C(Real, Set.Icc a b) := ⟨clamp, hclamp⟩
  have hf₀ : f c₀ = sixVertexBetheContinuationProjectionOn C z₀ := by
    rw [hz₀]
    apply Subtype.ext
    simp [f, clamp, max_eq_right hc₀.1, min_eq_right hc₀.2]
  letI : ContractibleSpace Real :=
    (contractible_iff_id_nullhomotopic Real).mpr
      ⟨0, ⟨ContinuousMap.Homotopy.affine
        (ContinuousMap.id Real) (ContinuousMap.const Real 0)⟩⟩
  obtain ⟨F, hF₀, hFlift⟩ :=
    (hcov.existsUnique_continuousMap_lifts f c₀ z₀ hf₀.symm).exists
  let roots : C(Real, Fin n → Real) :=
    ⟨fun t => (F t).1.1.2,
      continuous_subtype_val.snd.comp
        (continuous_subtype_val.comp F.continuous)⟩
  refine ⟨roots, ?_, ?_⟩
  · change (F c₀).1.1.2 = z₀.1.1.2
    rw [hF₀]
  · intro t ht
    have hprojF := congrFun hFlift t
    have hclamp_t : f t = ⟨t, ht⟩ := by
      apply Subtype.ext
      simp [f, clamp, max_eq_right ht.1, min_eq_right ht.2]
    have hfirst : (F t).1.1.1 = t := by
      have h := congrArg Subtype.val hprojF
      simpa [hclamp_t, sixVertexBetheContinuationProjectionOn,
        sixVertexBetheContinuationProjection] using h
    exact ⟨(F t).1, (F t).2, hfirst, rfl⟩



theorem analyticOnNhd_sixVertexContinuousEvenSymmetricBetheBranch
    {a b : Real} (ha : 2 < a) {N m : Nat}
    (roots : C(Real, Fin (m + m) → Real))
    (hopen : ∀ t ∈ Set.Ioo a b, SixVertexOpenRootSimplex (roots t))
    (hsol : ∀ t ∈ Set.Ioo a b,
      SixVertexSatisfiesBetheEquations t N (m + m) (roots t))
    (hjac : ∀ t ∈ Set.Ioo a b, Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m t
        (sixVertexEvenPositiveHalfProjection m (roots t)))) :
    AnalyticOnNhd Real roots (Set.Ioo a b) := by
  intro t ht
  let q : Fin m → Real := sixVertexEvenPositiveHalfProjection m (roots t)
  have htc : 2 < t := ha.trans ht.1
  have hlift : sixVertexEvenSymmetricLift m q = roots t :=
    sixVertexEvenSymmetricLift_projection m (hopen t ht).2.1
  have hqsol : SixVertexSatisfiesBetheEquations t N (m + m)
      (sixVertexEvenSymmetricLift m q) := by
    rw [hlift]
    exact hsol t ht
  obtain ⟨B⟩ := exists_sixVertexLocalAnalyticEvenSymmetricBetheBranch
    htc hqsol (hjac t ht)
  let qroots : Real → Fin m → Real := fun s =>
    sixVertexEvenPositiveHalfProjection m (roots s)
  have hqcont : Continuous qroots :=
    (sixVertexEvenPositiveHalfProjection m).continuous.comp roots.continuous
  have hgraph : Tendsto (fun s => (s, qroots s))
      (nhds t) (nhds (t, q)) := by
    exact continuousAt_id.prodMk hqcont.continuousAt
  have hunique : ∀ᶠ s in nhds t,
      SixVertexSatisfiesBetheEquations s N (m + m)
          (sixVertexEvenSymmetricLift m (qroots s)) →
        B.roots s = qroots s :=
    hgraph.eventually B.eventually_unique
  have hIoo : ∀ᶠ s in nhds t, s ∈ Set.Ioo a b :=
    isOpen_Ioo.mem_nhds ht
  have heqQ : B.roots =ᶠ[nhds t] qroots := by
    filter_upwards [hunique, hIoo] with s hsu hs
    have hliftS : sixVertexEvenSymmetricLift m (qroots s) = roots s :=
      sixVertexEvenSymmetricLift_projection m (hopen s hs).2.1
    apply hsu
    rw [hliftS]
    exact hsol s hs
  have hqanalytic : AnalyticAt Real qroots t :=
    B.analyticAt_roots.congr heqQ
  have hfullanalytic : AnalyticAt Real
      (fun s => sixVertexEvenSymmetricLift m (qroots s)) t :=
    ((sixVertexEvenSymmetricLift m).analyticAt (qroots t)).comp hqanalytic
  apply hfullanalytic.congr
  filter_upwards [hIoo] with s hs
  exact sixVertexEvenSymmetricLift_projection m (hopen s hs).2.1



theorem exists_sixVertexAnalyticEvenSymmetricBetheBranch_of_stabilityGauge
    {a b c₀ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Icc a b) {N m : Nat} (hN : 0 < N)
    (hhalf : 2 * (m + m) ≤ N)
    (g : SixVertexBetheContinuationSpace a b N (m + m) → Real)
    (hg : Continuous g) {inner outer : Real} (hio : inner < outer)
    (hgap : ∀ z, ¬(inner < g z ∧ g z < outer))
    (hjac : ∀ z, g z < outer → Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m z.1.1
        (sixVertexEvenPositiveHalfProjection m z.1.2)))
    (z₀ : SixVertexBetheContinuationSpace a b N (m + m))
    (hz₀g : g z₀ < outer)
    (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
    ∃ roots : C(Real, Fin (m + m) → Real),
      roots c₀ = z₀.1.2 ∧
      (∀ t ∈ Set.Icc a b,
        SixVertexOpenRootSimplex (roots t) ∧
        SixVertexSatisfiesBetheEquations t N (m + m) (roots t)) ∧
      AnalyticOnNhd Real roots (Set.Ioo a b) ∧
      ∀ t (ht : t ∈ Set.Icc a b),
        ∃ z : SixVertexBetheContinuationSpace a b N (m + m),
          g z ≤ inner ∧ z.1.1 = t ∧ z.1.2 = roots t := by
  let C : Set (SixVertexBetheContinuationSpace a b N (m + m)) :=
    {z | g z < outer}
  have hCopen : IsOpen C := isOpen_lt hg continuous_const
  have hCeq : C = {z | g z ≤ inner} :=
    sixVertex_stabilityGauge_lt_eq_le g hio hgap
  have hCcompact : IsCompact C := by
    rw [hCeq]
    letI : CompactSpace (SixVertexBetheContinuationSpace a b N (m + m)) :=
      isCompact_iff_compactSpace.mp
        (isCompact_sixVertexBetheContinuationSet ha hN)
    exact (isClosed_le hg continuous_const).isCompact
  let zC : C := ⟨z₀, hz₀g⟩
  have hzC : sixVertexBetheContinuationProjectionOn C zC = ⟨c₀, hc₀⟩ := by
    simpa [zC, sixVertexBetheContinuationProjectionOn] using hz₀
  have hlocal : IsLocalHomeomorph
      (sixVertexBetheContinuationProjectionOn C) :=
    isLocalHomeomorph_sixVertexBetheContinuationProjectionOn_of_evenSymmetricJacobian
      ha hN hhalf C hCopen (fun z hz => hjac z hz)
  obtain ⟨roots, hroots₀, hrootsMem⟩ :=
    exists_sixVertexContinuousBetheBranch_of_compactComponent_mem
      hab hc₀ C hCcompact hlocal zC hzC
  have hrootsData : ∀ t ∈ Set.Icc a b,
      SixVertexOpenRootSimplex (roots t) ∧
      SixVertexSatisfiesBetheEquations t N (m + m) (roots t) := by
    intro t ht
    obtain ⟨z, hzC', hzt, hzroots⟩ := hrootsMem t ht
    have hzopen : SixVertexOpenRootSimplex z.1.2 :=
      sixVertexBetheContinuationSet_subset_open ha hhalf z.2
    have hzsol : SixVertexSatisfiesBetheEquations z.1.1 N (m + m) z.1.2 :=
      (sixVertexBetheUpdate_eq_self_iff hN z.1.2).mp z.2.2.2
    constructor
    · simpa [← hzroots] using hzopen
    · simpa [hzt, hzroots] using hzsol
  have hrootsJac : ∀ t ∈ Set.Ioo a b, Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m t
        (sixVertexEvenPositiveHalfProjection m (roots t))) := by
    intro t ht
    have htIcc : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2.le⟩
    obtain ⟨z, hzC', hzt, hzroots⟩ := hrootsMem t htIcc
    have hzjac := hjac z hzC'
    simpa [hzt, hzroots] using hzjac
  have hrootsAnalytic := analyticOnNhd_sixVertexContinuousEvenSymmetricBetheBranch
    ha roots
      (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).1)
      (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).2)
      hrootsJac
  refine ⟨roots, hroots₀, hrootsData, hrootsAnalytic, ?_⟩
  intro t ht
  obtain ⟨z, hzC', hzt, hzroots⟩ := hrootsMem t ht
  have hzg : g z ≤ inner := by
    have hzInner : z ∈ {z | g z ≤ inner} := by
      rw [← hCeq]
      exact hzC'
    exact hzInner
  exact ⟨z, hzg, hzt, hzroots⟩



theorem exists_sixVertexAnalyticEvenSymmetricBetheBranch_of_densityGauge
    {a b c₀ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Icc a b) {N m : Nat} (hm : 0 < m) (hN : 0 < N)
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
          sixVertexFiniteDensityContinuumErrorOfLower
            t.1 N (rhoLower / 2) ≤ inner)
    (hmargin : ∀ t : Set.Icc a b,
      sixVertexSymmetricScatteringBoundaryBound t.1 +
        2 * sixVertexSymmetricJacobianTotalErrorOfLower
          t.1 N (rhoLower / 2) < 2 * Real.pi)
    (z₀ : SixVertexBetheContinuationSpace a b N (m + m))
    (hz₀g : sixVertexContinuationWeightedFiniteDensityGauge
      ha N (m + m) rho z₀ < outer)
    (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
    ∃ roots : C(Real, Fin (m + m) → Real),
      roots c₀ = z₀.1.2 ∧
      (∀ t ∈ Set.Icc a b,
        SixVertexOpenRootSimplex (roots t) ∧
        SixVertexSatisfiesBetheEquations t N (m + m) (roots t)) ∧
      AnalyticOnNhd Real roots (Set.Ioo a b) ∧
      ∀ t (ht : t ∈ Set.Icc a b),
        ∃ z : SixVertexBetheContinuationSpace a b N (m + m),
          sixVertexContinuationWeightedFiniteDensityGauge
            ha N (m + m) rho z ≤ inner ∧
          z.1.1 = t ∧ z.1.2 = roots t := by
  let g : SixVertexBetheContinuationSpace a b N (m + m) → Real :=
    sixVertexContinuationWeightedFiniteDensityGauge ha N (m + m) rho
  have hg : Continuous g :=
    continuous_sixVertexContinuationWeightedFiniteDensityGauge
      ha N (m + m) rho
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
  exact exists_sixVertexAnalyticEvenSymmetricBetheBranch_of_stabilityGauge
    ha hab hc₀ hN hcover g hg hio hgap hjac z₀ hz₀g hz₀

end

end StatMech.FrontierD
