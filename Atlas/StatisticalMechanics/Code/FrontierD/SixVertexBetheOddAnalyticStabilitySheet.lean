/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOddSymmetricStability
import Code.FrontierD.SixVertexBetheAnalyticStabilitySheet
import Code.FrontierD.SixVertexBetheFixedChargeStability





open Filter Topology

namespace StatMech.FrontierD

noncomputable section

theorem analyticOnNhd_sixVertexContinuousOddSymmetricBetheBranch
    {a b : Real} (ha : 2 < a) {N m : Nat}
    (roots : C(Real, Fin ((m + 1) + m) → Real))
    (hopen : ∀ t ∈ Set.Ioo a b, SixVertexOpenRootSimplex (roots t))
    (hsol : ∀ t ∈ Set.Ioo a b,
      SixVertexSatisfiesBetheEquations t N ((m + 1) + m) (roots t))
    (hjac : ∀ t ∈ Set.Ioo a b, Function.Injective
      (sixVertexOddSymmetricBetheRootJacobian N m t
        (sixVertexOddPositiveHalfProjection m (roots t)))) :
    AnalyticOnNhd Real roots (Set.Ioo a b) := by
  intro t ht
  let q : Fin m → Real := sixVertexOddPositiveHalfProjection m (roots t)
  have htc : 2 < t := ha.trans ht.1
  have hlift : sixVertexOddSymmetricLift m q = roots t :=
    sixVertexOddSymmetricLift_projection m (hopen t ht).2.1
  have hqsol : SixVertexSatisfiesBetheEquations t N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q) := by
    rw [hlift]
    exact hsol t ht
  obtain ⟨B⟩ := exists_sixVertexLocalAnalyticOddSymmetricBetheBranch
    htc hqsol (hjac t ht)
  let qroots : Real → Fin m → Real := fun s =>
    sixVertexOddPositiveHalfProjection m (roots s)
  have hqcont : Continuous qroots :=
    (sixVertexOddPositiveHalfProjection m).continuous.comp roots.continuous
  have hgraph : Tendsto (fun s => (s, qroots s))
      (nhds t) (nhds (t, q)) := by
    exact continuousAt_id.prodMk hqcont.continuousAt
  have hunique : ∀ᶠ s in nhds t,
      SixVertexSatisfiesBetheEquations s N ((m + 1) + m)
          (sixVertexOddSymmetricLift m (qroots s)) →
        B.roots s = qroots s :=
    hgraph.eventually B.eventually_unique
  have hIoo : ∀ᶠ s in nhds t, s ∈ Set.Ioo a b :=
    isOpen_Ioo.mem_nhds ht
  have heqQ : B.roots =ᶠ[nhds t] qroots := by
    filter_upwards [hunique, hIoo] with s hsu hs
    have hliftS : sixVertexOddSymmetricLift m (qroots s) = roots s :=
      sixVertexOddSymmetricLift_projection m (hopen s hs).2.1
    apply hsu
    rw [hliftS]
    exact hsol s hs
  have hqanalytic : AnalyticAt Real qroots t :=
    B.analyticAt_roots.congr heqQ
  have hfullanalytic : AnalyticAt Real
      (fun s => sixVertexOddSymmetricLift m (qroots s)) t :=
    ((sixVertexOddSymmetricLift m).analyticAt (qroots t)).comp hqanalytic
  apply hfullanalytic.congr
  filter_upwards [hIoo] with s hs
  exact sixVertexOddSymmetricLift_projection m (hopen s hs).2.1

theorem exists_sixVertexAnalyticOddSymmetricBetheBranch_of_stabilityGauge
    {a b c₀ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Icc a b) {N m : Nat} (hm : 0 < m) (hN : 0 < N)
    (hhalf : 2 * ((m + 1) + m) ≤ N)
    (g : SixVertexBetheContinuationSpace a b N ((m + 1) + m) → Real)
    (hg : Continuous g) {inner outer : Real} (hio : inner < outer)
    (hgap : ∀ z, ¬(inner < g z ∧ g z < outer))
    (hjac : ∀ z, g z < outer → Function.Injective
      (sixVertexOddSymmetricBetheRootJacobian N m z.1.1
        (sixVertexOddPositiveHalfProjection m z.1.2)))
    (z₀ : SixVertexBetheContinuationSpace a b N ((m + 1) + m))
    (hz₀g : g z₀ < outer)
    (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
    ∃ roots : C(Real, Fin ((m + 1) + m) → Real),
      roots c₀ = z₀.1.2 ∧
      (∀ t ∈ Set.Icc a b,
        SixVertexOpenRootSimplex (roots t) ∧
        SixVertexSatisfiesBetheEquations t N ((m + 1) + m) (roots t)) ∧
      AnalyticOnNhd Real roots (Set.Ioo a b) ∧
      ∀ t (ht : t ∈ Set.Icc a b),
        ∃ z : SixVertexBetheContinuationSpace a b N ((m + 1) + m),
          g z ≤ inner ∧ z.1.1 = t ∧ z.1.2 = roots t := by
  let C : Set (SixVertexBetheContinuationSpace a b N ((m + 1) + m)) :=
    {z | g z < outer}
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
  let zC : C := ⟨z₀, hz₀g⟩
  have hzC : sixVertexBetheContinuationProjectionOn C zC = ⟨c₀, hc₀⟩ := by
    simpa [zC, sixVertexBetheContinuationProjectionOn] using hz₀
  have hlocal : IsLocalHomeomorph
      (sixVertexBetheContinuationProjectionOn C) :=
    isLocalHomeomorph_sixVertexBetheContinuationProjectionOn_of_oddSymmetricJacobian
      ha hN hhalf C hCopen (fun z hz => hjac z hz)
  obtain ⟨roots, hroots₀, hrootsMem⟩ :=
    exists_sixVertexContinuousBetheBranch_of_compactComponent_mem
      hab hc₀ C hCcompact hlocal zC hzC
  have hrootsData : ∀ t ∈ Set.Icc a b,
      SixVertexOpenRootSimplex (roots t) ∧
      SixVertexSatisfiesBetheEquations t N ((m + 1) + m) (roots t) := by
    intro t ht
    obtain ⟨z, hzC', hzt, hzroots⟩ := hrootsMem t ht
    have hzopen : SixVertexOpenRootSimplex z.1.2 :=
      sixVertexBetheContinuationSet_subset_open ha hhalf z.2
    have hzsol : SixVertexSatisfiesBetheEquations
        z.1.1 N ((m + 1) + m) z.1.2 :=
      (sixVertexBetheUpdate_eq_self_iff hN z.1.2).mp z.2.2.2
    exact ⟨by simpa [← hzroots] using hzopen,
      by simpa [hzt, hzroots] using hzsol⟩
  have hrootsJac : ∀ t ∈ Set.Ioo a b, Function.Injective
      (sixVertexOddSymmetricBetheRootJacobian N m t
        (sixVertexOddPositiveHalfProjection m (roots t))) := by
    intro t ht
    obtain ⟨z, hzC', hzt, hzroots⟩ :=
      hrootsMem t ⟨ht.1.le, ht.2.le⟩
    simpa [hzt, hzroots] using hjac z hzC'
  have hrootsAnalytic :=
    analyticOnNhd_sixVertexContinuousOddSymmetricBetheBranch ha roots
      (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).1)
      (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).2)
      hrootsJac
  refine ⟨roots, hroots₀, hrootsData, hrootsAnalytic, ?_⟩
  intro t ht
  obtain ⟨z, hzC', hzt, hzroots⟩ := hrootsMem t ht
  have hzg : g z ≤ inner := by
    have : z ∈ {z | g z ≤ inner} := by rw [← hCeq]; exact hzC'
    exact this
  exact ⟨z, hzg, hzt, hzroots⟩

theorem exists_sixVertexAnalyticOddSymmetricBetheBranch_of_fixedChargeDensityGauge
    {a b c₀ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Icc a b) {N m r : Nat} (hm : 0 < m) (hN : 0 < N)
    (hcharge : N = 2 * ((m + 1) + m) + 2 * r)
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
            t.1 N r (rhoLower / 2) ≤ inner)
    (hmargin : ∀ t : Set.Icc a b,
      sixVertexSymmetricScatteringBoundaryBound t.1 +
        2 * sixVertexSymmetricJacobianTotalErrorOfLower
          t.1 N (rhoLower / 2) < 2 * Real.pi)
    (z₀ : SixVertexBetheContinuationSpace a b N ((m + 1) + m))
    (hz₀g : sixVertexContinuationWeightedFiniteDensityGauge
      ha N ((m + 1) + m) rho z₀ < outer)
    (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
    ∃ roots : C(Real, Fin ((m + 1) + m) → Real),
      roots c₀ = z₀.1.2 ∧
      (∀ t ∈ Set.Icc a b,
        SixVertexOpenRootSimplex (roots t) ∧
        SixVertexSatisfiesBetheEquations t N ((m + 1) + m) (roots t)) ∧
      AnalyticOnNhd Real roots (Set.Ioo a b) ∧
      ∀ t (_ht : t ∈ Set.Icc a b),
        ∃ z : SixVertexBetheContinuationSpace a b N ((m + 1) + m),
          sixVertexContinuationWeightedFiniteDensityGauge
            ha N ((m + 1) + m) rho z ≤ inner ∧
          z.1.1 = t ∧ z.1.2 = roots t := by
  let g : SixVertexBetheContinuationSpace a b N ((m + 1) + m) → Real :=
    sixVertexContinuationWeightedFiniteDensityGauge ha N ((m + 1) + m) rho
  have hg : Continuous g :=
    continuous_sixVertexContinuationWeightedFiniteDensityGauge
      ha N ((m + 1) + m) rho
  have hgap : ∀ z, ¬(inner < g z ∧ g z < outer) := by
    intro z
    have hgap' :=
      sixVertexContinuationWeightedFiniteDensityGauge_solutionFreeAnnulus_fixedCharge
        ha hN (n := (m + 1) + m - 1) (q := (m + 1) + m) (r := r)
          (by omega) (by omega) rho hrhoEq hrhoMass hrhoLower hrho
          houter hinner
    simpa only [g] using hgap' z
  have hcover : 2 * ((m + 1) + m) ≤ N := by omega
  have hcount : (m + 1) + m ≤ N := by omega
  have hjac : ∀ z, g z < outer → Function.Injective
      (sixVertexOddSymmetricBetheRootJacobian N m z.1.1
        (sixVertexOddPositiveHalfProjection m z.1.2)) := by
    intro z hzg
    exact sixVertexContinuationWeightedFiniteDensityGauge_oddJacobianInjective
      ha hm hN hcover hcount rho hrhoLower hrho houter hmargin z hzg
  exact exists_sixVertexAnalyticOddSymmetricBetheBranch_of_stabilityGauge
    ha hab hc₀ hm hN hcover g hg hio hgap hjac z₀ hz₀g hz₀

end

end StatMech.FrontierD
