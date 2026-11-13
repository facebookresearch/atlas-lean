/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheAnalyticStabilitySheet
import Code.FrontierD.SixVertexBetheVandermonde









open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section



theorem continuous_sixVertexCoordinateBetheWave_branch
    {N n : Nat} (p : Real → Fin n → Real) (hp : Continuous p) :
    Continuous (fun c => sixVertexCoordinateBetheWave (N := N) c (p c)) := by
  rw [continuous_pi_iff]
  intro x
  unfold sixVertexCoordinateBetheWave sixVertexBetheAmplitude
    sixVertexBethePairProduct sixVertexBetheMonomial
    sixVertexBethePairFactor sixVertexBethePhase sixVertexDelta
  fun_prop



theorem sixVertexBetheEigenvalueCandidate_evenSymmetricLift
    {m : Nat} (c : Real) (q : Fin m → Real) :
    sixVertexBetheEigenvalueCandidate c (sixVertexEvenSymmetricLift m q) =
      sixVertexSymmetricBetheEigenvalueCandidate c q := by
  unfold sixVertexBetheEigenvalueCandidate
    sixVertexSymmetricBetheEigenvalueCandidate
  have hprod (f : Real → Complex) :
      (∏ i, f (sixVertexEvenSymmetricLift m q i)) =
        (∏ j, f (q j)) * ∏ j, f (-q j) := by
    rw [Fin.prod_univ_add]
    simp_rw [sixVertexEvenSymmetricLift_castAdd,
      sixVertexEvenSymmetricLift_natAdd]
    have hrev : (∏ x : Fin m, f (-q x.rev)) = ∏ x, f (-q x) := by
      simpa using (Equiv.prod_comp Fin.revPerm (fun x => f (-q x)))
    rw [hrev, mul_comm]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rw [hprod (fun r => sixVertexBetheL c (sixVertexBethePhase r)),
    hprod (fun r => sixVertexBetheM c (sixVertexBethePhase r))]


theorem sixVertexBetheEigenvalueCandidate_evenSymmetricLift_eq_value
    {m : Nat} (c : Real) (q : Fin m → Real) :
    sixVertexBetheEigenvalueCandidate c (sixVertexEvenSymmetricLift m q) =
      (sixVertexSymmetricBetheEigenvalueValue c q : Complex) := by
  rw [sixVertexBetheEigenvalueCandidate_evenSymmetricLift,
    sixVertexSymmetricBetheEigenvalueCandidate_eq_value]


def sixVertexSymmetricBetheEigenvalueKernel
    {m : Nat} (c : Real) (q : Fin m → Real) : Real :=
  2 * ∏ j,
    (((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos (q j)) /
      (2 - 2 * Real.cos (q j)))

theorem sixVertexSymmetricBetheEigenvalueKernel_eq_value
    {m : Nat} (c : Real) (q : Fin m → Real)
    (hq : ∀ j, q j ∈ Set.Ioo 0 Real.pi) :
    sixVertexSymmetricBetheEigenvalueKernel c q =
      sixVertexSymmetricBetheEigenvalueValue c q := by
  unfold sixVertexSymmetricBetheEigenvalueKernel
    sixVertexSymmetricBetheEigenvalueValue
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [← Complex.normSq_eq_norm_sq]
  exact (sixVertexBetheM_phase_normSq c (q j)
    (sixVertexBethePhase_ne_one_of_mem_Ioo
      ⟨(neg_lt_zero.mpr Real.pi_pos).trans (hq j).1, (hq j).2⟩
      (ne_of_gt (hq j).1))).symm



theorem analyticOnNhd_sixVertexSymmetricBetheEigenvalueKernel
    {m : Nat} {U : Set Real} (q : Real → Fin m → Real)
    (hqAnalytic : AnalyticOnNhd Real q U)
    (hq : ∀ c ∈ U, ∀ j, q c j ∈ Set.Ioo 0 Real.pi) :
    AnalyticOnNhd Real
      (fun c => sixVertexSymmetricBetheEigenvalueKernel c (q c)) U := by
  intro c hc
  have hcoord (j : Fin m) : AnalyticAt Real (fun t => q t j) c :=
    by
      simpa only [Function.comp_apply] using
        ((ContinuousLinearMap.proj (R := Real) j).analyticAt (q c)).comp
          (hqAnalytic c hc)
  have hden (j : Fin m) : 2 - 2 * Real.cos (q c j) ≠ 0 := by
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi
      (show (0 : Real) ≤ 0 by rfl) (hq c hc j).2.le (hq c hc j).1
    rw [Real.cos_zero] at hcos
    nlinarith
  unfold sixVertexSymmetricBetheEigenvalueKernel
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_prod Finset.univ
  intro j _
  apply AnalyticAt.div
  · fun_prop
  · fun_prop
  · exact hden j

theorem sixVertexEvenSymmetricLift_positive_mem_Ioo
    {m : Nat} {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (j : Fin m) : q j ∈ Set.Ioo 0 Real.pi := by
  have hnonneg := (sixVertexEvenSymmetricLift_positive_mem_Icc hopen j).1
  have hpos : 0 < q j := hnonneg.lt_of_ne (fun h => by
    let i : Fin (m + m) := Fin.natAdd m j
    let ir : Fin (m + m) := Fin.castAdd m j.rev
    have hi : sixVertexEvenSymmetricLift m q i = 0 := by
      change sixVertexEvenSymmetricLift m q (Fin.natAdd m j) = 0
      rw [sixVertexEvenSymmetricLift_natAdd]
      exact h.symm
    have hir : sixVertexEvenSymmetricLift m q ir = 0 := by
      change sixVertexEvenSymmetricLift m q (Fin.castAdd m j.rev) = 0
      rw [sixVertexEvenSymmetricLift_castAdd]
      simp only [Fin.rev_rev]
      linarith
    have hieq : i = ir := hopen.1.injective (hi.trans hir.symm)
    have hval := congrArg Fin.val hieq
    simp [i, ir, Fin.castAdd, Fin.rev] at hval
    omega)
  have hpi := (hopen.2.2 (Fin.natAdd m j)).2
  rw [sixVertexEvenSymmetricLift_natAdd] at hpi
  exact ⟨hpos, hpi⟩

theorem sixVertexEvenSymmetricLift_ne_zero
    {m : Nat} {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (i : Fin (m + m)) : sixVertexEvenSymmetricLift m q i ≠ 0 := by
  intro hi
  have hir : sixVertexEvenSymmetricLift m q i.rev = 0 := by
    have hs := hopen.2.1 i
    rw [hi, neg_zero] at hs
    exact hs
  have hieq : i = i.rev := hopen.1.injective (hi.trans hir.symm)
  have hval := congrArg Fin.val hieq
  simp [Fin.rev] at hval
  omega




theorem sixVertexAnalyticEvenSymmetricBetheCandidate_eqOn_top
    {N m : Nat} (hm : 0 < m) (hn : m + m ≤ N)
    {U : Set Real} (hU : IsPreconnected U) (hUopen : IsOpen U)
    (hUtwo : U ⊆ Set.Ioi 2)
    (roots : C(Real, Fin (m + m) → Real))
    (hopen : ∀ t ∈ U, SixVertexOpenRootSimplex (roots t))
    (hsol : ∀ t ∈ U,
      SixVertexSatisfiesBetheEquations t N (m + m) (roots t))
    (hrootAnalytic : AnalyticOnNhd Real roots U)
    {c₀ : Real} (hc₀U : c₀ ∈ U)
    (hwave : sixVertexCoordinateBetheWave (N := N) c₀ (roots c₀) ≠ 0)
    (hbase : sixVertexSymmetricBetheEigenvalueKernel c₀
        (sixVertexEvenPositiveHalfProjection m (roots c₀)) =
      sixVertexSectorTopEigenvalue N (m + m) hn c₀) :
    Set.EqOn
      (fun t => sixVertexSymmetricBetheEigenvalueKernel t
        (sixVertexEvenPositiveHalfProjection m (roots t)))
      (sixVertexSectorTopEigenvalue N (m + m) hn) U := by
  let q : Real → Fin m → Real := fun t =>
    sixVertexEvenPositiveHalfProjection m (roots t)
  let f : Real → Real := fun t =>
    sixVertexSymmetricBetheEigenvalueKernel t (q t)
  have hqAnalytic : AnalyticOnNhd Real q U := by
    intro t ht
    simpa only [q, Function.comp_apply] using
      ((sixVertexEvenPositiveHalfProjection m).analyticAt (roots t)).comp
        (hrootAnalytic t ht)
  have hqpos : ∀ t ∈ U, ∀ j, q t j ∈ Set.Ioo 0 Real.pi := by
    intro t ht j
    have hlift : sixVertexEvenSymmetricLift m (q t) = roots t :=
      sixVertexEvenSymmetricLift_projection m (hopen t ht).2.1
    apply sixVertexEvenSymmetricLift_positive_mem_Ioo
    rw [hlift]
    exact hopen t ht
  have hfAnalytic : AnalyticOnNhd Real f U := by
    exact analyticOnNhd_sixVertexSymmetricBetheEigenvalueKernel
      q hqAnalytic hqpos
  have heigen : ∀ t ∈ U,
      SixVertexCoordinateBetheEigenrelation (N := N) t (roots t) := by
    intro t ht
    have hphase : ∀ i, sixVertexBethePhase (roots t i) ≠ 1 := by
      intro i
      let qt := q t
      have hlift : sixVertexEvenSymmetricLift m qt = roots t :=
        sixVertexEvenSymmetricLift_projection m (hopen t ht).2.1
      apply sixVertexBethePhase_ne_one_of_mem_Ioo ((hopen t ht).2.2 i)
      rw [← hlift]
      exact sixVertexEvenSymmetricLift_ne_zero (by rw [hlift]; exact hopen t ht) i
    exact (hsol t ht).multiplicative
      |>.physicalCoordinateBetheEigenrelation_of_pos
        (hUtwo ht) (by omega) (roots t) hphase
  have hcandidate : ∀ t ∈ U,
      sixVertexBetheEigenvalueCandidate t (roots t) = (f t : Complex) := by
    intro t ht
    have hlift : sixVertexEvenSymmetricLift m (q t) = roots t :=
      sixVertexEvenSymmetricLift_projection m (hopen t ht).2.1
    rw [← hlift,
      sixVertexBetheEigenvalueCandidate_evenSymmetricLift_eq_value]
    exact_mod_cast (sixVertexSymmetricBetheEigenvalueKernel_eq_value
      t (q t) (hqpos t ht)).symm
  have hwaveContinuous : ContinuousAt
      (fun t => sixVertexCoordinateBetheWave (N := N) t (roots t)) c₀ :=
    (continuous_sixVertexCoordinateBetheWave_branch roots roots.continuous).continuousAt
  have hUzero : U ⊆ Set.Ioi 0 := by
    intro t ht
    have httwo := hUtwo ht
    change 2 < t at httwo
    change 0 < t
    linarith
  have hc₀pos : 0 < c₀ := hUzero hc₀U
  apply sixVertexBetheCandidate_eqOn_top_of_analyticSheet_of_nonzero_at
    hn hU hUopen hUzero hc₀U hc₀pos roots f hfAnalytic heigen hcandidate
      hwaveContinuous hwave
  exact hbase



theorem eventually_sixVertexHalfFilledBetheCandidate_eq_top_and_wave_ne_zero
    (k : Nat) :
    ∀ᶠ c : Real in atTop, ∀ hc : 2 < c,
      sixVertexSymmetricBetheEigenvalueValue c
          (sixVertexPositiveHalfBetheRoots hc k) =
        sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1)) (by
            unfold sixVertexFourWidth
            omega) c ∧
      sixVertexCoordinateBetheWave (N := sixVertexFourWidth 0 k) c
        (sixVertexHalfFilledBetheRoots hc k) ≠ 0 := by
  filter_upwards
    [eventually_sixVertexHalfFilledBetheCandidate_eq_top_vandermonde k,
      eventually_exists_sixVertexHalfFilledBetheRotatedRealWave_ne_zero k]
      with c hcandidate hrotated
  intro hc
  refine ⟨hcandidate hc, ?_⟩
  obtain ⟨a, ha⟩ := hrotated hc
  intro hwave
  apply ha
  funext x
  unfold sixVertexHalfFilledBetheRotatedRealWave
  rw [show sixVertexCoordinateBetheWave c
      (sixVertexHalfFilledBetheRoots hc k) x = 0 by
    exact congrFun hwave x]
  simp



def sixVertexHalfFilledBetheContinuationPoint
    {a b c₀ : Real} (ha : 2 < a) (hc₀ : c₀ ∈ Set.Icc a b) (k : Nat) :
    SixVertexBetheContinuationSpace a b (sixVertexFourWidth 0 k)
      ((k + 1) + (k + 1)) := by
  let hc : 2 < c₀ := ha.trans_le hc₀.1
  let p := sixVertexHalfFilledBetheRoots hc k
  have hopen : SixVertexOpenRootSimplex p :=
    sixVertexHalfFilledBetheRoots_mem_open hc k
  have hsol : SixVertexSatisfiesBetheEquations c₀
      (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) p :=
    sixVertexHalfFilledBetheRoots_is_solution hc k
  have hN : 0 < sixVertexFourWidth 0 k := sixVertexFourWidth_pos 0 k
  exact ⟨(c₀, p), hc₀, hopen.toClosed,
    (sixVertexBetheUpdate_eq_self_iff hN p).mpr hsol⟩

@[simp] theorem sixVertexHalfFilledBetheContinuationPoint_parameter
    {a b c₀ : Real} (ha : 2 < a) (hc₀ : c₀ ∈ Set.Icc a b) (k : Nat) :
    (sixVertexHalfFilledBetheContinuationPoint ha hc₀ k).1.1 = c₀ := rfl

theorem sixVertexHalfFilledBetheContinuationPoint_roots
    {a b c₀ : Real} (ha : 2 < a) (hc₀ : c₀ ∈ Set.Icc a b) (k : Nat) :
    (sixVertexHalfFilledBetheContinuationPoint ha hc₀ k).1.2 =
      sixVertexHalfFilledBetheRoots (ha.trans_le hc₀.1) k := by
  rfl

@[simp] theorem sixVertexHalfFilledBetheContinuationPoint_projection
    {a b c₀ : Real} (ha : 2 < a) (hc₀ : c₀ ∈ Set.Icc a b) (k : Nat) :
    sixVertexBetheContinuationProjection
      (sixVertexHalfFilledBetheContinuationPoint ha hc₀ k) = ⟨c₀, hc₀⟩ :=
  rfl




theorem exists_sixVertexHalfFilledPerronSheet_of_densityGauge
    {a b c₀ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Ioo a b) (k : Nat)
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
          sixVertexFiniteDensityContinuumErrorOfLower t.1
            (sixVertexFourWidth 0 k) (rhoLower / 2) ≤ inner)
    (hmargin : ∀ t : Set.Icc a b,
      sixVertexSymmetricScatteringBoundaryBound t.1 +
        2 * sixVertexSymmetricJacobianTotalErrorOfLower t.1
          (sixVertexFourWidth 0 k) (rhoLower / 2) < 2 * Real.pi)
    (hz₀g : sixVertexContinuationWeightedFiniteDensityGauge ha
      (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) rho
        (sixVertexHalfFilledBetheContinuationPoint ha
          ⟨hc₀.1.le, hc₀.2.le⟩ k) < outer)
    (hbase : sixVertexSymmetricBetheEigenvalueValue c₀
        (sixVertexPositiveHalfBetheRoots (ha.trans hc₀.1) k) =
      sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
        ((k + 1) + (k + 1)) (by
          unfold sixVertexFourWidth
          omega) c₀)
    (hwave : sixVertexCoordinateBetheWave (N := sixVertexFourWidth 0 k) c₀
      (sixVertexHalfFilledBetheRoots (ha.trans hc₀.1) k) ≠ 0) :
    ∃ roots : C(Real, Fin ((k + 1) + (k + 1)) → Real),
      roots c₀ = sixVertexHalfFilledBetheRoots (ha.trans hc₀.1) k ∧
      (∀ t ∈ Set.Icc a b,
        SixVertexOpenRootSimplex (roots t) ∧
        SixVertexSatisfiesBetheEquations t (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1)) (roots t)) ∧
      AnalyticOnNhd Real roots (Set.Ioo a b) ∧
      Set.EqOn
        (fun t => sixVertexSymmetricBetheEigenvalueKernel t
          (sixVertexEvenPositiveHalfProjection (k + 1) (roots t)))
        (sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1)) (by
            unfold sixVertexFourWidth
            omega))
        (Set.Ioo a b) ∧
      ∀ t (ht : t ∈ Set.Icc a b),
        ∃ z : SixVertexBetheContinuationSpace a b
            (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)),
          sixVertexContinuationWeightedFiniteDensityGauge ha
              (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) rho z ≤ inner ∧
            z.1.1 = t ∧ z.1.2 = roots t := by
  let hc₀Icc : c₀ ∈ Set.Icc a b := ⟨hc₀.1.le, hc₀.2.le⟩
  let z₀ := sixVertexHalfFilledBetheContinuationPoint ha hc₀Icc k
  have hN : 0 < sixVertexFourWidth 0 k := sixVertexFourWidth_pos 0 k
  have hhalf : sixVertexFourWidth 0 k =
      2 * ((k + 1) + (k + 1)) := by
    unfold sixVertexFourWidth
    omega
  obtain ⟨roots, hroots₀, hrootsData, hrootsAnalytic, hrootsGauge⟩ :=
    exists_sixVertexAnalyticEvenSymmetricBetheBranch_of_densityGauge
      ha hab hc₀Icc (by omega) hN hhalf rho hrhoEq hrhoMass
        hrhoLower hrho hio houter hinner hmargin z₀ hz₀g
        (sixVertexHalfFilledBetheContinuationPoint_projection ha hc₀Icc k)
  have hrootsSelected : roots c₀ =
      sixVertexHalfFilledBetheRoots (ha.trans hc₀.1) k := by
    rw [hroots₀]
    exact sixVertexHalfFilledBetheContinuationPoint_roots ha hc₀Icc k
  have hqbase : sixVertexEvenPositiveHalfProjection (k + 1) (roots c₀) =
      sixVertexPositiveHalfBetheRoots (ha.trans hc₀.1) k := by
    rw [hrootsSelected]
    rfl
  have hkernelBase : sixVertexSymmetricBetheEigenvalueKernel c₀
        (sixVertexEvenPositiveHalfProjection (k + 1) (roots c₀)) =
      sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
        ((k + 1) + (k + 1)) (by
          unfold sixVertexFourWidth
          omega) c₀ := by
    rw [hqbase, sixVertexSymmetricBetheEigenvalueKernel_eq_value]
    · exact hbase
    · intro j
      exact ⟨sixVertexPositiveHalfBetheRoots_pos (ha.trans hc₀.1) k j,
        sixVertexPositiveHalfBetheRoots_lt_pi (ha.trans hc₀.1) k j⟩
  have hwaveRoots : sixVertexCoordinateBetheWave
      (N := sixVertexFourWidth 0 k) c₀ (roots c₀) ≠ 0 := by
    rwa [hrootsSelected]
  have hperron := sixVertexAnalyticEvenSymmetricBetheCandidate_eqOn_top
    (N := sixVertexFourWidth 0 k) (m := k + 1) (by omega) (by
      unfold sixVertexFourWidth
      omega) isPreconnected_Ioo isOpen_Ioo
      (fun t ht => by change 2 < t; linarith [ht.1]) roots
      (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).1)
      (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).2)
      hrootsAnalytic hc₀ hwaveRoots hkernelBase
  exact ⟨roots, hrootsSelected, hrootsData, hrootsAnalytic, hperron, hrootsGauge⟩

end

end StatMech.FrontierD
