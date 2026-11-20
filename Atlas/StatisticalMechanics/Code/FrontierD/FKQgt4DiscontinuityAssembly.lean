/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKQgt4CorrelationReduction
import Code.FK.OrderTransition
import Code.FK.TwoPointPositiveFull
import Code.FK.FreeTailTriviality
import Code.FK.FKGeneralQClusterFKG
import Code.BeffaraDC.SelfDualValue










open MeasureTheory Filter Topology

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section



def fkQgt4DiagonalSite (n : Nat) : Site 2 :=
  fun _ => (n / 2 : Nat)


noncomputable def fkQgt4CriticalFreeDiagonalTwoPoint
    {q : Real} (hq : 4 < q) (n : Nat) : Real :=
  FK.infiniteTwoPointReal
    ((FK.freeInfiniteVolume 2
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2))))
    (origin 2) (fkQgt4DiagonalSite n)

theorem fkQgt4CriticalFreeDiagonalTwoPoint_nonneg
    {q : Real} (hq : 4 < q) (n : Nat) :
    0 <= fkQgt4CriticalFreeDiagonalTwoPoint hq n :=
  measureReal_nonneg

theorem fkQgt4CriticalFreeDiagonalTwoPoint_le_one
    {q : Real} (hq : 4 < q) (n : Nat) :
    fkQgt4CriticalFreeDiagonalTwoPoint hq n <= 1 :=
  measureReal_le_one



noncomputable def fkQgt4CriticalFreeDiagonalRate
    {q : Real} (hq : 4 < q) (n : Nat) : Real :=
  -Real.log (fkQgt4CriticalFreeDiagonalTwoPoint hq (n + 1)) /
    (n + 1 : Real)





theorem tendsto_zero_of_neg_log_div_tendsto_pos
    (f : Nat -> Real) (hf0 : forall n, 0 <= f n)
    {xi : Real} (hxi : 0 < xi)
    (hrate : Tendsto (fun n => -Real.log (f n) / (n + 1 : Real))
      atTop (nhds xi)) :
    Tendsto f atTop (nhds 0) := by
  let a : Real := xi / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hrateEventually : ∀ᶠ n in atTop,
      a < -Real.log (f n) / (n + 1 : Real) :=
    (tendsto_order.1 hrate).1 a (by dsimp [a]; linarith)
  let upper : Nat -> Real := fun n => Real.exp (-a) ^ (n + 1)
  have hexp0 : 0 <= Real.exp (-a) := (Real.exp_pos _).le
  have hexp1 : Real.exp (-a) < 1 := by
    rw [<- Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hupper : Tendsto upper atTop (nhds 0) := by
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one hexp0 hexp1).comp
      (tendsto_add_atTop_nat 1)
  refine squeeze_zero' (f := f) (g := upper)
    (Filter.Eventually.of_forall hf0) ?_ hupper
  filter_upwards [hrateEventually] with n hn
  by_cases hzero : f n = 0
  · rw [hzero]
    exact pow_nonneg hexp0 _
  · have hfpos : 0 < f n := lt_of_le_of_ne (hf0 n) (Ne.symm hzero)
    have hnpos : (0 : Real) < n + 1 := by positivity
    have hlog : Real.log (f n) < -a * (n + 1 : Real) := by
      rw [lt_div_iff₀ hnpos] at hn
      linarith
    have hexplt := Real.exp_lt_exp.mpr hlog
    rw [Real.exp_log hfpos] at hexplt
    calc
      f n <= Real.exp (-a * (n + 1 : Real)) := hexplt.le
      _ = upper n := by
        dsimp [upper]
        rw [<- Real.exp_nat_mul]
        congr 1
        push_cast
        ring



theorem fkQgt4CriticalFreeDiagonalTwoPoint_tendsto_zero_of_rate
    {q xi : Real} (hq : 4 < q) (hxi : 0 < xi)
    (hrate : Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds xi)) :
    Tendsto (fun n => fkQgt4CriticalFreeDiagonalTwoPoint hq (n + 1))
      atTop (nhds 0) := by
  exact tendsto_zero_of_neg_log_div_tendsto_pos
    (fun n => fkQgt4CriticalFreeDiagonalTwoPoint hq (n + 1))
    (fun n => fkQgt4CriticalFreeDiagonalTwoPoint_nonneg hq (n + 1))
    hxi hrate





theorem percolationProbability_eq_zero_of_twoPoint_tendsto_zero
    {d : Nat} (mu : Measure (ConfigSpace (Sym2 (Site d))))
    [IsFiniteMeasure mu]
    (hPA : forall x : Site d,
      mu.real (FK.clusterInfiniteEvent d (origin d)) *
          mu.real (FK.clusterInfiniteEvent d x) <=
        mu.real (FK.clusterInfiniteEvent d (origin d) ∩
          FK.clusterInfiniteEvent d x))
    (hTI : forall x : Site d,
      mu.real (FK.clusterInfiniteEvent d x) =
        mu.real (FK.clusterInfiniteEvent d (origin d)))
    (huniq : mu (atLeastTwoInfinite d) = 0)
    (x : Nat -> Site d)
    (hdecay : Tendsto (fun n => FK.infiniteTwoPointReal mu (origin d) (x n))
      atTop (nhds 0)) :
    mu.real (percolationEvent d) = 0 := by
  apply le_antisymm ?_ measureReal_nonneg
  by_contra hnot
  have htheta : 0 < mu.real (percolationEvent d) := lt_of_not_ge hnot
  obtain ⟨c, hc, hlower⟩ :=
    FK.infiniteTwoPoint_uniform_pos_of_fkg_unique mu hPA hTI huniq htheta
  have heventually : ∀ᶠ n in atTop,
      FK.infiniteTwoPointReal mu (origin d) (x n) < c :=
    (tendsto_order.1 hdecay).2 c hc
  obtain ⟨n, hn⟩ := heventually.exists
  exact (not_lt_of_ge (hlower (x n))) hn



theorem clusterInfiniteEvent_real_eq_origin_of_translationInvariant
    {d : Nat} (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (htrans : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site d)) mu)
    (x : Site d) :
    mu.real (FK.clusterInfiniteEvent d x) =
      mu.real (FK.clusterInfiniteEvent d (origin d)) := by
  let g : Multiplicative (Site d) := Multiplicative.ofAdd x
  have hgx : g • origin d = x := by
    show Multiplicative.toAdd g + (0 : Site d) = x
    simp [g]
  have hpre :
      (ConfigSpace.shift g : ConfigSpace (Sym2 (Site d)) →
        ConfigSpace (Sym2 (Site d))) ⁻¹' FK.clusterInfiniteEvent d x =
        FK.clusterInfiniteEvent d (origin d) := by
    ext omega
    change (cluster d (ConfigSpace.shift g omega) x).Infinite ↔
      (cluster d omega (origin d)).Infinite
    rw [← hgx, cluster_shift]
    exact Set.infinite_image_iff
      (Set.injOn_of_injective (smul_injective g))
  have hinv := htrans.measure_preimage g
    (FK.measurableSet_clusterInfiniteEvent x)
  unfold Measure.real
  rw [hpre] at hinv
  exact congrArg ENNReal.toReal hinv.symm




theorem oneInfiniteCluster_ae_of_theta_pos_of_zero_one
    {d : Nat} (mu : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure mu]
    (htheta : 0 < mu.real (percolationEvent d))
    (hzeroOne :
      mu {omega | numInfiniteClusters d omega = 0} = 1 ∨
      mu {omega | numInfiniteClusters d omega = 1} = 1) :
    mu {omega | numInfiniteClusters d omega = 1} = 1 := by
  rcases hzeroOne with hzero | hone
  · exfalso
    have hsubset : percolationEvent d ⊆
        {omega | numInfiniteClusters d omega = 0}ᶜ := by
      intro omega homega
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
      intro hnone
      have hinf : (cluster d omega (origin d)).Infinite := homega
      have hmem : cluster d omega (origin d) ∈ infiniteClusters d omega :=
        ⟨hinf, origin d, rfl⟩
      have hpos : 0 < (infiniteClusters d omega).encard :=
        Set.encard_pos.mpr ⟨_, hmem⟩
      have hne : numInfiniteClusters d omega ≠ 0 := by
        unfold numInfiniteClusters
        exact ne_of_gt hpos
      exact hne hnone
    have hcomp : mu ({omega | numInfiniteClusters d omega = 0}ᶜ) = 0 := by
      have hmeas : MeasurableSet {omega | numInfiniteClusters d omega = 0} :=
        measurable_numInfiniteClusters (measurableSet_singleton 0)
      rw [MeasureTheory.measure_compl hmeas (measure_ne_top mu _), hzero,
        measure_univ]
      simp
    have hperco : mu (percolationEvent d) = 0 :=
      nonpos_iff_eq_zero.mp ((measure_mono hsubset).trans (le_of_eq hcomp))
    have hreal : mu.real (percolationEvent d) = 0 := by
      rw [Measure.real, hperco]
      simp
    linarith
  · exact hone



structure FKQgt4TorusSixVertexWindingBridge (xiInv R : Real) : Prop where
  oneWinding : R <= xiInv
  fixedCharge : forall r : Nat, 2 <= r ->
    ((r - 1 : Nat) : Real) * xiInv <= (r : Real) * R

theorem FKQgt4TorusSixVertexWindingBridge.toBounds
    {xiInv R : Real} (h : FKQgt4TorusSixVertexWindingBridge xiInv R) :
    FKQgt4WindingSectorBounds xiInv R :=
  ⟨h.oneWinding, h.fixedCharge⟩



theorem fkQgt4_discontinuity_of_winding_and_order_inputs
    {q xiInv : Real} (hq : 4 < q) (hxi : 0 < xiInv)
    (hrate : Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds xiInv))
    (hWiredAlmostSure :
      let mu := ((FK.wiredInfiniteVolume 2
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
        (by linarith : (0 : Real) < q) :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
          Measure (ConfigSpace (Sym2 (Site 2))) )
      mu (percolationEvent 2) = 1)
    (hwind : FKQgt4TorusSixVertexWindingBridge xiInv
      (fkQgt4SixVertexGapRate q)) :
    FK.IsFirstOrderTransition 2
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
        (by linarith : (0 : Real) < q)
      ∧ FK.freeInfiniteVolume 2
          (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
          (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
          (by linarith : (0 : Real) < q) ≠
        FK.wiredInfiniteVolume 2
          (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
          (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
          (by linarith : (0 : Real) < q)
      ∧ Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop
        (nhds (fkQgt4SixVertexGapRate q))
      ∧ 0 < fkQgt4SixVertexGapRate q
      ∧ (((FK.wiredInfiniteVolume 2
          (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
          (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
          (by linarith : (0 : Real) < q) :
            ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
          Measure (ConfigSpace (Sym2 (Site 2))))
        (percolationEvent 2) = 1) := by
  let hp := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).1
  let hp1 := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).2
  let hq0 : (0 : Real) < q := by linarith
  have hq1 : (1 : Real) ≤ q := by linarith
  let mu0 : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2 hp hp1 hq0
  let mu1 : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.wiredInfiniteVolume 2 hp hp1 hq0
  have hdecay := fkQgt4CriticalFreeDiagonalTwoPoint_tendsto_zero_of_rate
    hq hxi hrate
  have hfreeTI : ∀ x : Site 2,
      mu0.real (FK.clusterInfiniteEvent 2 x) =
        mu0.real (FK.clusterInfiniteEvent 2 (origin 2)) := by
    intro x
    apply clusterInfiniteEvent_real_eq_origin_of_translationInvariant mu0
    simpa [mu0] using
      (FK.fkgqt_freeIV_isTranslationInvariant
        (d := 2) hp hp1 hq1)
  have hfreeUniq : mu0 (atLeastTwoInfinite 2) = 0 := by
    have h := (FK.freeInfinite_canonical_uniqueness_all_parameters
      (d := 2) (by norm_num) hp hp1 hq1).2.1
    simpa [mu0] using h
  have hFree : FK.fkThetaFree 2 hp hp1 hq0 (q := q) = 0 := by
    change mu0.real (percolationEvent 2) = 0
    have hfreePA : forall x : Site 2,
        mu0.real (FK.clusterInfiniteEvent 2 (origin 2)) *
            mu0.real (FK.clusterInfiniteEvent 2 x) <=
          mu0.real (FK.clusterInfiniteEvent 2 (origin 2) ∩
            FK.clusterInfiniteEvent 2 x) := by
      intro x
      simpa [mu0] using FK.fkgq_freeInfiniteVolume_clusterInfinite_fkg
        hp hp1 hq1 (origin 2) x
    exact percolationProbability_eq_zero_of_twoPoint_tendsto_zero
      mu0 hfreePA hfreeTI hfreeUniq
      (fun n => fkQgt4DiagonalSite (n + 1)) hdecay
  have hWired : 0 < FK.fkTheta 2 hp hp1 hq0 (q := q) := by
    change 0 < mu1.real (percolationEvent 2)
    unfold Measure.real
    rw [hWiredAlmostSure]
    norm_num
  have horder := FK.order_transition_q_large_selfDual hq hFree hWired
  have hrateEq := fkQgt4_inverseCorrelation_eq_sixVertexGapRate hwind.toBounds
  have hrateGap : Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop
      (nhds (fkQgt4SixVertexGapRate q)) := by
    rwa [<- hrateEq]
  have hgapPos : 0 < fkQgt4SixVertexGapRate q := by
    rwa [<- hrateEq]
  exact ⟨horder.1, horder.2, hrateGap, hgapPos, hWiredAlmostSure⟩

end

end StatMech.FrontierD
