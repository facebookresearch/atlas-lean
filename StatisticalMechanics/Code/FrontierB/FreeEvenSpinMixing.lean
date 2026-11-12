/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.FreeParityErrorVanishing
import Code.Ising.GKS2

open Filter MeasureTheory Set Topology Function
open scoped BigOperators symmDiff

namespace StatMech.FrontierB

open ConfigSpace FK Ising Lattice Percolation Sharpness

variable {d : Nat}

private noncomputable def eventIndicator {Omega : Type*} (A : Set Omega) : Omega → Real :=
  A.indicator fun _ => 1

private theorem eventIndicator_mem_Icc {Omega : Type*} (A : Set Omega) (x : Omega) :
    eventIndicator A x ∈ Set.Icc (0 : Real) 1 := by
  by_cases hx : x ∈ A <;> simp [eventIndicator, hx]

private theorem eventBirkhoffAverage_mem_Icc {Omega : Type*}
    (T : Omega → Omega) (A : Set Omega) (n : Nat) (x : Omega) :
    birkhoffAverage Real T (eventIndicator A) n x ∈ Set.Icc (0 : Real) 1 := by
  rcases n with _ | n
  · simp [birkhoffAverage]
  · have hterm : ∀ k ∈ Finset.range (n + 1),
        eventIndicator A (T^[k] x) ∈ Set.Icc (0 : Real) 1 :=
      fun k hk => eventIndicator_mem_Icc A _
    have hsum0 : 0 ≤ ∑ k ∈ Finset.range (n + 1),
        eventIndicator A (T^[k] x) :=
      Finset.sum_nonneg fun k hk => (hterm k hk).1
    have hsum1 : (∑ k ∈ Finset.range (n + 1),
        eventIndicator A (T^[k] x)) ≤ (n + 1 : Real) := by
      calc
        _ ≤ ∑ _k ∈ Finset.range (n + 1), (1 : Real) :=
          Finset.sum_le_sum fun k hk => (hterm k hk).2
        _ = (n + 1 : Real) := by simp
    simp only [birkhoffAverage, birkhoffSum, smul_eq_mul]
    norm_num [Nat.cast_add, Nat.cast_one] at hsum1 ⊢
    constructor
    · exact mul_nonneg (inv_nonneg.mpr (by positivity)) hsum0
    · calc
        (n + 1 : Real)⁻¹ *
            (∑ k ∈ Finset.range (n + 1), eventIndicator A (T^[k] x)) ≤
            (n + 1 : Real)⁻¹ * (n + 1 : Real) :=
          mul_le_mul_of_nonneg_left hsum1 (inv_nonneg.mpr (by positivity))
        _ = 1 := inv_mul_cancel₀ (by positivity)

theorem freeInfiniteVolume_eventPairCorrelationAverage_tendsto
    (hd : 1 ≤ d) {p : Real} (hp : 0 < p) (hp1 : p < 1)
    (A B : Set (ConfigSpace (Sym2 (Site d))))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    let mu := (freeInfiniteVolume d hp hp1
      (by norm_num : (0 : Real) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
    Tendsto (fun n : Nat => (n : Real)⁻¹ * ∑ k ∈ Finset.range n,
        mu.real (A ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' B))
      atTop (nhds (mu.real A * mu.real B)) := by
  dsimp only
  let mu := (freeInfiniteVolume d hp hp1
    (by norm_num : (0 : Real) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
  let T := (shift (FK.freeAxisTranslation hd) :
    ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
  have herg : _root_.Ergodic T mu :=
    FK.freeInfiniteVolume_axisShift_ergodic hd hp hp1
  have hIA : Integrable (eventIndicator A) mu :=
    (integrable_const (1 : Real)).indicator hA
  have hIB : Integrable (eventIndicator B) mu :=
    (integrable_const (1 : Real)).indicator hB
  have hbirk := StatMech.BirkhoffAE.Ergodic.tendsto_birkhoffAverage_integral_ae
    herg hIB
  let F : Nat → ConfigSpace (Sym2 (Site d)) → Real := fun n omega =>
    eventIndicator A omega * birkhoffAverage Real T (eventIndicator B) n omega
  have hmassB : (∫ x, eventIndicator B x ∂mu) = mu.real B := by
    unfold eventIndicator
    rw [MeasureTheory.integral_indicator_const (1 : Real) hB]
    simp
  have hlim : ∀ᵐ omega ∂mu, Tendsto (fun n => F n omega) atTop
      (nhds (eventIndicator A omega * mu.real B)) := by
    filter_upwards [hbirk] with omega homega
    rw [hmassB] at homega
    exact tendsto_const_nhds.mul homega
  have hmeas : ∀ n, AEStronglyMeasurable (F n) mu := by
    intro n
    exact hIA.aestronglyMeasurable.mul
      (StatMech.BirkhoffAE.aestronglyMeasurable_birkhoffAverage
        herg.toMeasurePreserving hIB n)
  have hbound : ∀ n, ∀ᵐ omega ∂mu, ‖F n omega‖ ≤ (1 : Real) := by
    intro n
    filter_upwards with omega
    have ha := eventIndicator_mem_Icc A omega
    have hb := eventBirkhoffAverage_mem_Icc T B n omega
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha.1 hb.1)]
    exact mul_le_one₀ ha.2 hb.1 hb.2
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := mu) (fun _ => (1 : Real)) hmeas (by fun_prop) hbound hlim
  have hlimit : (∫ omega, eventIndicator A omega * mu.real B ∂mu) =
      mu.real A * mu.real B := by
    unfold eventIndicator
    rw [MeasureTheory.integral_mul_const,
      MeasureTheory.integral_indicator_const (1 : Real) hA]
    simp
  rw [hlimit] at hdct
  apply hdct.congr'
  filter_upwards with n
  have hpoint : (fun omega => F n omega) = fun omega =>
      (n : Real)⁻¹ * ∑ k ∈ Finset.range n,
        eventIndicator (A ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' B) omega := by
    funext omega
    simp only [F, T, birkhoffAverage, birkhoffSum, smul_eq_mul,
      FK.shift_freeAxisTranslationPower]
    calc
      eventIndicator A omega * ((n : Real)⁻¹ *
          ∑ k ∈ Finset.range n, eventIndicator B
            ((shift (FK.freeAxisTranslation hd))^[k] omega)) =
          (n : Real)⁻¹ * ∑ k ∈ Finset.range n,
            (eventIndicator A omega * eventIndicator B
              ((shift (FK.freeAxisTranslation hd))^[k] omega)) := by
        rw [mul_comm (eventIndicator A omega), mul_assoc, Finset.sum_mul]
        conv_lhs => rw [Finset.mul_sum]
        conv_rhs => rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        by_cases ha : omega ∈ A <;>
          by_cases hb : (shift (FK.freeAxisTranslation hd))^[k] omega ∈ B <;>
          simp [eventIndicator, ha, hb]
  rw [hpoint, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro k hk
    unfold eventIndicator
    rw [MeasureTheory.integral_indicator_const (1 : Real)]
    · simp only [smul_eq_mul, mul_one, mu]
    · exact hA.inter (hB.preimage
        (measurable_shift (FK.freeAxisTranslationPower hd k)))
  · intro k hk
    exact (integrable_const (1 : Real)).indicator
      (hA.inter (hB.preimage
        (measurable_shift (FK.freeAxisTranslationPower hd k))))

theorem markReachableCount_shift_eq
    (g : Multiplicative (Site d))
    (omega : ConfigSpace (Sym2 (Site d))) (A : Finset (Site d)) (x : Site d) :
    markReachableCount (hypercubicLattice d) (shift g omega) A x =
      markReachableCount (hypercubicLattice d) omega
        (A.image fun y => g⁻¹ • y) (g⁻¹ • x) := by
  classical
  letI : DecidableRel (openSub (hypercubicLattice d) (shift g omega)).Reachable :=
    Classical.decRel _
  letI : DecidableRel (openSub (hypercubicLattice d) omega).Reachable :=
    Classical.decRel _
  unfold markReachableCount
  apply Finset.card_bij (fun y _ => g⁻¹ • y)
  · intro y hy
    rw [Finset.mem_filter] at hy ⊢
    refine ⟨Finset.mem_image.2 ⟨y, hy.1, rfl⟩, ?_⟩
    simpa only [openSub, openSubgraph, FK.Connected] using
      (connected_shift g omega (g⁻¹ • x) (g⁻¹ • y)).mp (by
        simpa using hy.2)
  · intro a ha b hb hab
    exact MulAction.injective g⁻¹ hab
  · intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨z, hzA, hzy⟩ := Finset.mem_image.1 hy.1
    refine ⟨z, ?_, hzy⟩
    rw [Finset.mem_filter]
    refine ⟨hzA, ?_⟩
    have hconn : Lattice.Connected d omega (g⁻¹ • x) (g⁻¹ • z) := by
      rw [hzy]
      exact hy.2
    have := (connected_shift g omega (g⁻¹ • x) (g⁻¹ • z)).mpr hconn
    simpa using this

theorem allClustersEven_shift_iff
    (g : Multiplicative (Site d))
    (omega : ConfigSpace (Sym2 (Site d))) (A : Finset (Site d)) :
    AllClustersEven (hypercubicLattice d) (shift g omega) A ↔
      AllClustersEven (hypercubicLattice d) omega
        (A.image fun x => g⁻¹ • x) := by
  rw [allClustersEven_iff_mark_reachability,
    allClustersEven_iff_mark_reachability]
  constructor
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    rw [← markReachableCount_shift_eq g omega A x]
    exact h x hx
  · intro h x hx
    rw [markReachableCount_shift_eq g omega A x]
    exact h (g⁻¹ • x) (Finset.mem_image.2 ⟨x, hx, rfl⟩)

theorem preimage_allClustersEvenEvent_shift
    (g : Multiplicative (Site d)) (A : Finset (Site d)) :
    shift g ⁻¹' allClustersEvenEvent (hypercubicLattice d) A =
      allClustersEvenEvent (hypercubicLattice d)
        (A.image fun x => g⁻¹ • x) := by
  ext omega
  exact allClustersEven_shift_iff g omega A

private noncomputable def freeEvenParityGap
    (hd : 1 ≤ d) (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (A B : Finset (Site d)) (k : Nat) : Real :=
  mu.real (allClustersEvenEvent (hypercubicLattice d)
      (A ∪ inverseAxisTranslateFinset hd k B)) -
    mu.real (allClustersEvenEvent (hypercubicLattice d) A) *
      mu.real (allClustersEvenEvent (hypercubicLattice d) B)

theorem freeEvenParityGap_average_tendsto_zero
    (hd : 1 ≤ d) {p : Real} (hp : 0 < p) (hp1 : p < 1)
    (A B : Finset (Site d)) (hAeven : Even A.card) (hBeven : Even B.card) :
    let mu := (freeInfiniteVolume d hp hp1
      (by norm_num : (0 : Real) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
    Tendsto (fun n : Nat => (n : Real)⁻¹ * ∑ k ∈ Finset.range n,
      freeEvenParityGap hd mu A B k) atTop (nhds 0) := by
  dsimp only
  let phi := freeInfiniteVolume d hp hp1 (by norm_num : (0 : Real) < 2)
  let mu := (phi : Measure (ConfigSpace (Sym2 (Site d))))
  let EA := allClustersEvenEvent (hypercubicLattice d) A
  let EB := allClustersEvenEvent (hypercubicLattice d) B
  have hcorr := freeInfiniteVolume_eventPairCorrelationAverage_tendsto
    hd hp hp1 EA EB (measurableSet_allClustersEvenEvent A)
      (measurableSet_allClustersEvenEvent B)
  have hinter : Tendsto (fun n : Nat => (n : Real)⁻¹ * ∑ k ∈ Finset.range n,
      (mu.real (EA ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' EB) -
        mu.real EA * mu.real EB)) atTop (nhds 0) := by
    have hcorr' : Tendsto (fun n : Nat => (n : Real)⁻¹ *
        ∑ k ∈ Finset.range n,
          mu.real (EA ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' EB))
        atTop (nhds (mu.real EA * mu.real EB)) := by
      simpa only [mu, phi] using hcorr
    have hc : Tendsto (fun _ : Nat => mu.real EA * mu.real EB) atTop
        (nhds (mu.real EA * mu.real EB)) := tendsto_const_nhds
    have hsub := hcorr'.sub hc
    simp only [sub_self] at hsub
    apply hsub.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    have hnR : (n : Real) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp
  obtain ⟨R, hAR⟩ := Lattice.finite_subset_box
    (A : Set (Site d)) A.finite_toSet
  have hdisj : ∀ᶠ k in atTop,
      Disjoint A (inverseAxisTranslateFinset hd k B) := by
    filter_upwards [inverseAxisTranslateFinset_eventually_outside_box hd B R]
      with k hk
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact hk hxB (hAR hxA)
  have hunique : mu (atLeastTwoInfinite d) = 0 := by
    exact (freeInfinite_q2_canonical_uniqueness_all_parameters hd hp hp1).2.1
  have herr := twoOddCrossClusters_axisTranslate_real_tendsto_zero
    hd phi hunique A B
  let D : Nat → Real := fun k =>
    mu.real (allClustersEvenEvent (hypercubicLattice d)
        (A ∪ inverseAxisTranslateFinset hd k B)) -
      mu.real (EA ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' EB)
  have hD : Tendsto D atTop (nhds 0) := by
    apply squeeze_zero' (g := fun k => mu.real
      (twoOddCrossClustersEvent (hypercubicLattice d) A
        (inverseAxisTranslateFinset hd k B)))
    · filter_upwards [hdisj] with k hk
      have hpre : shift (FK.freeAxisTranslationPower hd k) ⁻¹' EB =
          allClustersEvenEvent (hypercubicLattice d)
            (inverseAxisTranslateFinset hd k B) := by
        exact preimage_allClustersEvenEvent_shift
          (FK.freeAxisTranslationPower hd k) B
      have hsub : EA ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' EB ⊆
          allClustersEvenEvent (hypercubicLattice d)
            (A ∪ inverseAxisTranslateFinset hd k B) := by
        rw [hpre]
        intro omega homega
        exact allClustersEven_union_of_disjoint (hypercubicLattice d) omega A
          (inverseAxisTranslateFinset hd k B) hk homega.1 homega.2
      exact sub_nonneg.mpr (measureReal_mono hsub)
    · filter_upwards [hdisj] with k hk
      have hpre : shift (FK.freeAxisTranslationPower hd k) ⁻¹' EB =
          allClustersEvenEvent (hypercubicLattice d)
            (inverseAxisTranslateFinset hd k B) :=
        preimage_allClustersEvenEvent_shift (FK.freeAxisTranslationPower hd k) B
      have hsub : EA ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' EB ⊆
          allClustersEvenEvent (hypercubicLattice d)
            (A ∪ inverseAxisTranslateFinset hd k B) := by
        rw [hpre]
        intro omega homega
        exact allClustersEven_union_of_disjoint (hypercubicLattice d) omega A
          (inverseAxisTranslateFinset hd k B) hk homega.1 homega.2
      have hdiff := allClustersEven_factorization_error_subset
        (hypercubicLattice d) A (inverseAxisTranslateFinset hd k B) hk hAeven
          (by
            rw [inverseAxisTranslateFinset, Finset.card_image_of_injective _
              (MulAction.injective (FK.freeAxisTranslationPower hd k)⁻¹)]
            exact hBeven)
      have hdiff' : allClustersEvenEvent (hypercubicLattice d)
            (A ∪ inverseAxisTranslateFinset hd k B) \
            (EA ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' EB) ⊆
          twoOddCrossClustersEvent (hypercubicLattice d) A
            (inverseAxisTranslateFinset hd k B) := by
        rwa [hpre]
      have heq : D k = mu.real
          (allClustersEvenEvent (hypercubicLattice d)
            (A ∪ inverseAxisTranslateFinset hd k B) \
            (EA ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' EB)) := by
        dsimp [D]
        rw [measureReal_diff hsub
          ((measurableSet_allClustersEvenEvent A).inter
            ((measurableSet_allClustersEvenEvent B).preimage
              (measurable_shift (FK.freeAxisTranslationPower hd k))))]
      rw [heq]
      have hfinite : mu
          (twoOddCrossClustersEvent (hypercubicLattice d) A
            (inverseAxisTranslateFinset hd k B)) ≠ ⊤ := measure_ne_top mu _
      exact measureReal_mono hdiff' (by exact hfinite)
    · exact herr
  have hDavg := hD.cesaro
  have hsum : Tendsto (fun n : Nat => (n : Real)⁻¹ * ∑ k ∈ Finset.range n,
        (mu.real (EA ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' EB) -
          mu.real EA * mu.real EB) +
      (n : Real)⁻¹ * ∑ k ∈ Finset.range n, D k) atTop (nhds 0) := by
    simpa only [zero_add] using hinter.add hDavg
  apply hsum.congr'
  filter_upwards with n
  dsimp [D, freeEvenParityGap, EA, EB, mu]
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply congrArg (fun z : Real => (n : Real)⁻¹ * z)
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem freeState_spinProd_gks_second
    (d : Nat) (beta : Real) (hbeta : 0 ≤ beta)
    (A B : Finset (Site d)) :
    (∫ sigma, spinProd A sigma
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) *
      (∫ sigma, spinProd B sigma
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) ≤
      ∫ sigma, spinProd (A ∆ B) sigma
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
  have hAconv := integral_freeMeasure_spinProd_tendsto_freeState
    d beta hbeta A
  have hBconv := integral_freeMeasure_spinProd_tendsto_freeState
    d beta hbeta B
  have hABconv := integral_freeMeasure_spinProd_tendsto_freeState
    d beta hbeta (A ∆ B)
  apply le_of_tendsto_of_tendsto (hAconv.mul hBconv) hABconv
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box
    ((A : Set (Site d)) ∪ (B : Set (Site d)))
    (A.finite_toSet.union B.finite_toSet)
  filter_upwards [eventually_ge_atTop R] with n hn
  have hAn : (A : Set (Site d)) ⊆ box d n :=
    (fun x hx => box_mono d hn (hR (Or.inl hx)))
  have hBn : (B : Set (Site d)) ⊆ box d n :=
    (fun x hx => box_mono d hn (hR (Or.inr hx)))
  have hABn : ((A ∆ B : Finset (Site d)) : Set (Site d)) ⊆ box d n := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_symmDiff] at hx
    exact hx.elim (fun h => hAn h.1) (fun h => hBn h.1)
  rw [integral_freeMeasure_spinProd d n beta 0 A hAn,
    integral_freeMeasure_spinProd d n beta 0 B hBn,
    integral_freeMeasure_spinProd d n beta 0 (A ∆ B) hABn]
  have hsupport : boxSpinSupport d n (A ∆ B) =
      boxSpinSupport d n A ∆ boxSpinSupport d n B := by
    ext x
    simp only [boxSpinSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_symmDiff]
  rw [hsupport]
  exact gks_second (sctBoxGraph d n) beta 0 hbeta le_rfl
    (boxSpinSupport d n A) (boxSpinSupport d n B)

theorem freeEvenParityMass_gap_nonneg_of_disjoint
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (A B : Finset (Site d)) (hAeven : Even A.card) (hBeven : Even B.card)
    (hdisj : Disjoint A B) :
    let mu := (freeInfiniteVolume d
      (p := 1 - Real.exp (-2 * beta)) (q := 2)
      (by
        apply sub_pos.mpr
        rw [Real.exp_lt_one_iff]
        linarith)
      (by linarith [Real.exp_pos (-2 * beta)])
      (by norm_num : (0 : Real) < 2) : Measure _)
    0 ≤ mu.real (allClustersEvenEvent (hypercubicLattice d) (A ∪ B)) -
      mu.real (allClustersEvenEvent (hypercubicLattice d) A) *
        mu.real (allClustersEvenEvent (hypercubicLattice d) B) := by
  dsimp only
  have hUnionEven : Even (A ∪ B).card := by
    rw [Finset.card_union_of_disjoint hdisj]
    exact hAeven.add hBeven
  have hsymm : A ∆ B = A ∪ B := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_union]
    constructor
    · intro h
      rcases h with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    · intro h
      rcases h with hx | hx
      · left
        exact ⟨hx, fun hy => Finset.disjoint_left.1 hdisj hx hy⟩
      · right
        exact ⟨hx, fun hy => Finset.disjoint_left.1 hdisj hy hx⟩
  rw [← integral_freeState_spinProd_eq_freeInfinite_allClustersEven
      d beta hbeta hd (A ∪ B) hUnionEven,
    ← integral_freeState_spinProd_eq_freeInfinite_allClustersEven
      d beta hbeta hd A hAeven,
    ← integral_freeState_spinProd_eq_freeInfinite_allClustersEven
      d beta hbeta hd B hBeven,
    sub_nonneg, ← hsymm]
  exact freeState_spinProd_gks_second d beta hbeta.le A B

private noncomputable def freeEvenParityFamilyTerm
    (hd : 1 ≤ d) (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (A B : Finset (Site d)) (k : Nat) : Real :=
  freeEvenParityGap hd mu A B k +
    if Disjoint A (inverseAxisTranslateFinset hd k B) then 0 else 2

private theorem freeInfiniteVolume_allClustersEven_inverseTranslate_real_eq
    (hd : 1 ≤ d) {p : Real} (hp : 0 < p) (hp1 : p < 1)
    (B : Finset (Site d)) (k : Nat) :
    let mu := (freeInfiniteVolume d hp hp1
      (by norm_num : (0 : Real) < 2) :
        Measure (ConfigSpace (Sym2 (Site d))))
    mu.real (allClustersEvenEvent (hypercubicLattice d)
        (inverseAxisTranslateFinset hd k B)) =
      mu.real (allClustersEvenEvent (hypercubicLattice d) B) := by
  dsimp only
  let mu := (freeInfiniteVolume d hp hp1
    (by norm_num : (0 : Real) < 2) :
      Measure (ConfigSpace (Sym2 (Site d))))
  have hti : IsTranslationInvariant
      (G := Multiplicative (Site d)) mu :=
    bdp_freeIV_isTranslationInvariant hp hp1
  rw [show allClustersEvenEvent (hypercubicLattice d)
        (inverseAxisTranslateFinset hd k B) =
      shift (FK.freeAxisTranslationPower hd k) ⁻¹'
        allClustersEvenEvent (hypercubicLattice d) B by
      exact (preimage_allClustersEvenEvent_shift
        (FK.freeAxisTranslationPower hd k) B).symm]
  exact fmc_real_preimage_shift hti (FK.freeAxisTranslationPower hd k)
    (measurableSet_allClustersEvenEvent B)

private theorem freeEvenParityFamilyTerm_nonneg
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (A B : Finset (Site d)) (hAeven : Even A.card) (hBeven : Even B.card)
    (k : Nat) :
    let mu := (freeInfiniteVolume d
      (p := 1 - Real.exp (-2 * beta)) (q := 2)
      (by
        apply sub_pos.mpr
        rw [Real.exp_lt_one_iff]
        linarith)
      (by linarith [Real.exp_pos (-2 * beta)])
      (by norm_num : (0 : Real) < 2) : Measure _)
    0 ≤ freeEvenParityFamilyTerm hd mu A B k := by
  dsimp only
  let p := 1 - Real.exp (-2 * beta)
  have hp : 0 < p := by
    dsimp [p]
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    linarith
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-2 * beta)]
  let mu := (freeInfiniteVolume d hp hp1
    (by norm_num : (0 : Real) < 2) :
      Measure (ConfigSpace (Sym2 (Site d))))
  by_cases hdisj : Disjoint A (inverseAxisTranslateFinset hd k B)
  · simp only [freeEvenParityFamilyTerm, if_pos hdisj, add_zero]
    have hgap := freeEvenParityMass_gap_nonneg_of_disjoint hd hbeta A
      (inverseAxisTranslateFinset hd k B) hAeven (by
        rw [inverseAxisTranslateFinset, Finset.card_image_of_injective _
          (MulAction.injective (FK.freeAxisTranslationPower hd k)⁻¹)]
        exact hBeven) hdisj
    have hgap' : 0 ≤
        mu.real (allClustersEvenEvent (hypercubicLattice d)
            (A ∪ inverseAxisTranslateFinset hd k B)) -
          mu.real (allClustersEvenEvent (hypercubicLattice d) A) *
            mu.real (allClustersEvenEvent (hypercubicLattice d)
              (inverseAxisTranslateFinset hd k B)) := by
      simpa only [mu] using hgap
    rw [freeInfiniteVolume_allClustersEven_inverseTranslate_real_eq
      hd hp hp1 B k] at hgap'
    simpa only [freeEvenParityGap, mu] using hgap'
  · simp only [freeEvenParityFamilyTerm, if_neg hdisj]
    have hprod : mu.real (allClustersEvenEvent (hypercubicLattice d) A) *
        mu.real (allClustersEvenEvent (hypercubicLattice d) B) ≤ 1 :=
      mul_le_one₀ measureReal_le_one measureReal_nonneg measureReal_le_one
    have hmass : 0 ≤ mu.real (allClustersEvenEvent (hypercubicLattice d)
        (A ∪ inverseAxisTranslateFinset hd k B)) := measureReal_nonneg
    dsimp [freeEvenParityGap, mu]
    linarith

private theorem freeEvenParityFamilyTerm_average_tendsto_zero
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (A B : Finset (Site d)) (hAeven : Even A.card) (hBeven : Even B.card) :
    let p := 1 - Real.exp (-2 * beta)
    let mu := (freeInfiniteVolume d
      (p := p) (q := 2)
      (by
        dsimp [p]
        apply sub_pos.mpr
        rw [Real.exp_lt_one_iff]
        linarith)
      (by
        dsimp [p]
        linarith [Real.exp_pos (-2 * beta)])
      (by norm_num : (0 : Real) < 2) : Measure _)
    Tendsto (fun n : Nat => (n : Real)⁻¹ * ∑ k ∈ Finset.range n,
      freeEvenParityFamilyTerm hd mu A B k) atTop (nhds 0) := by
  dsimp only
  let p := 1 - Real.exp (-2 * beta)
  have hp : 0 < p := by
    dsimp [p]
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    linarith
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-2 * beta)]
  let mu := (freeInfiniteVolume d hp hp1
    (by norm_num : (0 : Real) < 2) :
      Measure (ConfigSpace (Sym2 (Site d))))
  have hgap := freeEvenParityGap_average_tendsto_zero
    hd hp hp1 A B hAeven hBeven
  obtain ⟨R, hAR⟩ := Lattice.finite_subset_box
    (A : Set (Site d)) A.finite_toSet
  have hdisj : ∀ᶠ k in atTop,
      Disjoint A (inverseAxisTranslateFinset hd k B) := by
    filter_upwards [inverseAxisTranslateFinset_eventually_outside_box hd B R]
      with k hk
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact hk hxB (hAR hxA)
  let penalty : Nat → Real := fun k =>
    if Disjoint A (inverseAxisTranslateFinset hd k B) then 0 else 2
  have hpenalty : Tendsto penalty atTop (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hdisj] with k hk
    simp [penalty, hk]
  have hpenaltyAvg := hpenalty.cesaro
  have hadd := hgap.add hpenaltyAvg
  simpa only [zero_add, freeEvenParityFamilyTerm, penalty,
    Finset.sum_add_distrib, mul_add, mu, p] using hadd




theorem freeInfiniteVolume_evenParity_family_pairMixing_after
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (K : Nat)
    (supports : Finset (Finset (Site d)))
    (heven : ∀ A ∈ supports, Even A.card)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    let p := 1 - Real.exp (-2 * beta)
    let mu := (freeInfiniteVolume d
      (p := p) (q := 2)
      (by
        dsimp [p]
        apply sub_pos.mpr
        rw [Real.exp_lt_one_iff]
        linarith)
      (by
        dsimp [p]
        linarith [Real.exp_pos (-2 * beta)])
      (by norm_num : (0 : Real) < 2) : Measure _)
    ∃ k : Nat, K ≤ k ∧
      ∀ A ∈ supports, ∀ B ∈ supports,
        Disjoint A (B.image fun x =>
          (FK.freeAxisTranslationPower hd k)⁻¹ • x) ∧
        abs (mu.real (allClustersEvenEvent (hypercubicLattice d)
              (A ∪ B.image fun x =>
                (FK.freeAxisTranslationPower hd k)⁻¹ • x)) -
            mu.real (allClustersEvenEvent (hypercubicLattice d) A) *
              mu.real (allClustersEvenEvent (hypercubicLattice d) B)) <
          epsilon := by
  classical
  dsimp only
  let p := 1 - Real.exp (-2 * beta)
  have hp : 0 < p := by
    dsimp [p]
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    linarith
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-2 * beta)]
  let mu := (freeInfiniteVolume d hp hp1
    (by norm_num : (0 : Real) < 2) :
      Measure (ConfigSpace (Sym2 (Site d))))
  let delta := min epsilon (1 / 2 : Real)
  have hdelta : 0 < delta := lt_min hepsilon (by norm_num)
  have hbase : Tendsto (fun n : Nat =>
      ∑ A ∈ supports, ∑ B ∈ supports, (n : Real)⁻¹ *
        ∑ k ∈ Finset.range n, freeEvenParityFamilyTerm hd mu A B k)
      atTop (nhds 0) := by
    convert tendsto_finsetSum supports (fun A hA =>
      tendsto_finsetSum supports (fun B hB =>
        freeEvenParityFamilyTerm_average_tendsto_zero hd hbeta A B
          (heven A hA) (heven B hB))) using 1 <;>
      simp only [Finset.sum_const_zero]
  let latePenalty : Nat → Real := fun k => if K ≤ k then 0 else 2
  have hlate : Tendsto latePenalty atTop (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop K] with k hk
    simp [latePenalty, hk]
  have htotal : Tendsto (fun n : Nat =>
      (∑ A ∈ supports, ∑ B ∈ supports, (n : Real)⁻¹ *
        ∑ k ∈ Finset.range n, freeEvenParityFamilyTerm hd mu A B k) +
      (n : Real)⁻¹ * ∑ k ∈ Finset.range n, latePenalty k)
      atTop (nhds 0) := by
    simpa only [zero_add] using hbase.add hlate.cesaro
  have hevent : ∀ᶠ n : Nat in atTop,
      ((∑ A ∈ supports, ∑ B ∈ supports, (n : Real)⁻¹ *
        ∑ k ∈ Finset.range n, freeEvenParityFamilyTerm hd mu A B k) +
        (n : Real)⁻¹ * ∑ k ∈ Finset.range n, latePenalty k) <
        delta := htotal.eventually (eventually_lt_nhds hdelta)
  obtain ⟨n, hn, havg⟩ := ((eventually_ge_atTop 1).and hevent).exists
  have havg' : (n : Real)⁻¹ * ∑ k ∈ Finset.range n,
      ((∑ A ∈ supports, ∑ B ∈ supports,
        freeEvenParityFamilyTerm hd mu A B k) + latePenalty k) < delta := by
    calc
      (n : Real)⁻¹ * ∑ k ∈ Finset.range n,
          ((∑ A ∈ supports, ∑ B ∈ supports,
            freeEvenParityFamilyTerm hd mu A B k) + latePenalty k) =
          (∑ A ∈ supports, ∑ B ∈ supports, (n : Real)⁻¹ *
            ∑ k ∈ Finset.range n,
              freeEvenParityFamilyTerm hd mu A B k) +
            (n : Real)⁻¹ * ∑ k ∈ Finset.range n, latePenalty k := by
        rw [Finset.sum_add_distrib, mul_add]
        congr 1
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro A hA
        rw [Finset.sum_comm]
      _ < delta := havg
  have hnR : (0 : Real) < n := by positivity
  have hsumlt :
      (∑ k ∈ Finset.range n,
        ((∑ A ∈ supports, ∑ B ∈ supports,
          freeEvenParityFamilyTerm hd mu A B k) + latePenalty k)) <
      ∑ _k ∈ Finset.range n, delta := by
    calc
      (∑ k ∈ Finset.range n,
          ((∑ A ∈ supports, ∑ B ∈ supports,
            freeEvenParityFamilyTerm hd mu A B k) + latePenalty k)) =
          (n : Real) * ((n : Real)⁻¹ * ∑ k ∈ Finset.range n,
            ((∑ A ∈ supports, ∑ B ∈ supports,
              freeEvenParityFamilyTerm hd mu A B k) + latePenalty k)) := by
        field_simp
      _ < (n : Real) * delta := mul_lt_mul_of_pos_left havg' hnR
      _ = ∑ _k ∈ Finset.range n, delta := by simp
  obtain ⟨k, hk, hkdelta⟩ := Finset.exists_lt_of_sum_lt hsumlt
  have hsumNonneg : 0 ≤ ∑ A ∈ supports, ∑ B ∈ supports,
      freeEvenParityFamilyTerm hd mu A B k :=
    Finset.sum_nonneg fun A hA => Finset.sum_nonneg fun B hB =>
      freeEvenParityFamilyTerm_nonneg hd hbeta A B
        (heven A hA) (heven B hB) k
  have hkK : K ≤ k := by
    by_contra hnot
    have hpen : latePenalty k = 2 := by simp [latePenalty, hnot]
    have hdeltaHalf : delta ≤ 1 / 2 := min_le_right _ _
    rw [hpen] at hkdelta
    linarith
  refine ⟨k, hkK, ?_⟩
  intro A hA B hB
  have hinner : freeEvenParityFamilyTerm hd mu A B k ≤
      ∑ B' ∈ supports, freeEvenParityFamilyTerm hd mu A B' k :=
    Finset.single_le_sum (fun B' hB' =>
      freeEvenParityFamilyTerm_nonneg hd hbeta A B'
        (heven A hA) (heven B' hB') k) hB
  have houter : (∑ B' ∈ supports,
      freeEvenParityFamilyTerm hd mu A B' k) ≤
      ∑ A' ∈ supports, ∑ B' ∈ supports,
        freeEvenParityFamilyTerm hd mu A' B' k :=
    Finset.single_le_sum (fun A' hA' => Finset.sum_nonneg fun B' hB' =>
      freeEvenParityFamilyTerm_nonneg hd hbeta A' B'
        (heven A' hA') (heven B' hB') k) hA
  have hterm : freeEvenParityFamilyTerm hd mu A B k < delta :=
    lt_of_le_of_lt (hinner.trans (houter.trans (by
      have hlateNonneg : 0 ≤ latePenalty k := by
        dsimp [latePenalty]
        split <;> norm_num
      linarith))) hkdelta
  have hdisj : Disjoint A (inverseAxisTranslateFinset hd k B) := by
    by_contra hnot
    have hprod : mu.real (allClustersEvenEvent (hypercubicLattice d) A) *
        mu.real (allClustersEvenEvent (hypercubicLattice d) B) ≤ 1 :=
      mul_le_one₀ measureReal_le_one measureReal_nonneg measureReal_le_one
    have hmass : 0 ≤ mu.real (allClustersEvenEvent (hypercubicLattice d)
        (A ∪ inverseAxisTranslateFinset hd k B)) := measureReal_nonneg
    have hdeltaHalf : delta ≤ 1 / 2 := min_le_right _ _
    dsimp [freeEvenParityFamilyTerm, freeEvenParityGap] at hterm
    rw [if_neg hnot] at hterm
    linarith
  refine ⟨hdisj, ?_⟩
  have hgapNonneg := freeEvenParityMass_gap_nonneg_of_disjoint hd hbeta A
    (inverseAxisTranslateFinset hd k B) (heven A hA) (by
      rw [inverseAxisTranslateFinset, Finset.card_image_of_injective _
        (MulAction.injective (FK.freeAxisTranslationPower hd k)⁻¹)]
      exact heven B hB) hdisj
  have hgapNonneg' : 0 ≤
      mu.real (allClustersEvenEvent (hypercubicLattice d)
          (A ∪ inverseAxisTranslateFinset hd k B)) -
        mu.real (allClustersEvenEvent (hypercubicLattice d) A) *
          mu.real (allClustersEvenEvent (hypercubicLattice d)
            (inverseAxisTranslateFinset hd k B)) := by
    simpa only [mu] using hgapNonneg
  rw [freeInfiniteVolume_allClustersEven_inverseTranslate_real_eq
    hd hp hp1 B k] at hgapNonneg'
  have hgaplt : freeEvenParityGap hd mu A B k < epsilon := by
    have hdeltaEps : delta ≤ epsilon := min_le_left _ _
    dsimp [freeEvenParityFamilyTerm] at hterm
    rw [if_pos hdisj, add_zero] at hterm
    exact hterm.trans_le hdeltaEps
  change abs (freeEvenParityGap hd mu A B k) < epsilon
  rw [abs_of_nonneg (by
    simpa only [freeEvenParityGap, mu] using hgapNonneg')]
  exact hgaplt

theorem freeInfiniteVolume_evenParity_family_pairMixing
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (supports : Finset (Finset (Site d)))
    (heven : ∀ A ∈ supports, Even A.card)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    let p := 1 - Real.exp (-2 * beta)
    let mu := (freeInfiniteVolume d
      (p := p) (q := 2)
      (by
        dsimp [p]
        apply sub_pos.mpr
        rw [Real.exp_lt_one_iff]
        linarith)
      (by
        dsimp [p]
        linarith [Real.exp_pos (-2 * beta)])
      (by norm_num : (0 : Real) < 2) : Measure _)
    ∃ g : Multiplicative (Site d),
      ∀ A ∈ supports, ∀ B ∈ supports,
        Disjoint A (B.image fun x => g⁻¹ • x) ∧
        abs (mu.real (allClustersEvenEvent (hypercubicLattice d)
              (A ∪ B.image fun x => g⁻¹ • x)) -
            mu.real (allClustersEvenEvent (hypercubicLattice d) A) *
              mu.real (allClustersEvenEvent (hypercubicLattice d) B)) <
          epsilon := by
  obtain ⟨k, hk, hmix⟩ := freeInfiniteVolume_evenParity_family_pairMixing_after
    hd hbeta 0 supports heven epsilon hepsilon
  exact ⟨FK.freeAxisTranslationPower hd k, hmix⟩

end StatMech.FrontierB
