/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.FreeCurrentFamilyMixing
import Code.Ising.IsingCrossBoxCap

open Filter MeasureTheory Set Topology
open scoped BigOperators symmDiff

namespace StatMech.FrontierB

open ConfigSpace FK Ising Lattice Sharpness

variable {d : Nat}



theorem plusState_multiOpen_upper_of_outside_box
    (d N : Nat) {beta : Real} (hbeta : 0 ≤ beta)
    (g : Multiplicative (Site d)) (T U : Finset (Site d))
    (houtside : ∀ x ∈ U.image (fun y => g⁻¹ • y), x ∉ box d N) :
    let mu := (plusState d beta 0 : Measure (ConfigSpace (Site d)))
    mu.real (fmu_multiOpen T ∩ (shift g) ⁻¹' fmu_multiOpen U) ≤
      (plusMeasure d N beta 0 : Measure (ConfigSpace (Site d))).real
          (fmu_multiOpen T) *
        mu.real (fmu_multiOpen U) := by
  dsimp only
  let mu := (plusState d beta 0 : Measure (ConfigSpace (Site d)))
  let S := U.image (fun y => g⁻¹ • y)
  obtain ⟨phi, hphi, hconv⟩ := plusState_isInfiniteVolumeState d beta 0
  have hConvCross : Tendsto (fun k =>
      (plusMeasure d (phi k) beta 0 : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen T ∩ fmu_multiOpen S)) atTop
      (nhds (mu.real (fmu_multiOpen T ∩ fmu_multiOpen S))) :=
    hconv.tendsto_real_of_isClopen
      ((ipe_multiOpen_isClopen T).inter (ipe_multiOpen_isClopen S))
  have hConvFar : Tendsto (fun k =>
      (plusMeasure d (phi k) beta 0 : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen S)) atTop (nhds (mu.real (fmu_multiOpen S))) :=
    hconv.tendsto_real_of_isClopen (ipe_multiOpen_isClopen S)
  have hbound : ∀ᶠ k in atTop,
      (plusMeasure d (phi k) beta 0 : Measure (ConfigSpace (Site d))).real
          (fmu_multiOpen T ∩ fmu_multiOpen S) ≤
        (plusMeasure d N beta 0 : Measure (ConfigSpace (Site d))).real
            (fmu_multiOpen T) *
          (plusMeasure d (phi k) beta 0 :
            Measure (ConfigSpace (Site d))).real (fmu_multiOpen S) := by
    filter_upwards [hphi.tendsto_atTop.eventually (eventually_ge_atTop N)]
      with k hk
    exact icb_box_cross_cap hk beta 0 hbeta le_rfl
      (IsClopen.measurableSet_configSpace (ipe_multiOpen_isClopen T))
      (fmu_multiOpen_isIncreasing T) S houtside
  have hlimit : mu.real (fmu_multiOpen T ∩ fmu_multiOpen S) ≤
      (plusMeasure d N beta 0 : Measure (ConfigSpace (Site d))).real
          (fmu_multiOpen T) * mu.real (fmu_multiOpen S) :=
    le_of_tendsto_of_tendsto hConvCross (tendsto_const_nhds.mul hConvFar) hbound
  have hti : IsTranslationInvariant (G := Multiplicative (Site d)) mu :=
    iptp_plusState_isTranslationInvariant hbeta le_rfl
  have hfar : mu.real (fmu_multiOpen S) = mu.real (fmu_multiOpen U) := by
    rw [← fmu_shift_multiOpen g U]
    exact fmc_real_preimage_shift hti g (fmu_multiOpen_measurable U)
  rw [fmu_shift_multiOpen g U]
  simpa only [mu, S, hfar] using hlimit



theorem plusState_multiOpen_axis_pairCorrelation_tendsto
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 ≤ beta)
    (T U : Finset (Site d)) :
    let mu := (plusState d beta 0 : Measure (ConfigSpace (Site d)))
    Tendsto (fun k : Nat =>
      mu.real (fmu_multiOpen T ∩
        (shift (FK.freeAxisTranslationPower hd k)) ⁻¹' fmu_multiOpen U))
      atTop (nhds (mu.real (fmu_multiOpen T) *
        mu.real (fmu_multiOpen U))) := by
  dsimp only
  let mu := (plusState d beta 0 : Measure (ConfigSpace (Site d)))
  have hti : IsTranslationInvariant (G := Multiplicative (Site d)) mu :=
    iptp_plusState_isTranslationInvariant hbeta le_rfl
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  let eta := epsilon / 2
  have heta : 0 < eta := by dsimp [eta]; linarith
  obtain ⟨phi, hphi, hconv⟩ := plusState_isInfiniteVolumeState d beta 0
  have hnear := hconv.tendsto_real_of_isClopen (ipe_multiOpen_isClopen T)
  have hclose : ∀ᶠ j in atTop,
      (plusMeasure d (phi j) beta 0 : Measure (ConfigSpace (Site d))).real
          (fmu_multiOpen T) < mu.real (fmu_multiOpen T) + eta :=
    hnear.eventually (eventually_lt_nhds (by linarith))
  obtain ⟨j, hj⟩ := hclose.exists
  let N := phi j
  have hout : ∀ᶠ k in atTop,
      (inverseAxisTranslateFinset hd k U : Set (Site d)) ⊆
        (box d N)ᶜ :=
    inverseAxisTranslateFinset_eventually_outside_box hd U N
  obtain ⟨K, hK⟩ := (eventually_atTop.1 hout)
  refine ⟨K, ?_⟩
  intro k hk
  have hkout : ∀ x ∈ U.image
      (fun y => (FK.freeAxisTranslationPower hd k)⁻¹ • y), x ∉ box d N := by
    exact hK k hk
  have hupp := plusState_multiOpen_upper_of_outside_box d N hbeta
    (FK.freeAxisTranslationPower hd k) T U hkout
  have hlower : mu.real (fmu_multiOpen T) * mu.real (fmu_multiOpen U) ≤
      mu.real (fmu_multiOpen T ∩
        (shift (FK.freeAxisTranslationPower hd k)) ⁻¹' fmu_multiOpen U) := by
    rw [fmu_shift_multiOpen]
    have hfkg := ipe_plusState_fkg_multiOpen hbeta 0 T
      (U.image (fun y => (FK.freeAxisTranslationPower hd k)⁻¹ • y))
    have hfar : mu.real (fmu_multiOpen
        (U.image (fun y => (FK.freeAxisTranslationPower hd k)⁻¹ • y))) =
        mu.real (fmu_multiOpen U) := by
      rw [← fmu_shift_multiOpen (FK.freeAxisTranslationPower hd k) U]
      exact fmc_real_preimage_shift hti (FK.freeAxisTranslationPower hd k)
        (fmu_multiOpen_measurable U)
    rwa [hfar] at hfkg
  have hUle : mu.real (fmu_multiOpen U) ≤ 1 := measureReal_le_one
  have hUnn : 0 ≤ mu.real (fmu_multiOpen U) := measureReal_nonneg
  have hupper' : mu.real (fmu_multiOpen T ∩
        (shift (FK.freeAxisTranslationPower hd k)) ⁻¹' fmu_multiOpen U) <
      mu.real (fmu_multiOpen T) * mu.real (fmu_multiOpen U) + epsilon := by
    calc
      _ ≤ (plusMeasure d N beta 0 : Measure (ConfigSpace (Site d))).real
          (fmu_multiOpen T) * mu.real (fmu_multiOpen U) := hupp
      _ ≤ (mu.real (fmu_multiOpen T) + eta) *
          mu.real (fmu_multiOpen U) :=
        mul_le_mul_of_nonneg_right hj.le hUnn
      _ ≤ mu.real (fmu_multiOpen T) * mu.real (fmu_multiOpen U) + eta := by
        nlinarith [mul_le_mul_of_nonneg_left hUle heta.le]
      _ < mu.real (fmu_multiOpen T) * mu.real (fmu_multiOpen U) + epsilon := by
        dsimp [eta]
        linarith
  rw [Real.dist_eq]
  rw [abs_of_nonneg (sub_nonneg.mpr hlower)]
  linarith

theorem plusState_moInd_axis_pairCorrelation_tendsto
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 ≤ beta)
    (T U : Finset (Site d)) :
    let mu := (plusState d beta 0 : Measure (ConfigSpace (Site d)))
    Tendsto (fun k : Nat => ∫ omega, fmu_moInd T omega *
        fmu_moInd U (shift (FK.freeAxisTranslationPower hd k) omega) ∂mu)
      atTop (nhds (mu.real (fmu_multiOpen T) *
        mu.real (fmu_multiOpen U))) := by
  dsimp only
  let mu := (plusState d beta 0 : Measure (ConfigSpace (Site d)))
  have hcorr := plusState_multiOpen_axis_pairCorrelation_tendsto
    hd hbeta T U
  apply hcorr.congr'
  filter_upwards with k
  rw [fmu_moInd_mul_shift_eq]
  rw [integral_indicator_const (1 : Real)]
  · simp
  · exact (fmu_multiOpen_measurable T).inter
      ((fmu_multiOpen_measurable U).preimage
        (measurable_shift (FK.freeAxisTranslationPower hd k)))

theorem currentShiftFinset_axis_eventually_disjoint
    (hd : 1 ≤ d) (S T : Finset (Sym2 (Site d))) :
    ∀ᶠ k in atTop,
      Disjoint S (currentShiftFinset (FK.freeAxisTranslationPower hd k) T) := by
  obtain ⟨R, hR⟩ := finite_subset_box
    (↑(edgeVertexSupport S) : Set (Site d))
    (edgeVertexSupport S).finite_toSet
  filter_upwards [inverseAxisTranslateFinset_eventually_outside_box hd
      (edgeVertexSupport T) R] with k hk
  rw [Finset.disjoint_left]
  intro e heS heShift
  rw [currentShiftFinset, Finset.mem_image] at heShift
  obtain ⟨e', heT, heq⟩ := heShift
  have hxT : e'.out.1 ∈ edgeVertexSupport T :=
    mem_edgeVertexSupport_of_mem_edge heT (Sym2.out_fst_mem e')
  have hxedge : (FK.freeAxisTranslationPower hd k)⁻¹ • e'.out.1 ∈
      (FK.freeAxisTranslationPower hd k)⁻¹ • e' := by
    change (FK.freeAxisTranslationPower hd k)⁻¹ • e'.out.1 ∈
      Sym2.map (fun x => (FK.freeAxisTranslationPower hd k)⁻¹ • x) e'
    exact Sym2.mem_map.mpr ⟨e'.out.1, Sym2.out_fst_mem e', rfl⟩
  rw [heq] at hxedge
  have hxS : (FK.freeAxisTranslationPower hd k)⁻¹ • e'.out.1 ∈
      edgeVertexSupport S :=
    mem_edgeVertexSupport_of_mem_edge heS hxedge
  exact hk (Finset.mem_image.mpr ⟨e'.out.1, hxT, rfl⟩) (hR hxS)



theorem infinitePlusCurrentMeasure_parityPattern_axis_pairCorrelation_tendsto
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (S T : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (hT : (↑T : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (odd : ↑S -> Bool) (odd' : ↑T -> Bool) :
    let nu := (infinitePlusCurrentMeasure d beta hbeta.le :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
    Tendsto (fun k : Nat => nu.real
        (currentParityPatternCylinder S odd ∩
          (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹'
            currentParityPatternCylinder T odd'))
      atTop (nhds (nu.real (currentParityPatternCylinder S odd) *
        nu.real (currentParityPatternCylinder T odd'))) := by
  classical
  dsimp only
  let mu := (plusState d beta 0 : Measure (ConfigSpace (Site d)))
  let nu := (infinitePlusCurrentMeasure d beta hbeta.le :
    Measure (InfiniteCurrentConfig (Sym2 (Site d))))
  let IS := plusParityExpansionIndices S
  let IT := plusParityExpansionIndices T
  let c := fun i => plusParityExpansionCoeff beta S odd i
  let c' := fun j => plusParityExpansionCoeff beta T odd' j
  have hterms : ∀ i ∈ IS, ∀ j ∈ IT,
      Tendsto (fun k : Nat => c i * c' j *
          ∫ omega, fmu_moInd (plusParityExpansionSupport i) omega *
            fmu_moInd (plusParityExpansionSupport j)
              (shift (FK.freeAxisTranslationPower hd k) omega) ∂mu)
        atTop (nhds (c i * c' j *
          (mu.real (fmu_multiOpen (plusParityExpansionSupport i)) *
            mu.real (fmu_multiOpen (plusParityExpansionSupport j))))) := by
    intro i hi j hj
    exact (plusState_moInd_axis_pairCorrelation_tendsto hd hbeta.le
      (plusParityExpansionSupport i) (plusParityExpansionSupport j)).const_mul _
  have hsum := tendsto_finsetSum IS (fun i hi =>
    tendsto_finsetSum IT (fun j hj => hterms i hi j hj))
  have hSdiag : ∀ e ∈ S, ¬ e.IsDiag := by
    intro e he
    exact (hypercubicLattice d).not_isDiag_of_mem_edgeSet (hS he)
  have hTdiag : ∀ e ∈ T, ¬ e.IsDiag := by
    intro e he
    exact (hypercubicLattice d).not_isDiag_of_mem_edgeSet (hT he)
  have hspin : Tendsto (fun k : Nat =>
      ∫ omega, plusParityPatternSpinPolynomial beta S odd omega *
        plusParityPatternSpinPolynomial beta T odd'
          (shift (FK.freeAxisTranslationPower hd k) omega) ∂mu)
      atTop (nhds ((∫ omega, plusParityPatternSpinPolynomial beta S odd omega
          ∂mu) *
        (∫ omega, plusParityPatternSpinPolynomial beta T odd' omega ∂mu))) := by
    convert hsum using 1
    · funext k
      simp_rw [plusParityPatternSpinPolynomial_eq_multiOpenExpansion
          beta S odd hSdiag,
        plusParityPatternSpinPolynomial_eq_multiOpenExpansion
          beta T odd' hTdiag]
      change (∫ omega, (∑ i ∈ IS,
          c i * fmu_moInd (plusParityExpansionSupport i) omega) *
        (∑ j ∈ IT, c' j * fmu_moInd (plusParityExpansionSupport j)
          (shift (FK.freeAxisTranslationPower hd k) omega)) ∂mu) = _
      have hpoint (omega : ConfigSpace (Site d)) :
          (∑ i ∈ IS, c i * fmu_moInd (plusParityExpansionSupport i) omega) *
            (∑ j ∈ IT, c' j * fmu_moInd (plusParityExpansionSupport j)
              (shift (FK.freeAxisTranslationPower hd k) omega)) =
          ∑ i ∈ IS, ∑ j ∈ IT, (c i * c' j) *
            (fmu_moInd (plusParityExpansionSupport i) omega *
              fmu_moInd (plusParityExpansionSupport j)
                (shift (FK.freeAxisTranslationPower hd k) omega)) := by
        rw [Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      simp_rw [hpoint]
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro j hj
          rw [integral_const_mul]
        · intro j hj
          exact (fmu_integrable_moInd_mul_shift
            (FK.freeAxisTranslationPower hd k)
            (plusParityExpansionSupport i)
            (plusParityExpansionSupport j)).const_mul _
      · intro i hi
        apply integrable_finsetSum
        intro j hj
        exact (fmu_integrable_moInd_mul_shift
          (FK.freeAxisTranslationPower hd k)
          (plusParityExpansionSupport i)
          (plusParityExpansionSupport j)).const_mul _
    · rw [integral_plusParityPatternSpinPolynomial_eq_multiOpenExpansion
          mu beta S odd hSdiag,
        integral_plusParityPatternSpinPolynomial_eq_multiOpenExpansion
          mu beta T odd' hTdiag,
        Finset.sum_mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
  rw [← infinitePlusCurrentMeasure_parityPattern_real_eq_integral
      hbeta S odd hS,
    ← infinitePlusCurrentMeasure_parityPattern_real_eq_integral
      hbeta T odd' hT] at hspin
  apply hspin.congr'
  filter_upwards [currentShiftFinset_axis_eventually_disjoint hd S T] with k hk
  rw [← infinitePlusCurrentMeasure_parityPattern_inter_shift_real_eq_integral
      hbeta (FK.freeAxisTranslationPower hd k) S T odd odd' hS hT hk]

theorem infinitePlusCurrentMeasure_singleton_axis_pairCorrelation_tendsto
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (S T : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (hT : (↑T : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (a : ↑S -> Nat) (b : ↑T -> Nat) :
    let nu := (infinitePlusCurrentMeasure d beta hbeta.le :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
    Tendsto (fun k : Nat => nu.real
        (currentCylinder S {a} ∩
          (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹'
            currentCylinder T {b}))
      atTop (nhds (nu.real (currentCylinder S {a}) *
        nu.real (currentCylinder T {b}))) := by
  dsimp only
  let nu := (infinitePlusCurrentMeasure d beta hbeta.le :
    Measure (InfiniteCurrentConfig (Sym2 (Site d))))
  let ka := ENNReal.toReal
    (finiteParityPMF S beta hbeta (currentLocalParity a) a)
  let kb := ENNReal.toReal
    (finiteParityPMF T beta hbeta (currentLocalParity b) b)
  have hparity :=
    (infinitePlusCurrentMeasure_parityPattern_axis_pairCorrelation_tendsto
      hd hbeta S T hS hT (currentLocalParity a) (currentLocalParity b)).const_mul
        (ka * kb)
  have hlimit :
      nu.real (currentCylinder S {a}) * nu.real (currentCylinder T {b}) =
        (ka * kb) *
          (nu.real (currentParityPatternCylinder S (currentLocalParity a)) *
            nu.real (currentParityPatternCylinder T (currentLocalParity b))) := by
    rw [infinitePlusCurrentMeasure_singleton_real_eq hbeta S hS a,
      infinitePlusCurrentMeasure_singleton_real_eq hbeta T hT b]
    dsimp [ka, kb]
    ring
  rw [hlimit]
  apply hparity.congr'
  filter_upwards [currentShiftFinset_axis_eventually_disjoint hd S T] with k hk
  rw [infinitePlusCurrentMeasure_singleton_inter_shift_real_eq hbeta
      (FK.freeAxisTranslationPower hd k) S T hS hT hk a b]
  dsimp [ka, kb]
  ring

theorem infinitePlusCurrentMeasure_finsetCylinder_axis_pairCorrelation_tendsto
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (P Q : Finset (↑S -> Nat)) :
    let nu := (infinitePlusCurrentMeasure d beta hbeta.le :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
    Tendsto (fun k : Nat => nu.real
        (currentCylinder S (↑P : Set (↑S -> Nat)) ∩
          (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹'
            currentCylinder S (↑Q : Set (↑S -> Nat))))
      atTop (nhds (nu.real (currentCylinder S (↑P : Set (↑S -> Nat))) *
        nu.real (currentCylinder S (↑Q : Set (↑S -> Nat))))) := by
  dsimp only
  let nu := (infinitePlusCurrentMeasure d beta hbeta.le :
    Measure (InfiniteCurrentConfig (Sym2 (Site d))))
  have hsum := tendsto_finsetSum P (fun a ha =>
    tendsto_finsetSum Q (fun b hb =>
      infinitePlusCurrentMeasure_singleton_axis_pairCorrelation_tendsto
        hd hbeta S S hS hS a b))
  convert hsum using 1
  · funext k
    exact currentCylinder_finset_inter_shift_real_eq_sum nu
      (FK.freeAxisTranslationPower hd k) S P Q
  · rw [currentCylinder_finset_real_eq_sum nu S P,
      currentCylinder_finset_real_eq_sum nu S Q, Finset.sum_mul_sum]

private theorem current_pairCorrelation_tendsto_of_approximations
    {E H : Type*} [Countable E] [Group H] [MulAction H E]
    (mu : Measure (InfiniteCurrentConfig E)) [IsProbabilityMeasure mu]
    (hti : CurrentIsTranslationInvariant (H := H) mu)
    (g : Nat -> H) (A B : Set (InfiniteCurrentConfig E))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (happrox : ∀ eta : Real, 0 < eta ->
      ∃ A0 B0 : Set (InfiniteCurrentConfig E),
        MeasurableSet A0 ∧ MeasurableSet B0 ∧
        mu.real (A ∆ A0) < eta ∧ mu.real (B ∆ B0) < eta ∧
        Tendsto (fun k => mu.real (A0 ∩ (currentShift (g k)) ⁻¹' B0))
          atTop (nhds (mu.real A0 * mu.real B0))) :
    Tendsto (fun k => mu.real (A ∩ (currentShift (g k)) ⁻¹' B))
      atTop (nhds (mu.real A * mu.real B)) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  let eta := epsilon / 16
  have heta : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨A0, B0, hA0, hB0, hAdiff, hBdiff, hcore⟩ := happrox eta heta
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp hcore) (epsilon / 4) (by positivity)
  refine ⟨K, ?_⟩
  intro k hk
  have hBshiftDiff : mu.real
      (((currentShift (g k)) ⁻¹' B) ∆ ((currentShift (g k)) ⁻¹' B0)) < eta := by
    rw [← Set.preimage_symmDiff]
    have hpre := (hti (g k)).measure_preimage
      ((hB.symmDiff hB0).nullMeasurableSet)
    rw [Measure.real, hpre]
    exact hBdiff
  have hinterSubset :
      (A ∩ (currentShift (g k)) ⁻¹' B) ∆
          (A0 ∩ (currentShift (g k)) ⁻¹' B0) ⊆
        (A ∆ A0) ∪
          (((currentShift (g k)) ⁻¹' B) ∆
            ((currentShift (g k)) ⁻¹' B0)) := by
    intro m hm
    rcases hm with ⟨hm, hm0⟩ | ⟨hm0, hm⟩
    · by_cases hmA0 : m ∈ A0
      · right
        exact Or.inl ⟨hm.2, fun hmB0 => hm0 ⟨hmA0, hmB0⟩⟩
      · left
        exact Or.inl ⟨hm.1, hmA0⟩
    · by_cases hmA : m ∈ A
      · right
        exact Or.inr ⟨hm0.2, fun hmB => hm ⟨hmA, hmB⟩⟩
      · left
        exact Or.inr ⟨hm0.1, hmA⟩
  have hinter : abs (mu.real (A ∩ (currentShift (g k)) ⁻¹' B) -
      mu.real (A0 ∩ (currentShift (g k)) ⁻¹' B0)) < 2 * eta := by
    calc
      abs (mu.real (A ∩ (currentShift (g k)) ⁻¹' B) -
          mu.real (A0 ∩ (currentShift (g k)) ⁻¹' B0)) ≤
          mu.real ((A ∩ (currentShift (g k)) ⁻¹' B) ∆
            (A0 ∩ (currentShift (g k)) ⁻¹' B0)) :=
        abs_measureReal_sub_le_measureReal_symmDiff
          (hA.inter (hB.preimage (measurable_currentShift (g k)))).nullMeasurableSet
          (hA0.inter (hB0.preimage (measurable_currentShift (g k)))).nullMeasurableSet
      _ ≤ mu.real ((A ∆ A0) ∪
          (((currentShift (g k)) ⁻¹' B) ∆
            ((currentShift (g k)) ⁻¹' B0))) :=
        measureReal_mono hinterSubset (by finiteness)
      _ ≤ mu.real (A ∆ A0) + mu.real
          (((currentShift (g k)) ⁻¹' B) ∆
            ((currentShift (g k)) ⁻¹' B0)) := measureReal_union_le _ _
      _ < 2 * eta := by linarith
  have hmassA : abs (mu.real A - mu.real A0) < eta :=
    (abs_measureReal_sub_le_measureReal_symmDiff
      hA.nullMeasurableSet hA0.nullMeasurableSet).trans_lt hAdiff
  have hmassB : abs (mu.real B - mu.real B0) < eta :=
    (abs_measureReal_sub_le_measureReal_symmDiff
      hB.nullMeasurableSet hB0.nullMeasurableSet).trans_lt hBdiff
  have hprod : abs (mu.real A * mu.real B - mu.real A0 * mu.real B0) <
      2 * eta := by
    calc
      abs (mu.real A * mu.real B - mu.real A0 * mu.real B0) =
          abs ((mu.real A - mu.real A0) * mu.real B +
            mu.real A0 * (mu.real B - mu.real B0)) := by ring_nf
      _ ≤ abs (mu.real A - mu.real A0) * abs (mu.real B) +
          abs (mu.real A0) * abs (mu.real B - mu.real B0) := by
        simpa [abs_mul] using abs_add_le
          ((mu.real A - mu.real A0) * mu.real B)
          (mu.real A0 * (mu.real B - mu.real B0))
      _ < eta * 1 + 1 * eta := by
        apply add_lt_add
        · exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos hmassA
            (by rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
            (abs_nonneg _) zero_lt_one
        · exact mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
            (by rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
            hmassB (abs_nonneg _) zero_lt_one
      _ = 2 * eta := by ring
  rw [Real.dist_eq]
  calc
    abs (mu.real (A ∩ (currentShift (g k)) ⁻¹' B) -
        mu.real A * mu.real B) ≤
      abs (mu.real (A ∩ (currentShift (g k)) ⁻¹' B) -
        mu.real (A0 ∩ (currentShift (g k)) ⁻¹' B0)) +
      (abs (mu.real (A0 ∩ (currentShift (g k)) ⁻¹' B0) -
        mu.real A0 * mu.real B0) +
      abs (mu.real A0 * mu.real B0 - mu.real A * mu.real B)) := by
        calc
          _ ≤ _ + abs (mu.real (A0 ∩ (currentShift (g k)) ⁻¹' B0) -
              mu.real A * mu.real B) := abs_sub_le _ _ _
          _ ≤ _ := add_le_add le_rfl (abs_sub_le _ _ _)
    _ < 2 * eta + (epsilon / 4 + 2 * eta) :=
      add_lt_add hinter (add_lt_add (hK k hk) (by simpa [abs_sub_comm] using hprod))
    _ < epsilon := by dsimp [eta]; linarith



theorem infinitePlusCurrentMeasure_latticeCylinder_axis_pairCorrelation_tendsto
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (A B : Set (↑S -> Nat)) :
    let nu := (infinitePlusCurrentMeasure d beta hbeta.le :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
    Tendsto (fun k : Nat => nu.real
        (currentCylinder S A ∩
          (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹'
            currentCylinder S B))
      atTop (nhds (nu.real (currentCylinder S A) *
        nu.real (currentCylinder S B))) := by
  classical
  dsimp only
  let prob := infinitePlusCurrentMeasure d beta hbeta.le
  let nu := (prob : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
  apply current_pairCorrelation_tendsto_of_approximations nu
    (infinitePlusCurrentMeasure_isTranslationInvariant d beta hbeta)
    (fun k => FK.freeAxisTranslationPower hd k)
    (currentCylinder S A) (currentCylinder S B)
    (measurableSet_currentCylinder S A) (measurableSet_currentCylinder S B)
  intro eta heta
  let p := (currentMarginal prob S : Measure (↑S -> Nat)).toPMF
  obtain ⟨K, hKtail⟩ := pmf_exists_finset_compl_toReal_lt p eta heta
  let KA := K.filter fun a => a ∈ A
  let KB := K.filter fun b => b ∈ B
  let A0 := currentCylinder S (↑KA : Set (↑S -> Nat))
  let B0 := currentCylinder S (↑KB : Set (↑S -> Nat))
  have hpmeasure : p.toMeasure =
      (currentMarginal prob S : Measure (↑S -> Nat)) := by
    dsimp [p]
    exact Measure.toPMF_toMeasure _
  have htail : nu.real (currentCylinder S (↑K : Set (↑S -> Nat))ᶜ) < eta := by
    change ENNReal.toReal
      (nu (currentCylinder S (↑K : Set (↑S -> Nat))ᶜ)) < eta
    rw [← currentMarginal_apply prob S (↑K : Set (↑S -> Nat))ᶜ,
      ← hpmeasure]
    exact hKtail
  have hAsub : (currentCylinder S A ∆ A0) ⊆
      currentCylinder S (↑K : Set (↑S -> Nat))ᶜ := by
    intro m hm
    rcases hm with ⟨hmA, hmA0⟩ | ⟨hmA0, hmA⟩
    · change restrictCurrent S m ∉ (↑K : Set (↑S -> Nat))
      intro hmK
      apply hmA0
      change restrictCurrent S m ∈ KA
      exact Finset.mem_filter.mpr ⟨hmK, hmA⟩
    · exfalso
      apply hmA
      have hmA0' : restrictCurrent S m ∈ KA := hmA0
      exact (Finset.mem_filter.mp hmA0').2
  have hBsub : (currentCylinder S B ∆ B0) ⊆
      currentCylinder S (↑K : Set (↑S -> Nat))ᶜ := by
    intro m hm
    rcases hm with ⟨hmB, hmB0⟩ | ⟨hmB0, hmB⟩
    · change restrictCurrent S m ∉ (↑K : Set (↑S -> Nat))
      intro hmK
      apply hmB0
      change restrictCurrent S m ∈ KB
      exact Finset.mem_filter.mpr ⟨hmK, hmB⟩
    · exfalso
      apply hmB
      have hmB0' : restrictCurrent S m ∈ KB := hmB0
      exact (Finset.mem_filter.mp hmB0').2
  refine ⟨A0, B0, measurableSet_currentCylinder S _,
    measurableSet_currentCylinder S _, ?_, ?_, ?_⟩
  · exact (measureReal_mono hAsub (by finiteness)).trans_lt htail
  · exact (measureReal_mono hBsub (by finiteness)).trans_lt htail
  · exact infinitePlusCurrentMeasure_finsetCylinder_axis_pairCorrelation_tendsto
      hd hbeta S hS KA KB



theorem infinitePlusCurrentMeasure_cylinder_axis_pairCorrelation_tendsto
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (C D : Set (InfiniteCurrentConfig (Sym2 (Site d))))
    (hC : C ∈ measurableCylinders (fun _ : Sym2 (Site d) => Nat))
    (hD : D ∈ measurableCylinders (fun _ : Sym2 (Site d) => Nat)) :
    let nu := (infinitePlusCurrentMeasure d beta hbeta.le :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
    Tendsto (fun k : Nat => nu.real
        (C ∩ (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹' D))
      atTop (nhds (nu.real C * nu.real D)) := by
  classical
  dsimp only
  let prob := infinitePlusCurrentMeasure d beta hbeta.le
  let nu := (prob : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
  let SC := MeasureTheory.measurableCylinders.finset hC
  let SD := MeasureTheory.measurableCylinders.finset hD
  let AC := MeasureTheory.measurableCylinders.set hC
  let AD := MeasureTheory.measurableCylinders.set hD
  let U := SC ∪ SD
  have hSCU : SC ⊆ U := Finset.subset_union_left
  have hSDU : SD ⊆ U := Finset.subset_union_right
  let CU : Set (↑U -> Nat) := liftCurrentPatternSet hSCU AC
  let DU : Set (↑U -> Nat) := liftCurrentPatternSet hSDU AD
  have hreprC : C = currentCylinder U CU := by
    calc
      C = currentCylinder SC AC := by
        simpa only [currentCylinder, restrictCurrent, MeasureTheory.cylinder,
          Finset.restrict] using
          (MeasureTheory.measurableCylinders.eq_cylinder hC)
      _ = currentCylinder U CU :=
        (currentCylinder_liftCurrentPatternSet hSCU AC).symm
  have hreprD : D = currentCylinder U DU := by
    calc
      D = currentCylinder SD AD := by
        simpa only [currentCylinder, restrictCurrent, MeasureTheory.cylinder,
          Finset.restrict] using
          (MeasureTheory.measurableCylinders.eq_cylinder hD)
      _ = currentCylinder U DU :=
        (currentCylinder_liftCurrentPatternSet hSDU AD).symm
  let L := latticeEdgePart d U
  have hL : (↑L : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet := latticeEdgePart_lattice d U
  let CR := currentCylinder L (latticeReducedPatternSet d U CU)
  let DR := currentCylinder L (latticeReducedPatternSet d U DU)
  have hzero : ∀ e, e ∉ (hypercubicLattice d).edgeSet ->
      nu {m | m e = 0} = 1 := by
    intro e he
    exact plusCurrentLimit_nonlattice_zero d beta hbeta.le e he
      (plusBoxCurrentMeasure_tendsto_infinitePlus d beta hbeta.le)
  have haeCU := currentCylinder_ae_eq_latticeReduction d prob U hzero CU
  have haeDU := currentCylinder_ae_eq_latticeReduction d prob U hzero DU
  have haeC : (fun m => m ∈ C) =ᵐ[nu] (fun m => m ∈ CR) := by
    filter_upwards [haeCU] with m hm
    rw [hreprC]
    simpa [CR, L] using hm
  have haeD : (fun m => m ∈ D) =ᵐ[nu] (fun m => m ∈ DR) := by
    filter_upwards [haeDU] with m hm
    rw [hreprD]
    simpa [DR, L] using hm
  have hmassC : nu.real C = nu.real CR := by
    unfold Measure.real
    exact congrArg ENNReal.toReal (measure_congr haeC)
  have hmassD : nu.real D = nu.real DR := by
    unfold Measure.real
    exact congrArg ENNReal.toReal (measure_congr haeD)
  have hcore :=
    infinitePlusCurrentMeasure_latticeCylinder_axis_pairCorrelation_tendsto
      hd hbeta L hL (latticeReducedPatternSet d U CU)
        (latticeReducedPatternSet d U DU)
  change Tendsto (fun k : Nat => nu.real
      (CR ∩ (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹' DR))
    atTop (nhds (nu.real CR * nu.real DR)) at hcore
  rw [← hmassC, ← hmassD] at hcore
  apply hcore.congr'
  filter_upwards with k
  have hti := infinitePlusCurrentMeasure_isTranslationInvariant d beta hbeta
  have haeDshift :=
    (hti (FK.freeAxisTranslationPower hd k)).quasiMeasurePreserving.ae_eq_comp haeD
  have haeJoint :
      (fun m => m ∈ C ∩
        (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹' D) =ᵐ[nu]
      (fun m => m ∈ CR ∩
        (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹' DR) := by
    filter_upwards [haeC, haeDshift] with m hmC hmD
    exact congrArg₂ And hmC hmD
  unfold Measure.real
  exact (congrArg ENNReal.toReal (measure_congr haeJoint)).symm

end StatMech.FrontierB
