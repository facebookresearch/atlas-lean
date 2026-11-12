/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierB.FreeBoxEvenLimit
import Code.Ising.IsingPlusTIFromPlacement

open MeasureTheory Filter Topology
open scoped BigOperators

namespace StatMech.FrontierB

open Ising Lattice Sharpness


abbrev freeDomainVertices {d : Nat} (K : Finset (Site d)) :=
  {x : Site d // x ∈ K}

noncomputable instance freeDomainVerticesFintype {d : Nat}
    (K : Finset (Site d)) : Fintype (freeDomainVertices K) :=
  K.finite_toSet.fintype


def freeDomainGraph {d : Nat} (K : Finset (Site d)) :
    SimpleGraph (freeDomainVertices K) :=
  (hypercubicLattice d).comap Subtype.val

noncomputable instance freeDomainGraphDecidableAdj {d : Nat}
    (K : Finset (Site d)) : DecidableRel (freeDomainGraph K).Adj :=
  Classical.decRel _


noncomputable def freeDomainSpinSupport {d : Nat}
    (K A : Finset (Site d)) : Finset (freeDomainVertices K) :=
  Finset.univ.filter fun x => x.1 ∈ A

theorem freeDomainSpinSupport_image {d : Nat}
    (K A : Finset (Site d)) (hA : A ⊆ K) :
    (freeDomainSpinSupport K A).image Subtype.val = A := by
  ext x
  constructor
  · rintro hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa [freeDomainSpinSupport] using hy
  · intro hx
    rw [Finset.mem_image]
    exact ⟨⟨x, hA hx⟩, by simp [freeDomainSpinSupport, hx], rfl⟩



noncomputable def freeDomainInclusionEquiv {d : Nat}
    {K L : Finset (Site d)} (hKL : K ⊆ L) :
    freeDomainVertices K ≃
      {z : freeDomainVertices L // z.1 ∈ K} where
  toFun x := ⟨⟨x.1, hKL x.2⟩, x.2⟩
  invFun z := ⟨z.1.1, z.2⟩
  left_inv x := by ext; rfl
  right_inv z := by ext; rfl

theorem freeDomainInclusionEquiv_adj {d : Nat}
    {K L : Finset (Site d)} (hKL : K ⊆ L)
    (x y : freeDomainVertices K) :
    (freeDomainGraph K).Adj x y ↔
      ((freeDomainGraph L).comap
        (Subtype.val : {z : freeDomainVertices L // z.1 ∈ K} ->
          freeDomainVertices L)).Adj
        (freeDomainInclusionEquiv hKL x)
        (freeDomainInclusionEquiv hKL y) := by
  rfl

theorem freeDomainSpinSupport_map_inclusion {d : Nat}
    {K L : Finset (Site d)} (hKL : K ⊆ L)
    (A : Finset (Site d)) (hA : A ⊆ K) :
    ((freeDomainSpinSupport K A).map
      (freeDomainInclusionEquiv hKL).toEmbedding).map
      (Function.Embedding.subtype (fun z : freeDomainVertices L => z.1 ∈ K)) =
        freeDomainSpinSupport L A := by
  ext z
  simp only [Finset.mem_map, freeDomainSpinSupport, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    exact hx
  · intro hz
    let x : freeDomainVertices K := ⟨z.1, hA hz⟩
    let w : {z : freeDomainVertices L // z.1 ∈ K} :=
      freeDomainInclusionEquiv hKL x
    refine ⟨w, ⟨x, ?_, rfl⟩, ?_⟩
    · exact hz
    · apply Subtype.ext
      rfl


theorem freeDomain_spinProd_mono {d : Nat}
    {K L : Finset (Site d)} (hKL : K ⊆ L)
    (beta : Real) (hbeta : 0 <= beta)
    (A : Finset (Site d)) (hA : A ⊆ K) :
    isingExpectation (freeDomainGraph K) beta 0
        (spinProd (freeDomainSpinSupport K A)) <=
      isingExpectation (freeDomainGraph L) beta 0
        (spinProd (freeDomainSpinSupport L A)) := by
  let e := freeDomainInclusionEquiv hKL
  calc
    isingExpectation (freeDomainGraph K) beta 0
        (spinProd (freeDomainSpinSupport K A)) =
      isingExpectation
        ((freeDomainGraph L).comap
          (Subtype.val : {z : freeDomainVertices L // z.1 ∈ K} ->
            freeDomainVertices L)) beta 0
        (spinProd ((freeDomainSpinSupport K A).map e.toEmbedding)) := by
      exact isingExpectation_spinProd_relabel (freeDomainGraph K)
        ((freeDomainGraph L).comap
          (Subtype.val : {z : freeDomainVertices L // z.1 ∈ K} ->
            freeDomainVertices L)) e
        (freeDomainInclusionEquiv_adj hKL) beta 0 _
    _ <= isingExpectation (freeDomainGraph L) beta 0
        (spinProd (((freeDomainSpinSupport K A).map e.toEmbedding).map
          (Function.Embedding.subtype
            (fun z : freeDomainVertices L => z.1 ∈ K)))) :=
      isingExpectation_spinProd_induce_le (freeDomainGraph L)
        (fun z : freeDomainVertices L => z.1 ∈ K)
        beta 0 hbeta le_rfl _
    _ = isingExpectation (freeDomainGraph L) beta 0
        (spinProd (freeDomainSpinSupport L A)) := by
      rw [freeDomainSpinSupport_map_inclusion hKL A hA]


noncomputable def freeDomainTranslateEquiv {d : Nat}
    (g : Multiplicative (Site d)) (K : Finset (Site d)) :
    freeDomainVertices K ≃ freeDomainVertices (K.image fun x => g • x) :=
  iptp_transInteriorEquiv g K

theorem freeDomainTranslateEquiv_adj {d : Nat}
    (g : Multiplicative (Site d)) (K : Finset (Site d))
    (x y : freeDomainVertices K) :
    (freeDomainGraph K).Adj x y ↔
      (freeDomainGraph (K.image fun z => g • z)).Adj
        (freeDomainTranslateEquiv g K x)
        (freeDomainTranslateEquiv g K y) := by
  change (hypercubicLattice d).Adj x.1 y.1 ↔
    (hypercubicLattice d).Adj (g • x.1) (g • y.1)
  exact (Percolation.hyper_adj_smul g x.1 y.1).symm

theorem freeDomainSpinSupport_map_translate {d : Nat}
    (g : Multiplicative (Site d)) (K A : Finset (Site d)) :
    (freeDomainSpinSupport K A).map
        (freeDomainTranslateEquiv g K).toEmbedding =
      freeDomainSpinSupport (K.image fun x => g • x)
        (A.image fun x => g • x) := by
  ext z
  simp only [Finset.mem_map, freeDomainSpinSupport, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Finset.mem_image_of_mem _ hx
  · intro hz
    rw [Finset.mem_image] at hz
    obtain ⟨a, ha, haz⟩ := hz
    let x : freeDomainVertices K :=
      ⟨g⁻¹ • z.1, by
        obtain ⟨k, hk, hkz⟩ := Finset.mem_image.mp z.2
        rw [← hkz, inv_smul_smul]
        exact hk⟩
    refine ⟨x, ?_, ?_⟩
    · change g⁻¹ • z.1 ∈ A
      rw [← haz, inv_smul_smul]
      exact ha
    · apply Subtype.ext
      change g • (g⁻¹ • z.1) = z.1
      rw [smul_inv_smul]



theorem freeDomain_spinProd_translate {d : Nat}
    (g : Multiplicative (Site d)) (K A : Finset (Site d))
    (beta : Real) :
    isingExpectation (freeDomainGraph (K.image fun x => g • x)) beta 0
        (spinProd (freeDomainSpinSupport
          (K.image fun x => g • x) (A.image fun x => g • x))) =
      isingExpectation (freeDomainGraph K) beta 0
        (spinProd (freeDomainSpinSupport K A)) := by
  symm
  rw [isingExpectation_spinProd_relabel (freeDomainGraph K)
    (freeDomainGraph (K.image fun x => g • x))
    (freeDomainTranslateEquiv g K)
    (freeDomainTranslateEquiv_adj g K) beta 0
    (freeDomainSpinSupport K A)]
  rw [freeDomainSpinSupport_map_translate]


theorem freeDomainGraph_box_relabel (d n : Nat) (beta : Real)
    (A : Finset (Site d)) :
    isingExpectation (freeDomainGraph (boxFinset d n)) beta 0
        (spinProd (freeDomainSpinSupport (boxFinset d n) A)) =
      isingExpectation (sctBoxGraph d n) beta 0
        (spinProd (boxSpinSupport d n A)) := by
  let e := (iptp_boxEquiv d n).symm
  rw [isingExpectation_spinProd_relabel
    (freeDomainGraph (boxFinset d n)) (sctBoxGraph d n) e]
  · congr 2
    ext x
    simp only [Finset.mem_map, freeDomainSpinSupport, boxSpinSupport,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, hax⟩
      have hval := congrArg Subtype.val hax
      simpa [e, iptp_boxEquiv] using hval ▸ ha
    · intro hx
      refine ⟨iptp_boxEquiv d n x, ?_, ?_⟩
      · simpa [iptp_boxEquiv] using hx
      · exact (iptp_boxEquiv d n).symm_apply_apply x
  · intro x y
    rfl



theorem integral_freeMeasure_spinProd_eq_freeDomain
    (d n : Nat) (beta : Real) (A : Finset (Site d))
    (hA : A ⊆ boxFinset d n) :
    (∫ omega, spinProd A omega
        ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) =
      isingExpectation (freeDomainGraph (boxFinset d n)) beta 0
        (spinProd (freeDomainSpinSupport (boxFinset d n) A)) := by
  rw [integral_freeMeasure_spinProd d n beta 0 A]
  · exact (freeDomainGraph_box_relabel d n beta A).symm
  · intro x hx
    exact mem_boxFinset.mp (hA hx)



theorem integral_freeState_spinProd_translate
    (d : Nat) (beta : Real) (hbeta : 0 <= beta)
    (g : Multiplicative (Site d)) (A : Finset (Site d)) :
    (∫ omega, spinProd (A.image fun x => g • x) omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) =
      ∫ omega, spinProd A omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
  let c := StatMech.FK.flc_vrad (Multiplicative.toAdd g)
  obtain ⟨N, hAN⟩ := finite_subset_box
    (↑A : Set (Site d)) A.finite_toSet
  have hAbox (k : Nat) : A ⊆ boxFinset d (k + N) := by
    intro x hx
    rw [mem_boxFinset]
    exact box_mono d (Nat.le_add_left N k) (hAN hx)
  let lower : Nat -> Real := fun k =>
    ∫ omega, spinProd A omega
      ∂(freeMeasure d (k + N) beta 0 : Measure (ConfigSpace (Site d)))
  let middle : Nat -> Real := fun k =>
    ∫ omega, spinProd (A.image fun x => g • x) omega
      ∂(freeMeasure d (k + N + c) beta 0 : Measure (ConfigSpace (Site d)))
  let upper : Nat -> Real := fun k =>
    ∫ omega, spinProd A omega
      ∂(freeMeasure d (k + N + 2 * c) beta 0 : Measure (ConfigSpace (Site d)))
  have hlower : Tendsto lower atTop
      (nhds (∫ omega, spinProd A omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) := by
    simpa [lower, Nat.add_comm] using
      (integral_freeMeasure_spinProd_tendsto_freeState d beta hbeta A).comp
        (tendsto_add_atTop_nat N)
  have hmiddle : Tendsto middle atTop
      (nhds (∫ omega, spinProd (A.image fun x => g • x) omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) := by
    have hfull := integral_freeMeasure_spinProd_tendsto_freeState d beta hbeta
      (A.image fun x => g • x)
    have hadd := hfull.comp (tendsto_add_atTop_nat (N + c))
    simpa [middle, Nat.add_assoc] using hadd
  have hupper : Tendsto upper atTop
      (nhds (∫ omega, spinProd A omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) := by
    have hfull := integral_freeMeasure_spinProd_tendsto_freeState d beta hbeta A
    have hadd := hfull.comp (tendsto_add_atTop_nat (N + 2 * c))
    simpa [upper, Nat.add_assoc] using hadd
  have hsqueeze : ∀ k, lower k <= middle k ∧ middle k <= upper k := by
    intro k
    let K0 := boxFinset d (k + N)
    let K1 := boxFinset d (k + N + c)
    let K2 := boxFinset d (k + N + 2 * c)
    let gK0 := K0.image fun x => g • x
    let gK2 := K2.image fun x => g • x
    let gA := A.image fun x => g • x
    have hAgK0 : gA ⊆ gK0 := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image_of_mem _ (hAbox k hx)
    have hgK0K1 : gK0 ⊆ K1 := by
      exact (iptp_transBox_subset_box g (k + N)).trans
        (by simpa [K1, c, Nat.add_assoc] using
          (Finset.Subset.rfl : boxFinset d (k + N + c) ⊆
            boxFinset d (k + N + c)))
    have hK1gK2 : K1 ⊆ gK2 := by
      apply iptp_box_subset_transBox g
      dsimp [K1, K2, c]
      omega
    have hAgK2 : gA ⊆ gK2 :=
      hAgK0.trans (hgK0K1.trans hK1gK2)
    have hAK2 : A ⊆ K2 := by
      exact (hAbox k).trans (by
        intro x hx
        rw [mem_boxFinset] at hx ⊢
        exact box_mono d (by omega) hx)
    have hl := freeDomain_spinProd_mono hgK0K1 beta hbeta gA hAgK0
    have hu := freeDomain_spinProd_mono hK1gK2 beta hbeta gA
      (hAgK0.trans hgK0K1)
    have htrans0 := freeDomain_spinProd_translate g K0 A beta
    have htrans2 := freeDomain_spinProd_translate g K2 A beta
    have hmidDomain := integral_freeMeasure_spinProd_eq_freeDomain
      d (k + N + c) beta gA (hAgK0.trans hgK0K1)
    have hlowDomain := integral_freeMeasure_spinProd_eq_freeDomain
      d (k + N) beta A (hAbox k)
    have huppDomain := integral_freeMeasure_spinProd_eq_freeDomain
      d (k + N + 2 * c) beta A hAK2
    constructor
    · simpa [lower, middle, K0, K1, gK0, gA,
        hlowDomain, hmidDomain, htrans0] using hl
    · simpa [middle, upper, K1, K2, gK2, gA,
        hmidDomain, huppDomain, htrans2] using hu
  apply le_antisymm
  · exact le_of_tendsto_of_tendsto hmiddle hupper
      (Filter.Eventually.of_forall fun k => (hsqueeze k).2)
  · exact le_of_tendsto_of_tendsto hlower hmiddle
      (Filter.Eventually.of_forall fun k => (hsqueeze k).1)



theorem spinProd_shift {d : Nat}
    (g : Multiplicative (Site d)) (A : Finset (Site d))
    (omega : ConfigSpace (Site d)) :
    spinProd A (ConfigSpace.shift g omega) =
      spinProd (A.image fun x => g⁻¹ • x) omega := by
  unfold spinProd
  rw [Finset.prod_image (fun x _ y _ hxy => MulAction.injective g⁻¹ hxy)]
  apply Finset.prod_congr rfl
  intro x hx
  unfold spin ConfigSpace.shift
  rfl



theorem fmu_moInd_eq_spinProd_sum {d : Nat}
    (T : Finset (Site d)) (omega : ConfigSpace (Site d)) :
    StatMech.FK.fmu_moInd T omega =
      (1 / 2 : Real) ^ T.card *
        ∑ U ∈ T.powerset, spinProd U omega := by
  unfold StatMech.FK.fmu_moInd StatMech.FK.fmu_xR
  have hcoord (x : Site d) :
      (if omega x then (1 : Real) else 0) =
        (1 / 2 : Real) * (spin omega x + 1) := by
    cases h : omega x <;> norm_num [spin, h]
  simp_rw [hcoord]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_add]
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  simp [spinProd]



theorem integral_freeState_moInd_shift
    (d : Nat) (beta : Real) (hbeta : 0 <= beta)
    (g : Multiplicative (Site d)) (T : Finset (Site d)) :
    (∫ omega, StatMech.FK.fmu_moInd T (ConfigSpace.shift g omega)
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) =
      ∫ omega, StatMech.FK.fmu_moInd T omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
  simp_rw [fmu_moInd_eq_spinProd_sum T]
  rw [integral_const_mul, integral_const_mul]
  congr 1
  rw [integral_finsetSum, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro U hU
    simp_rw [spinProd_shift g U]
    exact integral_freeState_spinProd_translate d beta hbeta g⁻¹ U
  · intro U hU
    exact (spinProdBCF d U).integrable _
  · intro U hU
    simp_rw [spinProd_shift g U]
    exact (spinProdBCF d (U.image fun x => g⁻¹ • x)).integrable _



theorem freeState_multiOpen_preimage_eq
    (d : Nat) (beta : Real) (hbeta : 0 <= beta)
    (g : Multiplicative (Site d)) (T : Finset (Site d)) :
    (freeState d beta 0 : Measure (ConfigSpace (Site d))).real
        ((ConfigSpace.shift g) ⁻¹' StatMech.FK.fmu_multiOpen T) =
      (freeState d beta 0 : Measure (ConfigSpace (Site d))).real
        (StatMech.FK.fmu_multiOpen T) := by
  have hleft :
      (freeState d beta 0 : Measure (ConfigSpace (Site d))).real
          ((ConfigSpace.shift g) ⁻¹' StatMech.FK.fmu_multiOpen T) =
        ∫ omega, StatMech.FK.fmu_moInd T (ConfigSpace.shift g omega)
          ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
    simp_rw [StatMech.FK.fmu_moInd_comp_shift]
    rw [MeasureTheory.integral_indicator_const (1 : Real)]
    · simp
    · exact (StatMech.FK.fmu_multiOpen_measurable T).preimage
        (ConfigSpace.measurable_shift g)
  rw [hleft, integral_freeState_moInd_shift d beta hbeta g T,
    StatMech.FK.fmu_integral_moInd]


theorem freeState_isTranslationInvariant
    (d : Nat) (beta : Real) (hbeta : 0 <= beta) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
  intro g
  refine ⟨ConfigSpace.measurable_shift g, ?_⟩
  apply ext_of_generate_finite
    (measurableCylinders (fun _ : Site d => Bool))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro C hC
    have hCmeas : MeasurableSet C :=
      MeasurableSet.of_mem_measurableCylinders hC
    obtain ⟨P, coeff, hexp⟩ := StatMech.FK.fmu_cylinder_expand C hC
    have hreal :
        (freeState d beta 0 : Measure (ConfigSpace (Site d))).real
            ((ConfigSpace.shift g) ⁻¹' C) =
          (freeState d beta 0 : Measure (ConfigSpace (Site d))).real C := by
      rw [show
          (freeState d beta 0 : Measure (ConfigSpace (Site d))).real
              ((ConfigSpace.shift g) ⁻¹' C) =
            ∫ omega, C.indicator (fun _ => (1 : Real))
              (ConfigSpace.shift g omega)
              ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) by
        have hind (omega : ConfigSpace (Site d)) :
            C.indicator (fun _ => (1 : Real)) (ConfigSpace.shift g omega) =
              ((ConfigSpace.shift g) ⁻¹' C).indicator
                (fun _ => (1 : Real)) omega :=
          (Set.indicator_comp_right (s := C)
            (f := ConfigSpace.shift g) (g := fun _ => (1 : Real))
            (x := omega)).symm
        simp_rw [hind]
        rw [MeasureTheory.integral_indicator_const (1 : Real)]
        · simp
        · exact hCmeas.preimage (ConfigSpace.measurable_shift g)]
      simp_rw [hexp]
      rw [integral_finsetSum]
      · rw [StatMech.FK.fmu_real_eq_sum hCmeas P coeff hexp]
        apply Finset.sum_congr rfl
        intro T hT
        rw [integral_const_mul,
          integral_freeState_moInd_shift d beta hbeta g T,
          StatMech.FK.fmu_integral_moInd]
      · intro T hT
        have hi : Integrable
            (fun omega => StatMech.FK.fmu_moInd T
              (ConfigSpace.shift g omega))
            (freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
          simp_rw [StatMech.FK.fmu_moInd_comp_shift]
          exact (MeasureTheory.integrable_const (1 : Real)).indicator
            ((StatMech.FK.fmu_multiOpen_measurable T).preimage
              (ConfigSpace.measurable_shift g))
        exact hi.const_mul _
    rw [Measure.map_apply (ConfigSpace.measurable_shift g) hCmeas]
    apply (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top _ _) (measure_ne_top _ _)).mp
    simpa [Measure.real] using hreal
  · rw [Measure.map_apply (ConfigSpace.measurable_shift g) MeasurableSet.univ]
    simp

end StatMech.FrontierB
