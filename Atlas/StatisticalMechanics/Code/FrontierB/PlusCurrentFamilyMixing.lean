/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierB.PlusCurrentSingletonMixing

open MeasureTheory Set
open scoped BigOperators ENNReal symmDiff

namespace StatMech.FrontierB

open Sharpness Ising Lattice
open StatMech.ConfigSpace StatMech.FK



theorem infinitePlusCurrentMeasure_parityPattern_family_pairMixing {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (patterns : Finset (↑S -> Bool))
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ g : Multiplicative (Site d),
      Disjoint S (currentShiftFinset g S) ∧
      ∀ odd ∈ patterns, ∀ odd' ∈ patterns,
        abs ((infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
            (currentParityPatternCylinder S odd ∩
              (currentShift g) ⁻¹' currentParityPatternCylinder S odd') -
          (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
              (currentParityPatternCylinder S odd) *
            (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
              (currentParityPatternCylinder S odd')) < epsilon := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let IS := plusParityExpansionIndices S
  let sentinel : PlusParityExpansionIndex d :=
    ⟨∅, ⟨∅, edgeVertexSupport S⟩⟩
  let indices := insert sentinel IS
  let patternCoeff : (↑S -> Bool) -> PlusParityExpansionIndex d -> Real :=
    fun odd i => if i ∈ IS then plusParityExpansionCoeff beta S odd i else 0
  let coeffs : Finset (PlusParityExpansionIndex d -> Real) :=
    patterns.image patternCoeff
  let mu := (plusState d beta 0 : Measure (ConfigSpace (Site d)))
  have hti : IsTranslationInvariant (G := Multiplicative (Site d)) mu :=
    iptp_plusState_isTranslationInvariant hbeta.le le_rfl
  have hpair : fmu_PairMixing (G := Multiplicative (Site d)) mu :=
    ipe_plusState_pairMixing_of_upperDecay hbeta.le 0 hti
      (icb_plusState_upperDecay hd hbeta.le le_rfl hti)
  obtain ⟨g, hdisj, hcorr⟩ := fmu_finsetExpansion_family_pairMixing
    (fun x y => siteTranslation_solution_finite x y) hti hpair indices
      plusParityExpansionSupport coeffs epsilon hepsilon
  have hIS : IS ⊆ indices := by
    intro i hi
    simp [indices, hi]
  have hSdiag : ∀ e ∈ S, ¬ e.IsDiag := by
    intro e he
    exact (hypercubicLattice d).not_isDiag_of_mem_edgeSet (hS he)
  have hsentinel : sentinel ∈ indices := by simp [indices]
  have hvertices : Disjoint (edgeVertexSupport S)
      ((edgeVertexSupport S).image (fun x => g⁻¹ • x)) := by
    simpa [sentinel, plusParityExpansionSupport] using
      hdisj sentinel hsentinel sentinel hsentinel
  have hedges : Disjoint S (currentShiftFinset g S) := by
    rw [Finset.disjoint_left]
    intro e heS heShift
    rw [currentShiftFinset, Finset.mem_image] at heShift
    obtain ⟨e', heS', heq⟩ := heShift
    have hxS' : e'.out.1 ∈ edgeVertexSupport S :=
      mem_edgeVertexSupport_of_mem_edge heS' (Sym2.out_fst_mem e')
    have hxedge : g⁻¹ • e'.out.1 ∈ g⁻¹ • e' := by
      change g⁻¹ • e'.out.1 ∈ Sym2.map (fun x => g⁻¹ • x) e'
      exact Sym2.mem_map.mpr ⟨e'.out.1, Sym2.out_fst_mem e', rfl⟩
    rw [heq] at hxedge
    have hxS : g⁻¹ • e'.out.1 ∈ edgeVertexSupport S :=
      mem_edgeVertexSupport_of_mem_edge heS hxedge
    exact (Finset.disjoint_left.mp hvertices hxS)
      (Finset.mem_image.mpr ⟨e'.out.1, hxS', rfl⟩)
  refine ⟨g, hedges, ?_⟩
  intro odd hodd odd' hodd'
  have hc : patternCoeff odd ∈ coeffs :=
    Finset.mem_image.mpr ⟨odd, hodd, rfl⟩
  have hc' : patternCoeff odd' ∈ coeffs :=
    Finset.mem_image.mpr ⟨odd', hodd', rfl⟩
  have hleftPoint (omega : ConfigSpace (Site d)) :
      (∑ i ∈ indices,
          patternCoeff odd i * fmu_moInd (plusParityExpansionSupport i) omega) =
        plusParityPatternSpinPolynomial beta S odd omega := by
    calc
      (∑ i ∈ indices,
          patternCoeff odd i * fmu_moInd (plusParityExpansionSupport i) omega) =
          ∑ i ∈ IS,
            patternCoeff odd i * fmu_moInd (plusParityExpansionSupport i) omega := by
              refine (Finset.sum_subset hIS (fun i hiIndices hiIS => ?_)).symm
              simp [patternCoeff, hiIS]
      _ = ∑ i ∈ plusParityExpansionIndices S,
          plusParityExpansionCoeff beta S odd i *
            fmu_moInd (plusParityExpansionSupport i) omega := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [patternCoeff, IS, hi]
      _ = plusParityPatternSpinPolynomial beta S odd omega :=
        (plusParityPatternSpinPolynomial_eq_multiOpenExpansion
          beta S odd hSdiag omega).symm
  have hrightPoint (omega : ConfigSpace (Site d)) :
      (∑ i ∈ indices,
          patternCoeff odd' i * fmu_moInd (plusParityExpansionSupport i) omega) =
        plusParityPatternSpinPolynomial beta S odd' omega := by
    calc
      (∑ i ∈ indices,
          patternCoeff odd' i * fmu_moInd (plusParityExpansionSupport i) omega) =
          ∑ i ∈ IS,
            patternCoeff odd' i * fmu_moInd (plusParityExpansionSupport i) omega := by
              refine (Finset.sum_subset hIS (fun i hiIndices hiIS => ?_)).symm
              simp [patternCoeff, hiIS]
      _ = ∑ i ∈ plusParityExpansionIndices S,
          plusParityExpansionCoeff beta S odd' i *
            fmu_moInd (plusParityExpansionSupport i) omega := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [patternCoeff, IS, hi]
      _ = plusParityPatternSpinPolynomial beta S odd' omega :=
        (plusParityPatternSpinPolynomial_eq_multiOpenExpansion
          beta S odd' hSdiag omega).symm
  have hleftMass :
      (∑ i ∈ indices, patternCoeff odd i *
          mu.real (fmu_multiOpen (plusParityExpansionSupport i))) =
        ∫ omega, plusParityPatternSpinPolynomial beta S odd omega ∂mu := by
    calc
      (∑ i ∈ indices, patternCoeff odd i *
          mu.real (fmu_multiOpen (plusParityExpansionSupport i))) =
          ∑ i ∈ IS, patternCoeff odd i *
            mu.real (fmu_multiOpen (plusParityExpansionSupport i)) := by
              refine (Finset.sum_subset hIS (fun i hiIndices hiIS => ?_)).symm
              simp [patternCoeff, hiIS]
      _ = ∑ i ∈ plusParityExpansionIndices S,
          plusParityExpansionCoeff beta S odd i *
            mu.real (fmu_multiOpen (plusParityExpansionSupport i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [patternCoeff, IS, hi]
      _ = ∫ omega, plusParityPatternSpinPolynomial beta S odd omega ∂mu :=
        (integral_plusParityPatternSpinPolynomial_eq_multiOpenExpansion
          mu beta S odd hSdiag).symm
  have hrightMass :
      (∑ i ∈ indices, patternCoeff odd' i *
          mu.real (fmu_multiOpen (plusParityExpansionSupport i))) =
        ∫ omega, plusParityPatternSpinPolynomial beta S odd' omega ∂mu := by
    calc
      (∑ i ∈ indices, patternCoeff odd' i *
          mu.real (fmu_multiOpen (plusParityExpansionSupport i))) =
          ∑ i ∈ IS, patternCoeff odd' i *
            mu.real (fmu_multiOpen (plusParityExpansionSupport i)) := by
              refine (Finset.sum_subset hIS (fun i hiIndices hiIS => ?_)).symm
              simp [patternCoeff, hiIS]
      _ = ∑ i ∈ plusParityExpansionIndices S,
          plusParityExpansionCoeff beta S odd' i *
            mu.real (fmu_multiOpen (plusParityExpansionSupport i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [patternCoeff, IS, hi]
      _ = ∫ omega, plusParityPatternSpinPolynomial beta S odd' omega ∂mu :=
        (integral_plusParityPatternSpinPolynomial_eq_multiOpenExpansion
          mu beta S odd' hSdiag).symm
  rw [infinitePlusCurrentMeasure_parityPattern_inter_shift_real_eq_integral
      hbeta g S S odd odd' hS hS hedges,
    infinitePlusCurrentMeasure_parityPattern_real_eq_integral hbeta S odd hS,
    infinitePlusCurrentMeasure_parityPattern_real_eq_integral hbeta S odd' hS]
  simpa only [hleftPoint, hrightPoint, hleftMass, hrightMass, mu] using
    hcorr (patternCoeff odd) hc (patternCoeff odd') hc'



theorem infinitePlusCurrentMeasure_singleton_family_pairMixing {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (patterns : Finset (↑S -> Nat))
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ g : Multiplicative (Site d),
      Disjoint S (currentShiftFinset g S) ∧
      ∀ a ∈ patterns, ∀ b ∈ patterns,
        abs ((infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
            (currentCylinder S {a} ∩
              (currentShift g) ⁻¹' currentCylinder S {b}) -
          (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
              (currentCylinder S {a}) *
            (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
              (currentCylinder S {b})) < epsilon := by
  classical
  let parityPatterns : Finset (↑S -> Bool) := patterns.image currentLocalParity
  obtain ⟨g, hdisj, hmix⟩ :=
    infinitePlusCurrentMeasure_parityPattern_family_pairMixing hd hbeta S hS
      parityPatterns epsilon hepsilon
  refine ⟨g, hdisj, ?_⟩
  intro a ha b hb
  let k := ENNReal.toReal
    (finiteParityPMF S beta hbeta (currentLocalParity a) a)
  let k' := ENNReal.toReal
    (finiteParityPMF S beta hbeta (currentLocalParity b) b)
  have hk : 0 ≤ k := ENNReal.toReal_nonneg
  have hk' : 0 ≤ k' := ENNReal.toReal_nonneg
  have hkle : k ≤ 1 := by
    dsimp [k]
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (finiteParityPMF S beta hbeta (currentLocalParity a)) a)
  have hk'le : k' ≤ 1 := by
    dsimp [k']
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (finiteParityPMF S beta hbeta (currentLocalParity b)) b)
  rw [infinitePlusCurrentMeasure_singleton_inter_shift_real_eq hbeta g S S
      hS hS hdisj a b,
    infinitePlusCurrentMeasure_singleton_real_eq hbeta S hS a,
    infinitePlusCurrentMeasure_singleton_real_eq hbeta S hS b]
  let p := (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
    (currentParityPatternCylinder S (currentLocalParity a) ∩
      (currentShift g) ⁻¹'
        currentParityPatternCylinder S (currentLocalParity b))
  let q := (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
    (currentParityPatternCylinder S (currentLocalParity a))
  let r := (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
    (currentParityPatternCylinder S (currentLocalParity b))
  change abs (p * (k * k') - (q * k) * (r * k')) < epsilon
  have hfactor : p * (k * k') - (q * k) * (r * k') =
      (k * k') * (p - q * r) := by ring
  rw [hfactor, abs_mul, abs_of_nonneg (mul_nonneg hk hk')]
  calc
    k * k' * abs (p - q * r) ≤ 1 * abs (p - q * r) := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      nlinarith
    _ < epsilon := by
      simpa [p, q, r, parityPatterns] using
        hmix (currentLocalParity a)
          (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
          (currentLocalParity b)
          (Finset.mem_image.mpr ⟨b, hb, rfl⟩)



theorem pmf_exists_finset_compl_toReal_lt {A : Type*} [Countable A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p : PMF A) (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ K : Finset A,
      ENNReal.toReal (p.toMeasure (↑K : Set A)ᶜ) < epsilon := by
  have htend := ENNReal.tendsto_tsum_compl_atTop_zero p.tsum_coe_ne_top
  have hnhds : {x : ENNReal | x < ENNReal.ofReal epsilon} ∈
      nhds (0 : ENNReal) := by
    exact Iio_mem_nhds (by simpa using hepsilon)
  obtain ⟨K, hK⟩ := (htend.eventually hnhds).exists
  refine ⟨K, ?_⟩
  have hmeasure : p.toMeasure (↑K : Set A)ᶜ =
      ∑' x : {x // x ∉ K}, p x := by
    rw [PMF.toMeasure_apply_eq_tsum]
    simpa using (tsum_subtype ((↑K : Set A)ᶜ) (p : A -> ENNReal)).symm
  rw [hmeasure]
  have hne : (∑' x : {x // x ∉ K}, p x) ≠ ⊤ :=
    lt_top_iff_ne_top.mp (hK.trans_le (by simp))
  have hreal :=
    (ENNReal.toReal_lt_toReal hne ENNReal.ofReal_ne_top).2 hK
  rwa [ENNReal.toReal_ofReal hepsilon.le] at hreal



theorem currentCylinder_finset_real_eq_sum {E : Type*} [Countable E]
    (mu : Measure (InfiniteCurrentConfig E)) [IsFiniteMeasure mu]
    (S : Finset E) (P : Finset (↑S -> Nat)) :
    mu.real (currentCylinder S (↑P : Set (↑S -> Nat))) =
      ∑ a ∈ P, mu.real (currentCylinder S {a}) := by
  have hset : currentCylinder S (↑P : Set (↑S -> Nat)) =
      ⋃ a ∈ P, currentCylinder S {a} := by
    ext m
    simp [currentCylinder]
  rw [hset, measureReal_biUnion_finset]
  · intro a ha b hb hab
    change Disjoint (currentCylinder S {a}) (currentCylinder S {b})
    rw [Set.disjoint_left]
    intro m hma hmb
    apply hab
    simpa [currentCylinder] using hma.symm.trans hmb
  · intro a ha
    exact measurableSet_currentCylinder S {a}



theorem currentCylinder_finset_inter_shift_real_eq_sum
    {E H : Type*} [Countable E] [Group H] [MulAction H E]
    (mu : Measure (InfiniteCurrentConfig E)) [IsFiniteMeasure mu]
    (g : H) (S : Finset E) (P Q : Finset (↑S -> Nat)) :
    mu.real (currentCylinder S (↑P : Set (↑S -> Nat)) ∩
        (currentShift g) ⁻¹' currentCylinder S (↑Q : Set (↑S -> Nat))) =
      ∑ a ∈ P, ∑ b ∈ Q,
        mu.real (currentCylinder S {a} ∩
          (currentShift g) ⁻¹' currentCylinder S {b}) := by
  have hset : currentCylinder S (↑P : Set (↑S -> Nat)) ∩
      (currentShift g) ⁻¹' currentCylinder S (↑Q : Set (↑S -> Nat)) =
      ⋃ a ∈ P, ⋃ b ∈ Q,
        (currentCylinder S {a} ∩
          (currentShift g) ⁻¹' currentCylinder S {b}) := by
    ext m
    simp [currentCylinder]
  have houter : Set.PairwiseDisjoint (↑P)
      (fun a => ⋃ b ∈ Q, currentCylinder S {a} ∩
        (currentShift g) ⁻¹' currentCylinder S {b}) := by
    intro a ha a' ha' haa'
    change Disjoint
      (⋃ b ∈ Q, currentCylinder S {a} ∩
        (currentShift g) ⁻¹' currentCylinder S {b})
      (⋃ b ∈ Q, currentCylinder S {a'} ∩
        (currentShift g) ⁻¹' currentCylinder S {b})
    rw [Set.disjoint_left]
    intro m hma hma'
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage] at hma hma'
    obtain ⟨b, hb, hleft, hright⟩ := hma
    obtain ⟨b', hb', hleft', hright'⟩ := hma'
    apply haa'
    simpa [currentCylinder] using hleft.symm.trans hleft'
  have houterMeas : ∀ a ∈ P, MeasurableSet
      (⋃ b ∈ Q, currentCylinder S {a} ∩
        (currentShift g) ⁻¹' currentCylinder S {b}) := by
    intro a ha
    apply MeasurableSet.biUnion Q.countable_toSet
    intro b hb
    exact (measurableSet_currentCylinder S {a}).inter
      ((measurableSet_currentCylinder S {b}).preimage
        (measurable_currentShift g))
  rw [hset, measureReal_biUnion_finset houter houterMeas
    (fun a ha => measure_ne_top mu _)]
  apply Finset.sum_congr rfl
  intro a ha
  have hinner : Set.PairwiseDisjoint (↑Q)
      (fun b => currentCylinder S {a} ∩
        (currentShift g) ⁻¹' currentCylinder S {b}) := by
    intro b hb b' hb' hbb'
    change Disjoint
      (currentCylinder S {a} ∩
        (currentShift g) ⁻¹' currentCylinder S {b})
      (currentCylinder S {a} ∩
        (currentShift g) ⁻¹' currentCylinder S {b'})
    rw [Set.disjoint_left]
    intro m hmb hmb'
    apply hbb'
    have hright := hmb.2
    have hright' := hmb'.2
    simpa [currentCylinder] using hright.symm.trans hright'
  have hinnerMeas : ∀ b ∈ Q, MeasurableSet
      (currentCylinder S {a} ∩
        (currentShift g) ⁻¹' currentCylinder S {b}) := by
    intro b hb
    exact (measurableSet_currentCylinder S {a}).inter
      ((measurableSet_currentCylinder S {b}).preimage
        (measurable_currentShift g))
  rw [measureReal_biUnion_finset hinner hinnerMeas
    (fun b hb => measure_ne_top mu _)]



theorem infinitePlusCurrentMeasure_latticeCylinder_family_pairMixing {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (accepted : Finset (Set (↑S -> Nat)))
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ g : Multiplicative (Site d),
      ∀ A ∈ accepted, ∀ B ∈ accepted,
        abs ((infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
            (currentCylinder S A ∩
              (currentShift g) ⁻¹' currentCylinder S B) -
          (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
              (currentCylinder S A) *
            (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
              (currentCylinder S B)) < epsilon := by
  classical
  let nu := infinitePlusCurrentMeasure d beta hbeta.le
  let mu := (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
  let eta := epsilon / 16
  have heta : 0 < eta := by dsimp [eta]; positivity
  let p := (currentMarginal nu S : Measure (↑S -> Nat)).toPMF
  obtain ⟨K, hKtail⟩ := pmf_exists_finset_compl_toReal_lt p eta heta
  let delta := epsilon / ((K.card : Real) ^ 2 + 1) / 8
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  obtain ⟨g, hdisj, hsingle⟩ :=
    infinitePlusCurrentMeasure_singleton_family_pairMixing hd hbeta S hS K
      delta hdelta
  have hti : CurrentIsTranslationInvariant
      (H := Multiplicative (Site d)) mu :=
    infinitePlusCurrentMeasure_isTranslationInvariant d beta hbeta
  have hpmeasure : p.toMeasure =
      (currentMarginal nu S : Measure (↑S -> Nat)) := by
    dsimp [p]
    exact Measure.toPMF_toMeasure _
  have htail : mu.real (currentCylinder S (↑K : Set (↑S -> Nat))ᶜ) < eta := by
    change ENNReal.toReal (mu (currentCylinder S (↑K : Set (↑S -> Nat))ᶜ)) < eta
    rw [← currentMarginal_apply nu S (↑K : Set (↑S -> Nat))ᶜ,
      ← hpmeasure]
    exact hKtail
  refine ⟨g, ?_⟩
  intro A hA B hB
  let KA := K.filter fun a => a ∈ A
  let KB := K.filter fun b => b ∈ B
  let CA := currentCylinder S A
  let CB := currentCylinder S B
  let CA0 := currentCylinder S (↑KA : Set (↑S -> Nat))
  let CB0 := currentCylinder S (↑KB : Set (↑S -> Nat))
  have hfiniteRewrite :
      mu.real (CA0 ∩ (currentShift g) ⁻¹' CB0) -
          mu.real CA0 * mu.real CB0 =
        ∑ a ∈ KA, ∑ b ∈ KB,
          (mu.real (currentCylinder S {a} ∩
              (currentShift g) ⁻¹' currentCylinder S {b}) -
            mu.real (currentCylinder S {a}) *
              mu.real (currentCylinder S {b})) := by
    dsimp [CA0, CB0]
    rw [currentCylinder_finset_inter_shift_real_eq_sum mu g S KA KB,
      currentCylinder_finset_real_eq_sum mu S KA,
      currentCylinder_finset_real_eq_sum mu S KB,
      Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_sub_distrib]
  have hfinite : abs (mu.real (CA0 ∩ (currentShift g) ⁻¹' CB0) -
      mu.real CA0 * mu.real CB0) < epsilon / 8 := by
    rw [hfiniteRewrite]
    calc
      abs (∑ a ∈ KA, ∑ b ∈ KB,
          (mu.real (currentCylinder S {a} ∩
              (currentShift g) ⁻¹' currentCylinder S {b}) -
            mu.real (currentCylinder S {a}) *
              mu.real (currentCylinder S {b}))) ≤
          ∑ a ∈ KA, ∑ b ∈ KB,
            abs (mu.real (currentCylinder S {a} ∩
                (currentShift g) ⁻¹' currentCylinder S {b}) -
              mu.real (currentCylinder S {a}) *
                mu.real (currentCylinder S {b})) := by
            apply (Finset.abs_sum_le_sum_abs _ _).trans
            apply Finset.sum_le_sum
            intro a ha
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ KA, ∑ b ∈ KB, delta := by
            apply Finset.sum_le_sum
            intro a ha
            apply Finset.sum_le_sum
            intro b hb
            exact (hsingle a (Finset.mem_of_subset (Finset.filter_subset _ _) ha)
              b (Finset.mem_of_subset (Finset.filter_subset _ _) hb)).le
      _ = (KA.card : Real) * (KB.card : Real) * delta := by
            simp
            ring
      _ ≤ (K.card : Real) ^ 2 * delta := by
            apply mul_le_mul_of_nonneg_right _ hdelta.le
            have hKAcard : KA.card ≤ K.card :=
              Finset.card_le_card (Finset.filter_subset _ _)
            have hKBcard : KB.card ≤ K.card :=
              Finset.card_le_card (Finset.filter_subset _ _)
            have hKAreal : (KA.card : Real) ≤ K.card := by exact_mod_cast hKAcard
            have hKBreal : (KB.card : Real) ≤ K.card := by exact_mod_cast hKBcard
            nlinarith [mul_le_mul hKAreal hKBreal
              (Nat.cast_nonneg KB.card) (Nat.cast_nonneg K.card)]
      _ < epsilon / 8 := by
            dsimp [delta]
            have hbase : 0 < epsilon / ((K.card : Real) ^ 2 + 1) := by
              positivity
            calc
              (K.card : Real) ^ 2 *
                    (epsilon / ((K.card : Real) ^ 2 + 1) / 8) <
                  ((K.card : Real) ^ 2 + 1) *
                    (epsilon / ((K.card : Real) ^ 2 + 1) / 8) := by
                      apply mul_lt_mul_of_pos_right (by linarith)
                      positivity
              _ = epsilon / 8 := by
                    field_simp
  have hsymmA : CA ∆ CA0 ⊆
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
      exact (Finset.mem_filter.mp hmA0).2
  have hsymmB : CB ∆ CB0 ⊆
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
      exact (Finset.mem_filter.mp hmB0).2
  have hCAmeas : MeasurableSet CA := by
    exact measurableSet_currentCylinder S A
  have hCBmeas : MeasurableSet CB := by
    exact measurableSet_currentCylinder S B
  have hCA0meas : MeasurableSet CA0 := by
    exact measurableSet_currentCylinder S (↑KA : Set (↑S -> Nat))
  have hCB0meas : MeasurableSet CB0 := by
    exact measurableSet_currentCylinder S (↑KB : Set (↑S -> Nat))
  have hAapprox : mu.real (CA ∆ CA0) < eta :=
    (measureReal_mono hsymmA (by finiteness)).trans_lt htail
  have hBapprox : mu.real (CB ∆ CB0) < eta :=
    (measureReal_mono hsymmB (by finiteness)).trans_lt htail
  have hBshiftApprox : mu.real
      (((currentShift g) ⁻¹' CB) ∆ ((currentShift g) ⁻¹' CB0)) < eta := by
    rw [← Set.preimage_symmDiff]
    have hpre := (hti g).measure_preimage
      ((hCBmeas.symmDiff hCB0meas).nullMeasurableSet)
    rw [Measure.real, hpre]
    exact hBapprox
  have hinterSubset :
      (CA ∩ (currentShift g) ⁻¹' CB) ∆
          (CA0 ∩ (currentShift g) ⁻¹' CB0) ⊆
        (CA ∆ CA0) ∪
          (((currentShift g) ⁻¹' CB) ∆ ((currentShift g) ⁻¹' CB0)) := by
    intro m hm
    rcases hm with ⟨hm, hm0⟩ | ⟨hm0, hm⟩
    · by_cases hmCA0 : m ∈ CA0
      · right
        exact Or.inl ⟨hm.2, fun hmCB0 => hm0 ⟨hmCA0, hmCB0⟩⟩
      · left
        exact Or.inl ⟨hm.1, hmCA0⟩
    · by_cases hmCA : m ∈ CA
      · right
        exact Or.inr ⟨hm0.2, fun hmCB => hm ⟨hmCA, hmCB⟩⟩
      · left
        exact Or.inr ⟨hm0.1, hmCA⟩
  have hinter : abs (mu.real (CA ∩ (currentShift g) ⁻¹' CB) -
      mu.real (CA0 ∩ (currentShift g) ⁻¹' CB0)) < 2 * eta := by
    calc
      abs (mu.real (CA ∩ (currentShift g) ⁻¹' CB) -
          mu.real (CA0 ∩ (currentShift g) ⁻¹' CB0)) ≤
          mu.real ((CA ∩ (currentShift g) ⁻¹' CB) ∆
            (CA0 ∩ (currentShift g) ⁻¹' CB0)) :=
        abs_measureReal_sub_le_measureReal_symmDiff
          (hCAmeas.inter (hCBmeas.preimage (measurable_currentShift g))).nullMeasurableSet
          (hCA0meas.inter (hCB0meas.preimage (measurable_currentShift g))).nullMeasurableSet
      _ ≤ mu.real ((CA ∆ CA0) ∪
          (((currentShift g) ⁻¹' CB) ∆ ((currentShift g) ⁻¹' CB0))) :=
        measureReal_mono hinterSubset (by finiteness)
      _ ≤ mu.real (CA ∆ CA0) +
          mu.real (((currentShift g) ⁻¹' CB) ∆
            ((currentShift g) ⁻¹' CB0)) := measureReal_union_le _ _
      _ < 2 * eta := by linarith
  have hAdiff : abs (mu.real CA - mu.real CA0) < eta :=
    (abs_measureReal_sub_le_measureReal_symmDiff
      hCAmeas.nullMeasurableSet hCA0meas.nullMeasurableSet).trans_lt hAapprox
  have hBdiff : abs (mu.real CB - mu.real CB0) < eta :=
    (abs_measureReal_sub_le_measureReal_symmDiff
      hCBmeas.nullMeasurableSet hCB0meas.nullMeasurableSet).trans_lt hBapprox
  have hprod : abs (mu.real CA * mu.real CB -
      mu.real CA0 * mu.real CB0) < 2 * eta := by
    have hCBnonneg : 0 ≤ mu.real CB := measureReal_nonneg
    have hCA0nonneg : 0 ≤ mu.real CA0 := measureReal_nonneg
    have hCBle : mu.real CB ≤ 1 := measureReal_le_one
    have hCA0le : mu.real CA0 ≤ 1 := measureReal_le_one
    calc
      abs (mu.real CA * mu.real CB - mu.real CA0 * mu.real CB0) =
          abs ((mu.real CA - mu.real CA0) * mu.real CB +
            mu.real CA0 * (mu.real CB - mu.real CB0)) := by ring_nf
      _ ≤ abs (mu.real CA - mu.real CA0) * abs (mu.real CB) +
          abs (mu.real CA0) * abs (mu.real CB - mu.real CB0) := by
            calc
              _ ≤ abs ((mu.real CA - mu.real CA0) * mu.real CB) +
                  abs (mu.real CA0 * (mu.real CB - mu.real CB0)) :=
                abs_add_le _ _
              _ = _ := by rw [abs_mul, abs_mul]
      _ < eta * 1 + 1 * eta := by
            rw [abs_of_nonneg hCBnonneg, abs_of_nonneg hCA0nonneg]
            exact add_lt_add
              (lt_of_le_of_lt
                (mul_le_mul_of_nonneg_left hCBle (abs_nonneg _))
                (mul_lt_mul_of_pos_right hAdiff zero_lt_one))
              (lt_of_le_of_lt
                (mul_le_mul_of_nonneg_right hCA0le (abs_nonneg _))
                (mul_lt_mul_of_pos_left hBdiff zero_lt_one))
      _ = 2 * eta := by ring
  have htriangle : abs (mu.real (CA ∩ (currentShift g) ⁻¹' CB) -
      mu.real CA * mu.real CB) ≤
      abs (mu.real (CA ∩ (currentShift g) ⁻¹' CB) -
        mu.real (CA0 ∩ (currentShift g) ⁻¹' CB0)) +
      (abs (mu.real (CA0 ∩ (currentShift g) ⁻¹' CB0) -
        mu.real CA0 * mu.real CB0) +
      abs (mu.real CA0 * mu.real CB0 - mu.real CA * mu.real CB)) := by
    calc
      abs (mu.real (CA ∩ (currentShift g) ⁻¹' CB) -
          mu.real CA * mu.real CB) ≤
          abs (mu.real (CA ∩ (currentShift g) ⁻¹' CB) -
            mu.real (CA0 ∩ (currentShift g) ⁻¹' CB0)) +
          abs (mu.real (CA0 ∩ (currentShift g) ⁻¹' CB0) -
            mu.real CA * mu.real CB) := abs_sub_le _ _ _
      _ ≤ _ := by
        exact add_le_add le_rfl (abs_sub_le _ _ _)
  change abs (mu.real (CA ∩ (currentShift g) ⁻¹' CB) -
    mu.real CA * mu.real CB) < epsilon
  calc
    abs (mu.real (CA ∩ (currentShift g) ⁻¹' CB) -
        mu.real CA * mu.real CB) ≤ _ := htriangle
    _ < 2 * eta + (epsilon / 8 + 2 * eta) := by
      exact add_lt_add hinter (add_lt_add hfinite (by simpa [abs_sub_comm] using hprod))
    _ < epsilon := by
      dsimp [eta]
      linarith



noncomputable def extendLatticeLocalPattern (d : Nat)
    (S : Finset (Sym2 (Site d)))
    (a : ↑(latticeEdgePart d S) -> Nat) : ↑S -> Nat :=
  fun e => if he : e.1 ∈ latticeEdgePart d S then a ⟨e.1, he⟩ else 0



noncomputable def latticeReducedPatternSet (d : Nat)
    (S : Finset (Sym2 (Site d))) (A : Set (↑S -> Nat)) :
    Set (↑(latticeEdgePart d S) -> Nat) :=
  {a | extendLatticeLocalPattern d S a ∈ A}

theorem restrictCurrent_eq_extendLatticeLocalPattern
    (d : Nat) (S : Finset (Sym2 (Site d)))
    (m : InfiniteCurrentConfig (Sym2 (Site d)))
    (hm : ∀ e ∈ S, e ∉ (hypercubicLattice d).edgeSet -> m e = 0) :
    restrictCurrent S m =
      extendLatticeLocalPattern d S
        (restrictCurrent (latticeEdgePart d S) m) := by
  funext e
  by_cases he : e.1 ∈ latticeEdgePart d S
  · simp [extendLatticeLocalPattern, he, restrictCurrent]
  · have hnonlattice : e.1 ∉ (hypercubicLattice d).edgeSet := by
      intro helattice
      exact he (Finset.mem_filter.mpr ⟨e.2, helattice⟩)
    simp [extendLatticeLocalPattern, he, restrictCurrent, hm e.1 e.2 hnonlattice]



theorem currentCylinder_ae_eq_latticeReduction
    (d : Nat)
    (mu : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))))
    (S : Finset (Sym2 (Site d)))
    (hzero : ∀ e, e ∉ (hypercubicLattice d).edgeSet ->
      (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | m e = 0} = 1)
    (A : Set (↑S -> Nat)) :
    (fun m => m ∈ currentCylinder S A) =ᵐ[(mu : Measure _)]
      (fun m => m ∈ currentCylinder (latticeEdgePart d S)
        (latticeReducedPatternSet d S A)) := by
  have hae := ae_nonlattice_zero_on_finset d mu S hzero
  filter_upwards [hae] with m hm
  apply propext
  change restrictCurrent S m ∈ A ↔
    restrictCurrent (latticeEdgePart d S) m ∈
      latticeReducedPatternSet d S A
  rw [restrictCurrent_eq_extendLatticeLocalPattern d S m hm]
  rfl



def liftCurrentPatternSet {E : Type*} {S U : Finset E} (hSU : S ⊆ U)
    (A : Set (↑S -> Nat)) : Set (↑U -> Nat) :=
  {a | Finset.restrict₂ (π := fun _ : E => Nat) hSU a ∈ A}

theorem currentCylinder_liftCurrentPatternSet {E : Type*}
    {S U : Finset E} (hSU : S ⊆ U) (A : Set (↑S -> Nat)) :
    currentCylinder U (liftCurrentPatternSet hSU A) = currentCylinder S A := by
  ext m
  change Finset.restrict₂ (π := fun _ : E => Nat) hSU
      (restrictCurrent U m) ∈ A ↔ restrictCurrent S m ∈ A
  rw [restrictCurrent_restrict₂ hSU]



theorem infinitePlusCurrentMeasure_cylinderPairMixing {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta) :
    CurrentCylinderPairMixing (H := Multiplicative (Site d))
      (infinitePlusCurrentMeasure d beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d)))) := by
  classical
  let nu := infinitePlusCurrentMeasure d beta hbeta.le
  let mu := (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
  intro family hfamily epsilon hepsilon
  let members := family.attach
  let support : ↑family -> Finset (Sym2 (Site d)) := fun C =>
    MeasureTheory.measurableCylinders.finset (hfamily C.1 C.2)
  let rawAccepted : (C : ↑family) -> Set (↑(support C) -> Nat) := fun C =>
    MeasureTheory.measurableCylinders.set (hfamily C.1 C.2)
  let U : Finset (Sym2 (Site d)) := members.biUnion support
  have hsupport (C : ↑family) : support C ⊆ U := by
    intro e he
    apply Finset.mem_biUnion.mpr
    exact ⟨C, Finset.mem_attach _ C, he⟩
  let liftedAccepted (C : ↑family) : Set (↑U -> Nat) :=
    liftCurrentPatternSet (hsupport C) (rawAccepted C)
  have hrepr (C : ↑family) : C.1 =
      currentCylinder (support C) (rawAccepted C) := by
    simpa only [currentCylinder, restrictCurrent, MeasureTheory.cylinder,
      Finset.restrict] using
      (MeasureTheory.measurableCylinders.eq_cylinder (hfamily C.1 C.2))
  have hreprU (C : ↑family) : C.1 =
      currentCylinder U (liftedAccepted C) := by
    calc
      C.1 = currentCylinder (support C) (rawAccepted C) := hrepr C
      _ = currentCylinder U (liftedAccepted C) :=
        (currentCylinder_liftCurrentPatternSet
          (hsupport C) (rawAccepted C)).symm
  let L := latticeEdgePart d U
  have hL : (↑L : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet := by
    exact latticeEdgePart_lattice d U
  let reducedAccepted (C : ↑family) : Set (↑L -> Nat) :=
    latticeReducedPatternSet d U (liftedAccepted C)
  let reducedFamily : Finset (Set (↑L -> Nat)) :=
    members.image reducedAccepted
  obtain ⟨g, hmix⟩ :=
    infinitePlusCurrentMeasure_latticeCylinder_family_pairMixing hd hbeta
      L hL reducedFamily epsilon hepsilon
  refine ⟨g, ?_⟩
  intro A hA B hB
  let a : ↑family := ⟨A, hA⟩
  let b : ↑family := ⟨B, hB⟩
  have haMember : a ∈ members := Finset.mem_attach _ a
  have hbMember : b ∈ members := Finset.mem_attach _ b
  have haReduced : reducedAccepted a ∈ reducedFamily :=
    Finset.mem_image.mpr ⟨a, haMember, rfl⟩
  have hbReduced : reducedAccepted b ∈ reducedFamily :=
    Finset.mem_image.mpr ⟨b, hbMember, rfl⟩
  let AR := currentCylinder L (reducedAccepted a)
  let BR := currentCylinder L (reducedAccepted b)
  have hzero : ∀ e, e ∉ (hypercubicLattice d).edgeSet ->
      mu {m | m e = 0} = 1 := by
    intro e he
    exact plusCurrentLimit_nonlattice_zero d beta hbeta.le e he
      (plusBoxCurrentMeasure_tendsto_infinitePlus d beta hbeta.le)
  have haeAU := currentCylinder_ae_eq_latticeReduction d nu U hzero
    (liftedAccepted a)
  have haeBU := currentCylinder_ae_eq_latticeReduction d nu U hzero
    (liftedAccepted b)
  have hreprA : A = currentCylinder U (liftedAccepted a) := by
    simpa [a] using hreprU a
  have hreprB : B = currentCylinder U (liftedAccepted b) := by
    simpa [b] using hreprU b
  have haeA : (fun m => m ∈ A) =ᵐ[mu] (fun m => m ∈ AR) := by
    filter_upwards [haeAU] with m hm
    rw [hreprA]
    simpa [AR, L, reducedAccepted] using hm
  have haeB : (fun m => m ∈ B) =ᵐ[mu] (fun m => m ∈ BR) := by
    filter_upwards [haeBU] with m hm
    rw [hreprB]
    simpa [BR, L, reducedAccepted] using hm
  have hti : CurrentIsTranslationInvariant
      (H := Multiplicative (Site d)) mu :=
    infinitePlusCurrentMeasure_isTranslationInvariant d beta hbeta
  have haeBshift := (hti g).quasiMeasurePreserving.ae_eq_comp haeB
  have haeJoint :
      (fun m => m ∈ A ∩ (currentShift g) ⁻¹' B) =ᵐ[mu]
        (fun m => m ∈ AR ∩ (currentShift g) ⁻¹' BR) := by
    filter_upwards [haeA, haeBshift] with m hmA hmB
    change ((m ∈ A) ∧ currentShift g m ∈ B) =
      ((m ∈ AR) ∧ currentShift g m ∈ BR)
    exact congrArg₂ And hmA hmB
  have hmassA : mu.real A = mu.real AR := by
    unfold Measure.real
    exact congrArg ENNReal.toReal
      (measure_congr (μ := mu) (s := A) (t := AR) haeA)
  have hmassB : mu.real B = mu.real BR := by
    unfold Measure.real
    exact congrArg ENNReal.toReal
      (measure_congr (μ := mu) (s := B) (t := BR) haeB)
  have hmassJoint :
      mu.real (A ∩ (currentShift g) ⁻¹' B) =
        mu.real (AR ∩ (currentShift g) ⁻¹' BR) := by
    unfold Measure.real
    exact congrArg ENNReal.toReal
      (measure_congr (μ := mu)
        (s := A ∩ (currentShift g) ⁻¹' B)
        (t := AR ∩ (currentShift g) ⁻¹' BR) haeJoint)
  have hcore := hmix (reducedAccepted a) haReduced
    (reducedAccepted b) hbReduced
  change abs (mu.real (A ∩ (currentShift g) ⁻¹' B) -
    mu.real A * mu.real B) < epsilon
  rw [hmassA, hmassB, hmassJoint]
  simpa [AR, BR, mu, L] using hcore



theorem infinitePlusCurrentMeasure_isErgodic {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta) :
    CurrentIsErgodic (H := Multiplicative (Site d))
      (infinitePlusCurrentMeasure d beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d)))) :=
  current_isErgodic_of_cylinderPairMixing
    (infinitePlusCurrentMeasure_isTranslationInvariant d beta hbeta)
    (infinitePlusCurrentMeasure_cylinderPairMixing hd hbeta)

end StatMech.FrontierB
