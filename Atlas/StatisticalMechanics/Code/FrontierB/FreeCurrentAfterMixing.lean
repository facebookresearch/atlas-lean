/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.FreeCurrentFamilyMixing

open MeasureTheory Set
open scoped BigOperators ENNReal symmDiff

namespace StatMech.FrontierB

open Sharpness Ising Lattice
open StatMech.ConfigSpace StatMech.FK



theorem infiniteFreeCurrentMeasure_singleton_family_pairMixing_after
    {d : Nat} (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (K0 : Nat) (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (patterns : Finset (↑S → Nat))
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ k : Nat, K0 ≤ k ∧
      Disjoint S
        (currentShiftFinset (FK.freeAxisTranslationPower hd k) S) ∧
      ∀ a ∈ patterns, ∀ b ∈ patterns,
        abs ((infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
            (currentCylinder S {a} ∩
              (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹'
                currentCylinder S {b}) -
          (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
              (currentCylinder S {a}) *
            (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
              (currentCylinder S {b})) < epsilon := by
  classical
  let parityPatterns : Finset (↑S → Bool) :=
    patterns.image currentLocalParity
  obtain ⟨k, hk0, hdisj, hmix⟩ :=
    infiniteFreeCurrentMeasure_parityPattern_family_pairMixing_after
      hd hbeta K0 S hS parityPatterns epsilon hepsilon
  refine ⟨k, hk0, hdisj, ?_⟩
  intro a ha b hb
  let c := ENNReal.toReal
    (finiteParityPMF S beta hbeta (currentLocalParity a) a)
  let c' := ENNReal.toReal
    (finiteParityPMF S beta hbeta (currentLocalParity b) b)
  have hc : 0 ≤ c := ENNReal.toReal_nonneg
  have hc' : 0 ≤ c' := ENNReal.toReal_nonneg
  have hcle : c ≤ 1 := by
    dsimp [c]
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (finiteParityPMF S beta hbeta
        (currentLocalParity a)) a)
  have hc'le : c' ≤ 1 := by
    dsimp [c']
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (finiteParityPMF S beta hbeta
        (currentLocalParity b)) b)
  rw [infiniteFreeCurrentMeasure_singleton_inter_shift_real_eq hbeta
      (FK.freeAxisTranslationPower hd k) S S hS hS hdisj a b,
    infiniteFreeCurrentMeasure_singleton_real_eq hbeta S hS a,
    infiniteFreeCurrentMeasure_singleton_real_eq hbeta S hS b]
  let p := (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
    (currentParityPatternCylinder S (currentLocalParity a) ∩
      (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹'
        currentParityPatternCylinder S (currentLocalParity b))
  let q := (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
    (currentParityPatternCylinder S (currentLocalParity a))
  let r := (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
    (currentParityPatternCylinder S (currentLocalParity b))
  change abs (p * (c * c') - (q * c) * (r * c')) < epsilon
  have hfactor : p * (c * c') - (q * c) * (r * c') =
      (c * c') * (p - q * r) := by ring
  rw [hfactor, abs_mul, abs_of_nonneg (mul_nonneg hc hc')]
  calc
    c * c' * abs (p - q * r) ≤ 1 * abs (p - q * r) := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      nlinarith
    _ < epsilon := by
      simpa [p, q, r, parityPatterns] using
        hmix (currentLocalParity a)
          (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
          (currentLocalParity b)
          (Finset.mem_image.mpr ⟨b, hb, rfl⟩)




theorem current_pairGap_lt_of_approx
    {E H : Type*} [Countable E] [Group H] [MulAction H E]
    (mu : Measure (InfiniteCurrentConfig E)) [IsProbabilityMeasure mu]
    (hti : CurrentIsTranslationInvariant (H := H) mu) (g : H)
    {A A0 B B0 : Set (InfiniteCurrentConfig E)}
    (hA : MeasurableSet A) (hA0 : MeasurableSet A0)
    (hB : MeasurableSet B) (hB0 : MeasurableSet B0)
    {eta delta : Real}
    (hAapprox : mu.real (A ∆ A0) < eta)
    (hBapprox : mu.real (B ∆ B0) < eta)
    (hfinite : abs (mu.real (A0 ∩ (currentShift g) ⁻¹' B0) -
      mu.real A0 * mu.real B0) < delta) :
    abs (mu.real (A ∩ (currentShift g) ⁻¹' B) -
      mu.real A * mu.real B) < 4 * eta + delta := by
  have hBshiftApprox : mu.real
      (((currentShift g) ⁻¹' B) ∆ ((currentShift g) ⁻¹' B0)) < eta := by
    rw [← Set.preimage_symmDiff]
    have hpre := (hti g).measure_preimage
      ((hB.symmDiff hB0).nullMeasurableSet)
    rw [Measure.real, hpre]
    exact hBapprox
  have hinterSubset :
      (A ∩ (currentShift g) ⁻¹' B) ∆
          (A0 ∩ (currentShift g) ⁻¹' B0) ⊆
        (A ∆ A0) ∪
          (((currentShift g) ⁻¹' B) ∆
            ((currentShift g) ⁻¹' B0)) := by
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
  have hinter : abs (mu.real (A ∩ (currentShift g) ⁻¹' B) -
      mu.real (A0 ∩ (currentShift g) ⁻¹' B0)) < 2 * eta := by
    calc
      abs (mu.real (A ∩ (currentShift g) ⁻¹' B) -
          mu.real (A0 ∩ (currentShift g) ⁻¹' B0)) ≤
          mu.real ((A ∩ (currentShift g) ⁻¹' B) ∆
            (A0 ∩ (currentShift g) ⁻¹' B0)) :=
        abs_measureReal_sub_le_measureReal_symmDiff
          (hA.inter (hB.preimage (measurable_currentShift g))).nullMeasurableSet
          (hA0.inter (hB0.preimage (measurable_currentShift g))).nullMeasurableSet
      _ ≤ mu.real ((A ∆ A0) ∪
          (((currentShift g) ⁻¹' B) ∆
            ((currentShift g) ⁻¹' B0))) :=
        measureReal_mono hinterSubset (by finiteness)
      _ ≤ mu.real (A ∆ A0) +
          mu.real (((currentShift g) ⁻¹' B) ∆
            ((currentShift g) ⁻¹' B0)) := measureReal_union_le _ _
      _ < 2 * eta := by linarith
  have hAdiff : abs (mu.real A - mu.real A0) < eta :=
    (abs_measureReal_sub_le_measureReal_symmDiff
      hA.nullMeasurableSet hA0.nullMeasurableSet).trans_lt hAapprox
  have hBdiff : abs (mu.real B - mu.real B0) < eta :=
    (abs_measureReal_sub_le_measureReal_symmDiff
      hB.nullMeasurableSet hB0.nullMeasurableSet).trans_lt hBapprox
  have hprod : abs (mu.real A * mu.real B -
      mu.real A0 * mu.real B0) < 2 * eta := by
    have hBnonneg : 0 ≤ mu.real B := measureReal_nonneg
    have hA0nonneg : 0 ≤ mu.real A0 := measureReal_nonneg
    have hBle : mu.real B ≤ 1 := measureReal_le_one
    have hA0le : mu.real A0 ≤ 1 := measureReal_le_one
    calc
      abs (mu.real A * mu.real B - mu.real A0 * mu.real B0) =
          abs ((mu.real A - mu.real A0) * mu.real B +
            mu.real A0 * (mu.real B - mu.real B0)) := by ring_nf
      _ ≤ abs (mu.real A - mu.real A0) * abs (mu.real B) +
          abs (mu.real A0) * abs (mu.real B - mu.real B0) := by
        calc
          _ ≤ abs ((mu.real A - mu.real A0) * mu.real B) +
              abs (mu.real A0 * (mu.real B - mu.real B0)) :=
            abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul]
      _ < eta * 1 + 1 * eta := by
        rw [abs_of_nonneg hBnonneg, abs_of_nonneg hA0nonneg]
        exact add_lt_add
          (lt_of_le_of_lt
            (mul_le_mul_of_nonneg_left hBle (abs_nonneg _))
            (mul_lt_mul_of_pos_right hAdiff zero_lt_one))
          (lt_of_le_of_lt
            (mul_le_mul_of_nonneg_right hA0le (abs_nonneg _))
            (mul_lt_mul_of_pos_left hBdiff zero_lt_one))
      _ = 2 * eta := by ring
  have htriangle := abs_sub_le
    (mu.real (A ∩ (currentShift g) ⁻¹' B))
    (mu.real (A0 ∩ (currentShift g) ⁻¹' B0))
    (mu.real A * mu.real B)
  have htriangle' := abs_sub_le
    (mu.real (A0 ∩ (currentShift g) ⁻¹' B0))
    (mu.real A0 * mu.real B0) (mu.real A * mu.real B)
  calc
    abs (mu.real (A ∩ (currentShift g) ⁻¹' B) -
        mu.real A * mu.real B) ≤
      abs (mu.real (A ∩ (currentShift g) ⁻¹' B) -
        mu.real (A0 ∩ (currentShift g) ⁻¹' B0)) +
      abs (mu.real (A0 ∩ (currentShift g) ⁻¹' B0) -
        mu.real A * mu.real B) := htriangle
    _ ≤ abs (mu.real (A ∩ (currentShift g) ⁻¹' B) -
        mu.real (A0 ∩ (currentShift g) ⁻¹' B0)) +
      (abs (mu.real (A0 ∩ (currentShift g) ⁻¹' B0) -
        mu.real A0 * mu.real B0) +
       abs (mu.real A0 * mu.real B0 - mu.real A * mu.real B)) := by
      exact add_le_add le_rfl htriangle'
    _ < 2 * eta + (delta + 2 * eta) :=
      add_lt_add hinter (add_lt_add hfinite (by
        simpa only [abs_sub_comm] using hprod))
    _ = 4 * eta + delta := by ring



theorem infiniteFreeCurrentMeasure_latticeCylinder_family_pairMixing_after
    {d : Nat} (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (K0 : Nat) (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (accepted : Finset (Set (↑S → Nat)))
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ k : Nat, K0 ≤ k ∧
      ∀ A ∈ accepted, ∀ B ∈ accepted,
        abs ((infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
            (currentCylinder S A ∩
              (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹'
                currentCylinder S B) -
          (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
              (currentCylinder S A) *
            (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
              (currentCylinder S B)) < epsilon := by
  classical
  let prob := infiniteFreeCurrentMeasure d beta hbeta.le
  let mu := (prob : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
  let eta := epsilon / 16
  have heta : 0 < eta := by dsimp [eta]; positivity
  let p := (currentMarginal prob S : Measure (↑S → Nat)).toPMF
  obtain ⟨patterns, htailPatterns⟩ :=
    pmf_exists_finset_compl_toReal_lt p eta heta
  let delta := epsilon / 4 / ((patterns.card : Real) ^ 2 + 1)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨k, hk0, hdisj, hsingle⟩ :=
    infiniteFreeCurrentMeasure_singleton_family_pairMixing_after
      hd hbeta K0 S hS patterns delta hdelta
  refine ⟨k, hk0, ?_⟩
  have hti : CurrentIsTranslationInvariant
      (H := Multiplicative (Site d)) mu :=
    infiniteFreeCurrentMeasure_isTranslationInvariant d beta hbeta
  have hpmeasure : p.toMeasure =
      (currentMarginal prob S : Measure (↑S → Nat)) := by
    dsimp [p]
    exact Measure.toPMF_toMeasure _
  have htail :
      mu.real (currentCylinder S (↑patterns : Set (↑S → Nat))ᶜ) < eta := by
    change ENNReal.toReal
      (mu (currentCylinder S (↑patterns : Set (↑S → Nat))ᶜ)) < eta
    rw [← currentMarginal_apply prob S
        (↑patterns : Set (↑S → Nat))ᶜ,
      ← hpmeasure]
    exact htailPatterns
  intro A hA B hB
  let PA := patterns.filter fun a => a ∈ A
  let PB := patterns.filter fun b => b ∈ B
  let CA := currentCylinder S A
  let CB := currentCylinder S B
  let CA0 := currentCylinder S (↑PA : Set (↑S → Nat))
  let CB0 := currentCylinder S (↑PB : Set (↑S → Nat))
  let g := FK.freeAxisTranslationPower hd k
  have hfiniteRewrite :
      mu.real (CA0 ∩ (currentShift g) ⁻¹' CB0) -
          mu.real CA0 * mu.real CB0 =
        ∑ a ∈ PA, ∑ b ∈ PB,
          (mu.real (currentCylinder S {a} ∩
              (currentShift g) ⁻¹' currentCylinder S {b}) -
            mu.real (currentCylinder S {a}) *
              mu.real (currentCylinder S {b})) := by
    dsimp [CA0, CB0]
    rw [currentCylinder_finset_inter_shift_real_eq_sum mu g S PA PB,
      currentCylinder_finset_real_eq_sum mu S PA,
      currentCylinder_finset_real_eq_sum mu S PB,
      Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_sub_distrib]
  have hfinite : abs (mu.real (CA0 ∩ (currentShift g) ⁻¹' CB0) -
      mu.real CA0 * mu.real CB0) < epsilon / 4 := by
    rw [hfiniteRewrite]
    calc
      abs (∑ a ∈ PA, ∑ b ∈ PB,
          (mu.real (currentCylinder S {a} ∩
              (currentShift g) ⁻¹' currentCylinder S {b}) -
            mu.real (currentCylinder S {a}) *
              mu.real (currentCylinder S {b}))) ≤
          ∑ a ∈ PA, ∑ b ∈ PB,
            abs (mu.real (currentCylinder S {a} ∩
                (currentShift g) ⁻¹' currentCylinder S {b}) -
              mu.real (currentCylinder S {a}) *
                mu.real (currentCylinder S {b})) := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro a ha
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ PA, ∑ _b ∈ PB, delta := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        exact (hsingle a
          (Finset.mem_of_subset (Finset.filter_subset _ _) ha) b
          (Finset.mem_of_subset (Finset.filter_subset _ _) hb)).le
      _ = (PA.card : Real) * (PB.card : Real) * delta := by
        simp
        ring
      _ ≤ (patterns.card : Real) ^ 2 * delta := by
        apply mul_le_mul_of_nonneg_right _ hdelta.le
        have hPAcard : PA.card ≤ patterns.card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        have hPBcard : PB.card ≤ patterns.card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        have hPAreal : (PA.card : Real) ≤ patterns.card := by
          exact_mod_cast hPAcard
        have hPBreal : (PB.card : Real) ≤ patterns.card := by
          exact_mod_cast hPBcard
        nlinarith [mul_le_mul hPAreal hPBreal
          (Nat.cast_nonneg PB.card) (Nat.cast_nonneg patterns.card)]
      _ < epsilon / 4 := by
        dsimp [delta]
        have hbase : 0 < epsilon / 4 /
            ((patterns.card : Real) ^ 2 + 1) := by positivity
        calc
          (patterns.card : Real) ^ 2 *
              (epsilon / 4 / ((patterns.card : Real) ^ 2 + 1)) <
            ((patterns.card : Real) ^ 2 + 1) *
              (epsilon / 4 / ((patterns.card : Real) ^ 2 + 1)) := by
            apply mul_lt_mul_of_pos_right (by linarith) hbase
          _ = epsilon / 4 := by field_simp
  have hsymmA : CA ∆ CA0 ⊆
      currentCylinder S (↑patterns : Set (↑S → Nat))ᶜ := by
    intro m hm
    rcases hm with ⟨hmA, hmA0⟩ | ⟨hmA0, hmA⟩
    · change restrictCurrent S m ∉ (↑patterns : Set (↑S → Nat))
      intro hmP
      apply hmA0
      exact Finset.mem_filter.mpr ⟨hmP, hmA⟩
    · exfalso
      apply hmA
      exact (Finset.mem_filter.mp hmA0).2
  have hsymmB : CB ∆ CB0 ⊆
      currentCylinder S (↑patterns : Set (↑S → Nat))ᶜ := by
    intro m hm
    rcases hm with ⟨hmB, hmB0⟩ | ⟨hmB0, hmB⟩
    · change restrictCurrent S m ∉ (↑patterns : Set (↑S → Nat))
      intro hmP
      apply hmB0
      exact Finset.mem_filter.mpr ⟨hmP, hmB⟩
    · exfalso
      apply hmB
      exact (Finset.mem_filter.mp hmB0).2
  have hAapprox : mu.real (CA ∆ CA0) < eta :=
    (measureReal_mono hsymmA (by finiteness)).trans_lt htail
  have hBapprox : mu.real (CB ∆ CB0) < eta :=
    (measureReal_mono hsymmB (by finiteness)).trans_lt htail
  have hfinal := current_pairGap_lt_of_approx mu hti g
    (measurableSet_currentCylinder S A)
    (measurableSet_currentCylinder S (↑PA : Set (↑S → Nat)))
    (measurableSet_currentCylinder S B)
    (measurableSet_currentCylinder S (↑PB : Set (↑S → Nat)))
    hAapprox hBapprox hfinite
  change abs (mu.real (CA ∩ (currentShift g) ⁻¹' CB) -
    mu.real CA * mu.real CB) < epsilon
  exact hfinal.trans (by
    dsimp [eta]
    linarith)



theorem infiniteFreeCurrentMeasure_cylinderPairMixing_after
    {d : Nat} (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (K0 : Nat)
    (family : Finset
      (Set (InfiniteCurrentConfig (Sym2 (Site d)))))
    (hfamily : ∀ A ∈ family,
      A ∈ measurableCylinders (fun _ : Sym2 (Site d) => Nat))
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ k : Nat, K0 ≤ k ∧ ∀ A ∈ family, ∀ B ∈ family,
      abs ((infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
          (A ∩ (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹' B) -
        (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real A *
          (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real B) <
        epsilon := by
  classical
  let prob := infiniteFreeCurrentMeasure d beta hbeta.le
  let mu := (prob : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
  let members := family.attach
  let support : ↑family → Finset (Sym2 (Site d)) := fun C =>
    MeasureTheory.measurableCylinders.finset (hfamily C.1 C.2)
  let rawAccepted : (C : ↑family) → Set (↑(support C) → Nat) := fun C =>
    MeasureTheory.measurableCylinders.set (hfamily C.1 C.2)
  let U : Finset (Sym2 (Site d)) := members.biUnion support
  have hsupport (C : ↑family) : support C ⊆ U := by
    intro e he
    apply Finset.mem_biUnion.mpr
    exact ⟨C, Finset.mem_attach _ C, he⟩
  let liftedAccepted (C : ↑family) : Set (↑U → Nat) :=
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
      (hypercubicLattice d).edgeSet := latticeEdgePart_lattice d U
  let reducedAccepted (C : ↑family) : Set (↑L → Nat) :=
    latticeReducedPatternSet d U (liftedAccepted C)
  let reducedFamily : Finset (Set (↑L → Nat)) :=
    members.image reducedAccepted
  obtain ⟨k, hk0, hmix⟩ :=
    infiniteFreeCurrentMeasure_latticeCylinder_family_pairMixing_after
      hd hbeta K0 L hL reducedFamily epsilon hepsilon
  refine ⟨k, hk0, ?_⟩
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
  have hzero : ∀ e, e ∉ (hypercubicLattice d).edgeSet →
      mu {m | m e = 0} = 1 := by
    intro e he
    exact freeCurrentLimit_nonlattice_zero d beta hbeta.le e he
      (freeBoxCurrentMeasure_tendsto_infiniteFree d beta hbeta.le)
  have haeAU := currentCylinder_ae_eq_latticeReduction d prob U hzero
    (liftedAccepted a)
  have haeBU := currentCylinder_ae_eq_latticeReduction d prob U hzero
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
  let g := FK.freeAxisTranslationPower hd k
  have hti : CurrentIsTranslationInvariant
      (H := Multiplicative (Site d)) mu :=
    infiniteFreeCurrentMeasure_isTranslationInvariant d beta hbeta
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
    exact congrArg ENNReal.toReal (measure_congr haeA)
  have hmassB : mu.real B = mu.real BR := by
    unfold Measure.real
    exact congrArg ENNReal.toReal (measure_congr haeB)
  have hmassJoint : mu.real (A ∩ (currentShift g) ⁻¹' B) =
      mu.real (AR ∩ (currentShift g) ⁻¹' BR) := by
    unfold Measure.real
    exact congrArg ENNReal.toReal (measure_congr haeJoint)
  have hcore := hmix (reducedAccepted a) haReduced
    (reducedAccepted b) hbReduced
  change abs (mu.real (A ∩ (currentShift g) ⁻¹' B) -
    mu.real A * mu.real B) < epsilon
  rw [hmassA, hmassB, hmassJoint]
  simpa [AR, BR, mu, L, g] using hcore

end StatMech.FrontierB
