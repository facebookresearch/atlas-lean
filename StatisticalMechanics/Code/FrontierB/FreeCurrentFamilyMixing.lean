/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.FreeCurrentParityMixing
import Code.FrontierB.PlusCurrentFamilyMixing

open MeasureTheory Set
open scoped BigOperators ENNReal symmDiff

namespace StatMech.FrontierB

open Sharpness Ising Lattice
open StatMech.ConfigSpace StatMech.FK

theorem infiniteFreeCurrentMeasure_singleton_real_eq {d : Nat}
    {beta : Real} (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet) (a : ↑S -> Nat) :
    (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
        (currentCylinder S {a}) =
      (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
          (currentParityPatternCylinder S (currentLocalParity a)) *
        ENNReal.toReal
          (finiteParityPMF S beta hbeta (currentLocalParity a) a) := by
  have hfactor := freeCurrentLimit_pattern_factor d beta hbeta S hS
    (infiniteCurrentBoxSubsequence_strictMono d beta hbeta.le)
    (freeBoxCurrentMeasure_tendsto_infiniteFree d beta hbeta.le) a
  rw [Measure.real, Measure.real, hfactor, ENNReal.toReal_mul]

theorem infiniteFreeCurrentMeasure_singleton_inter_shift_real_eq {d : Nat}
    {beta : Real} (hbeta : 0 < beta)
    (g : Multiplicative (Site d))
    (S T : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (hT : (↑T : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (hdisj : Disjoint S (currentShiftFinset g T))
    (a : ↑S -> Nat) (b : ↑T -> Nat) :
    (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
        (currentCylinder S {a} ∩ (currentShift g) ⁻¹' currentCylinder T {b}) =
      (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
        (currentParityPatternCylinder S (currentLocalParity a) ∩
          (currentShift g) ⁻¹'
            currentParityPatternCylinder T (currentLocalParity b)) *
        (ENNReal.toReal
          (finiteParityPMF S beta hbeta (currentLocalParity a) a) *
        ENNReal.toReal
          (finiteParityPMF T beta hbeta (currentLocalParity b) b)) := by
  let G := currentShiftFinset g T
  let bG := currentShiftPattern g T b
  let c := mergeLocalPattern S G hdisj a bG
  have hG : (↑G : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet := currentShiftFinset_lattice d g T hT
  have hSG : (↑(S ∪ G) : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet := by
    intro e he
    change e ∈ S ∪ G at he
    rw [Finset.mem_union] at he
    exact he.elim (fun h => hS h) (fun h => hG h)
  rw [currentCylinder_singleton_inter_shift_of_disjoint g S T hdisj a b]
  rw [infiniteFreeCurrentMeasure_singleton_real_eq hbeta (S ∪ G) hSG c]
  have hparity : currentLocalParity c =
      mergeLocalPattern S G hdisj (currentLocalParity a)
        (currentShiftPattern g T (currentLocalParity b)) := by
    dsimp [c, bG]
    rw [currentLocalParity_merge, currentLocalParity_shiftPattern]
  rw [hparity]
  rw [← currentParityPatternCylinder_inter_shift_of_disjoint g S T hdisj
    (currentLocalParity a) (currentLocalParity b)]
  have hkernel := finiteParityPMF_merge S G hdisj beta hbeta
    (currentLocalParity a) (currentShiftPattern g T (currentLocalParity b)) a bG
  rw [show c = mergeLocalPattern S G hdisj a bG by rfl]
  rw [hkernel, finiteParityPMF_shiftPattern g T beta hbeta
    (currentLocalParity b) b, ENNReal.toReal_mul]



theorem infiniteFreeCurrentMeasure_singleton_family_pairMixing {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (patterns : Finset (↑S -> Nat))
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ g : Multiplicative (Site d),
      Disjoint S (currentShiftFinset g S) ∧
      ∀ a ∈ patterns, ∀ b ∈ patterns,
        abs ((infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
            (currentCylinder S {a} ∩
              (currentShift g) ⁻¹' currentCylinder S {b}) -
          (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
              (currentCylinder S {a}) *
            (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
              (currentCylinder S {b})) < epsilon := by
  classical
  let parityPatterns : Finset (↑S -> Bool) := patterns.image currentLocalParity
  obtain ⟨g, hdisj, hmix⟩ :=
    infiniteFreeCurrentMeasure_parityPattern_family_pairMixing hd hbeta S hS
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
  rw [infiniteFreeCurrentMeasure_singleton_inter_shift_real_eq hbeta g S S
      hS hS hdisj a b,
    infiniteFreeCurrentMeasure_singleton_real_eq hbeta S hS a,
    infiniteFreeCurrentMeasure_singleton_real_eq hbeta S hS b]
  let p := (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
    (currentParityPatternCylinder S (currentLocalParity a) ∩
      (currentShift g) ⁻¹'
        currentParityPatternCylinder S (currentLocalParity b))
  let q := (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
    (currentParityPatternCylinder S (currentLocalParity a))
  let r := (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
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



theorem infiniteFreeCurrentMeasure_latticeCylinder_family_pairMixing {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (accepted : Finset (Set (↑S -> Nat)))
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ g : Multiplicative (Site d),
      ∀ A ∈ accepted, ∀ B ∈ accepted,
        abs ((infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
            (currentCylinder S A ∩
              (currentShift g) ⁻¹' currentCylinder S B) -
          (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
              (currentCylinder S A) *
            (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
              (currentCylinder S B)) < epsilon := by
  classical
  let nu := infiniteFreeCurrentMeasure d beta hbeta.le
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
    infiniteFreeCurrentMeasure_singleton_family_pairMixing hd hbeta S hS K
      delta hdelta
  have hti : CurrentIsTranslationInvariant
      (H := Multiplicative (Site d)) mu :=
    infiniteFreeCurrentMeasure_isTranslationInvariant d beta hbeta
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



theorem infiniteFreeCurrentMeasure_cylinderPairMixing {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta) :
    CurrentCylinderPairMixing (H := Multiplicative (Site d))
      (infiniteFreeCurrentMeasure d beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d)))) := by
  classical
  let nu := infiniteFreeCurrentMeasure d beta hbeta.le
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
    infiniteFreeCurrentMeasure_latticeCylinder_family_pairMixing hd hbeta
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
    exact freeCurrentLimit_nonlattice_zero d beta hbeta.le e he
      (freeBoxCurrentMeasure_tendsto_infiniteFree d beta hbeta.le)
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



theorem infiniteFreeCurrentMeasure_isErgodic {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta) :
    CurrentIsErgodic (H := Multiplicative (Site d))
      (infiniteFreeCurrentMeasure d beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d)))) :=
  current_isErgodic_of_cylinderPairMixing
    (infiniteFreeCurrentMeasure_isTranslationInvariant d beta hbeta)
    (infiniteFreeCurrentMeasure_cylinderPairMixing hd hbeta)

end StatMech.FrontierB
