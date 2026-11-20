/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.CurrentChainClosure

open Filter MeasureTheory Set Topology
open scoped symmDiff

namespace StatMech.FrontierB

open ConfigSpace StatMech.FK Lattice Percolation Sharpness
open StatMech.OSSS.FKSharpnessWeightedPhaseTransport

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]



def fmu_AxisCofinalPairMixing (axis : Nat → H)
    (rho : Measure (ConfigSpace E)) : Prop :=
  ∀ (P : Finset (Finset E)), ∀ epsilon : Real, 0 < epsilon → ∀ K : Nat,
    ∃ k : Nat, K ≤ k ∧ ∀ T ∈ P, ∀ U ∈ P,
      abs (rho.real (fmu_multiOpen T ∩
          (shift (axis k)) ⁻¹' fmu_multiOpen U) -
        rho.real (fmu_multiOpen T) * rho.real (fmu_multiOpen U)) < epsilon



theorem independentMixedPairConfigLaw_axisCofinalGenMixing
    (axis : Nat → H)
    (rho nu : ProbabilityMeasure (ConfigSpace E))
    (hrho : fmu_AxisCofinalGenMixing axis
      (rho : Measure (ConfigSpace E)))
    (hnu : fmu_AxisEventuallyGenMixing axis
      (nu : Measure (ConfigSpace E))) :
    fmu_AxisCofinalPairMixing axis
      (independentMixedPairConfigLaw rho nu :
        Measure (ConfigSpace (E ⊕ E))) := by
  classical
  intro P epsilon hepsilon K0
  let Q : Finset (Finset E) :=
    P.image pairLeft ∪ P.image pairRight
  let cylinders : Finset (Set (ConfigSpace E)) := Q.image fmu_multiOpen
  have hcylinders : ∀ A ∈ cylinders,
      A ∈ measurableCylinders (fun _ : E => Bool) := by
    intro A hA
    rw [Finset.mem_image] at hA
    obtain ⟨T, hT, rfl⟩ := hA
    exact fmu_multiOpen_mem_measurableCylinders T
  let delta := epsilon / 3
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hnuEventually := hnu cylinders hcylinders delta hdelta
  obtain ⟨K1, hK1⟩ := eventually_atTop.mp hnuEventually
  obtain ⟨k, hk, hrhoMix⟩ :=
    hrho cylinders hcylinders delta hdelta (max K0 K1)
  have hk0 : K0 ≤ k := (le_max_left K0 K1).trans hk
  have hk1 : K1 ≤ k := (le_max_right K0 K1).trans hk
  have hnuMix := hK1 k hk1
  refine ⟨k, hk0, ?_⟩
  intro T hT U hU
  have hTL : pairLeft T ∈ Q :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨T, hT, rfl⟩)
  have hTR : pairRight T ∈ Q :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨T, hT, rfl⟩)
  have hUL : pairLeft U ∈ Q :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨U, hU, rfl⟩)
  have hUR : pairRight U ∈ Q :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨U, hU, rfl⟩)
  have hleft := hrhoMix (fmu_multiOpen (pairLeft T))
    (Finset.mem_image.mpr ⟨pairLeft T, hTL, rfl⟩)
    (fmu_multiOpen (pairLeft U))
    (Finset.mem_image.mpr ⟨pairLeft U, hUL, rfl⟩)
  have hright := hnuMix (fmu_multiOpen (pairRight T))
    (Finset.mem_image.mpr ⟨pairRight T, hTR, rfl⟩)
    (fmu_multiOpen (pairRight U))
    (Finset.mem_image.mpr ⟨pairRight U, hUR, rfl⟩)
  let a := (rho : Measure _).real
    (fmu_multiOpen (pairLeft T) ∩
      (shift (axis k)) ⁻¹' fmu_multiOpen (pairLeft U))
  let b := (nu : Measure _).real
    (fmu_multiOpen (pairRight T) ∩
      (shift (axis k)) ⁻¹' fmu_multiOpen (pairRight U))
  let c := (rho : Measure _).real (fmu_multiOpen (pairLeft T)) *
    (rho : Measure _).real (fmu_multiOpen (pairLeft U))
  let e := (nu : Measure _).real (fmu_multiOpen (pairRight T)) *
    (nu : Measure _).real (fmu_multiOpen (pairRight U))
  have hb : 0 ≤ b := measureReal_nonneg
  have hc : 0 ≤ c := mul_nonneg measureReal_nonneg measureReal_nonneg
  have hb1 : b ≤ 1 := measureReal_le_one
  have hc1 : c ≤ 1 :=
    mul_le_one₀ measureReal_le_one measureReal_nonneg measureReal_le_one
  change abs (_ - _) < epsilon
  rw [independentMixedPairConfigLaw_real_inter_shift,
    independentMixedPairConfigLaw_real_multiOpen,
    independentMixedPairConfigLaw_real_multiOpen]
  change abs (a * b -
    ((rho : Measure _).real (fmu_multiOpen (pairLeft T)) *
      (nu : Measure _).real (fmu_multiOpen (pairRight T))) *
    ((rho : Measure _).real (fmu_multiOpen (pairLeft U)) *
      (nu : Measure _).real (fmu_multiOpen (pairRight U)))) < epsilon
  rw [show
    ((rho : Measure _).real (fmu_multiOpen (pairLeft T)) *
      (nu : Measure _).real (fmu_multiOpen (pairRight T))) *
    ((rho : Measure _).real (fmu_multiOpen (pairLeft U)) *
      (nu : Measure _).real (fmu_multiOpen (pairRight U))) = c * e by
      dsimp [c, e]
      ring]
  have hab : a * b - c * e = (a - c) * b + c * (b - e) := by ring
  rw [hab]
  calc
    abs ((a - c) * b + c * (b - e)) ≤
        abs (a - c) * abs b + abs c * abs (b - e) := by
      simpa [abs_mul] using abs_add_le ((a - c) * b) (c * (b - e))
    _ < delta * 1 + 1 * delta := by
      have habsB : abs b ≤ 1 := by
        rw [abs_of_nonneg hb]
        exact hb1
      have habsC : abs c ≤ 1 := by
        rw [abs_of_nonneg hc]
        exact hc1
      exact add_lt_add_of_lt_of_lt
        (mul_lt_mul_of_lt_of_le_of_nonneg_of_pos
          hleft habsB (abs_nonneg _) zero_lt_one)
        (mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
          habsC hright (abs_nonneg _) zero_lt_one)
    _ < epsilon := by dsimp [delta]; linarith



theorem freePlusCurrentTracePairLaw_axisCofinalGenMixing
    {d : Nat} (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta) :
    fmu_AxisCofinalPairMixing
      (fun k => FK.freeAxisTranslationPower hd k)
      (independentMixedPairConfigLaw
        (currentTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le))
        (currentTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le)) :
          Measure (ConfigSpace
            (Sym2 (Site d) ⊕ Sym2 (Site d)))) :=
  independentMixedPairConfigLaw_axisCofinalGenMixing _ _ _
    (infiniteFreeCurrentTraceLaw_axisCofinalGenMixing hd hbeta)
    (infinitePlusCurrentTraceLaw_axisEventuallyGenMixing hd hbeta)

set_option maxHeartbeats 2000000 in


theorem fmu_axisCofinalGenMixing_of_axisCofinalPairMixing
    {rho : Measure (ConfigSpace E)} [IsProbabilityMeasure rho]
    (axis : Nat → H)
    (hmix : fmu_AxisCofinalPairMixing axis rho) :
    fmu_AxisCofinalGenMixing axis rho := by
  classical
  intro family hfamily epsilon hepsilon K
  let members := family.attach
  let support (A : ↑family) : Finset (Finset E) :=
    (fmu_cylinder_expand A.1 (hfamily A.1 A.2)).choose
  let baseCoeff (A : ↑family) : Finset E → Real :=
    (fmu_cylinder_expand A.1 (hfamily A.1 A.2)).choose_spec.choose
  have hbase (A : ↑family) (omega : ConfigSpace E) :
      A.1.indicator (fun _ => (1 : Real)) omega =
        ∑ T ∈ support A, baseCoeff A T * fmu_moInd T omega :=
    (fmu_cylinder_expand A.1
      (hfamily A.1 A.2)).choose_spec.choose_spec omega
  let indices : Finset (Finset E) := members.biUnion support
  have hsupport (A : ↑family) : support A ⊆ indices := by
    intro T hT
    exact Finset.mem_biUnion.mpr
      ⟨A, Finset.mem_attach _ A, hT⟩
  let coeff (A : ↑family) : Finset E → Real := fun T =>
    if T ∈ support A then baseCoeff A T else 0
  have hexp (A : ↑family) (omega : ConfigSpace E) :
      A.1.indicator (fun _ => (1 : Real)) omega =
        ∑ T ∈ indices, coeff A T * fmu_moInd T omega := by
    calc
      A.1.indicator (fun _ => (1 : Real)) omega =
          ∑ T ∈ support A, baseCoeff A T * fmu_moInd T omega :=
        hbase A omega
      _ = ∑ T ∈ support A, coeff A T * fmu_moInd T omega := by
        apply Finset.sum_congr rfl
        intro T hT
        simp [coeff, hT]
      _ = ∑ T ∈ indices, coeff A T * fmu_moInd T omega :=
        Finset.sum_subset (hsupport A) (by
          intro T hTindices hTsupport
          simp [coeff, hTsupport])
  let coeffs : Finset (Finset E → Real) := members.image coeff
  let M : Real := ∑ c ∈ coeffs, ∑ T ∈ indices, abs (c T)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let delta := epsilon / (M * M + 1)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨k, hk, hgood⟩ := hmix indices delta hdelta K
  refine ⟨k, hk, ?_⟩
  intro A hA B hB
  let a : ↑family := ⟨A, hA⟩
  let b : ↑family := ⟨B, hB⟩
  have ha : coeff a ∈ coeffs :=
    Finset.mem_image.mpr ⟨a, Finset.mem_attach _ a, rfl⟩
  have hb : coeff b ∈ coeffs :=
    Finset.mem_image.mpr ⟨b, Finset.mem_attach _ b, rfl⟩
  have hca : (∑ T ∈ indices, abs (coeff a T)) ≤ M := by
    dsimp [M]
    exact Finset.single_le_sum
      (fun c hc => Finset.sum_nonneg fun T hT => abs_nonneg (c T)) ha
  have hcb : (∑ T ∈ indices, abs (coeff b T)) ≤ M := by
    dsimp [M]
    exact Finset.single_le_sum
      (fun c hc => Finset.sum_nonneg fun T hT => abs_nonneg (c T)) hb
  have hAmeas : MeasurableSet A :=
    MeasurableSet.of_mem_measurableCylinders (hfamily A hA)
  have hBmeas : MeasurableSet B :=
    MeasurableSet.of_mem_measurableCylinders (hfamily B hB)
  rw [fmu_real_inter_shift_eq_cross_sum (axis k) hAmeas hBmeas
      indices indices (coeff a) (coeff b) (hexp a) (hexp b),
    fmu_real_eq_sum hAmeas indices (coeff a) (hexp a),
    fmu_real_eq_sum hBmeas indices (coeff b) (hexp b),
    Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  have hdiff (T : Finset E) :
      (∑ U ∈ indices, coeff a T * coeff b U *
          rho.real (fmu_multiOpen T ∩
            (shift (axis k) : ConfigSpace E → ConfigSpace E) ⁻¹'
              fmu_multiOpen U)) -
        (∑ U ∈ indices,
          (coeff a T * rho.real (fmu_multiOpen T)) *
            (coeff b U * rho.real (fmu_multiOpen U))) =
      ∑ U ∈ indices, coeff a T * coeff b U *
        (rho.real (fmu_multiOpen T ∩
            (shift (axis k) : ConfigSpace E → ConfigSpace E) ⁻¹'
              fmu_multiOpen U) -
          rho.real (fmu_multiOpen T) *
            rho.real (fmu_multiOpen U)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro U hU
    ring
  simp_rw [hdiff]
  calc
    abs (∑ T ∈ indices, ∑ U ∈ indices,
        coeff a T * coeff b U *
          (rho.real (fmu_multiOpen T ∩
              (shift (axis k) : ConfigSpace E → ConfigSpace E) ⁻¹'
                fmu_multiOpen U) -
            rho.real (fmu_multiOpen T) *
              rho.real (fmu_multiOpen U))) ≤
      ∑ T ∈ indices, ∑ U ∈ indices,
        abs (coeff a T) * abs (coeff b U) * delta := by
      calc
        _ ≤ ∑ T ∈ indices, abs (∑ U ∈ indices,
            coeff a T * coeff b U *
              (rho.real (fmu_multiOpen T ∩
                  (shift (axis k) : ConfigSpace E → ConfigSpace E) ⁻¹'
                    fmu_multiOpen U) -
                rho.real (fmu_multiOpen T) *
                  rho.real (fmu_multiOpen U))) :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro T hT
          calc
            _ ≤ ∑ U ∈ indices, abs (coeff a T * coeff b U *
                (rho.real (fmu_multiOpen T ∩
                    (shift (axis k) : ConfigSpace E → ConfigSpace E) ⁻¹'
                      fmu_multiOpen U) -
                  rho.real (fmu_multiOpen T) *
                    rho.real (fmu_multiOpen U))) :=
              Finset.abs_sum_le_sum_abs _ _
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro U hU
              rw [abs_mul, abs_mul]
              exact mul_le_mul_of_nonneg_left
                (hgood T hT U hU).le
                (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∑ T ∈ indices, abs (coeff a T)) *
        (∑ U ∈ indices, abs (coeff b U)) * delta := by
      rw [Finset.sum_mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro T hT
      rw [Finset.sum_mul]
    _ ≤ M * M * delta := by
      apply mul_le_mul_of_nonneg_right _ hdelta.le
      exact mul_le_mul hca hcb
        (Finset.sum_nonneg fun U hU => abs_nonneg _) hM
    _ < epsilon := by
      dsimp [delta]
      have hden : M * M + 1 ≠ 0 := by positivity
      have hpos : 0 < epsilon / (M * M + 1) := by positivity
      calc
        M * M * (epsilon / (M * M + 1)) <
            (M * M + 1) * (epsilon / (M * M + 1)) :=
          mul_lt_mul_of_pos_right (by linarith) hpos
        _ = epsilon := mul_div_cancel₀ epsilon hden

theorem freePlusCurrentTracePairLaw_axisCofinalGenMixing_full
    {d : Nat} (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta) :
    fmu_AxisCofinalGenMixing
      (fun k => FK.freeAxisTranslationPower hd k)
      (independentMixedPairConfigLaw
        (currentTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le))
        (currentTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le)) :
          Measure (ConfigSpace
            (Sym2 (Site d) ⊕ Sym2 (Site d)))) :=
  fmu_axisCofinalGenMixing_of_axisCofinalPairMixing _
    (freePlusCurrentTracePairLaw_axisCofinalGenMixing hd hbeta)


theorem independentMixedOrConfigLaw_axisCofinalGenMixing
    (axis : Nat → H)
    (rho nu : ProbabilityMeasure (ConfigSpace E))
    (hmix : fmu_AxisCofinalGenMixing axis
      (independentMixedPairConfigLaw rho nu :
        Measure (ConfigSpace (E ⊕ E)))) :
    fmu_AxisCofinalGenMixing axis
      (independentMixedOrConfigLaw rho nu : Measure (ConfigSpace E)) := by
  classical
  intro family hfamily epsilon hepsilon K
  let pulled : Finset (Set (ConfigSpace (E ⊕ E))) :=
    family.image (fun A => pairOrConfig ⁻¹' A)
  have hpulled : ∀ A ∈ pulled,
      A ∈ measurableCylinders (fun _ : E ⊕ E => Bool) := by
    intro A hA
    rw [Finset.mem_image] at hA
    obtain ⟨C, hC, rfl⟩ := hA
    exact pairOrConfig_preimage_mem_measurableCylinders (hfamily C hC)
  obtain ⟨k, hk, hmixk⟩ := hmix pulled hpulled epsilon hepsilon K
  refine ⟨k, hk, ?_⟩
  intro A hA B hB
  have hAmeas : MeasurableSet A :=
    MeasurableSet.of_mem_measurableCylinders (hfamily A hA)
  have hBmeas : MeasurableSet B :=
    MeasurableSet.of_mem_measurableCylinders (hfamily B hB)
  have hABmeas : MeasurableSet (A ∩ (shift (axis k)) ⁻¹' B) :=
    hAmeas.inter (hBmeas.preimage (measurable_shift (axis k)))
  rw [independentMixedOrConfigLaw_real rho nu hABmeas,
    independentMixedOrConfigLaw_real rho nu hAmeas,
    independentMixedOrConfigLaw_real rho nu hBmeas,
    pairOrConfig_preimage_inter_shift]
  exact hmixk (pairOrConfig ⁻¹' A)
    (Finset.mem_image.mpr ⟨A, hA, rfl⟩)
    (pairOrConfig ⁻¹' B)
    (Finset.mem_image.mpr ⟨B, hB, rfl⟩)

theorem freePlusSuperposedTraceLaw_axisCofinalGenMixing
    {d : Nat} (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta) :
    fmu_AxisCofinalGenMixing
      (fun k => FK.freeAxisTranslationPower hd k)
      (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) :
          Measure (ConfigSpace (Sym2 (Site d)))) := by
  rw [← independentMixedOr_currentTraceLaw_eq_superposed]
  exact independentMixedOrConfigLaw_axisCofinalGenMixing _ _ _
    (freePlusCurrentTracePairLaw_axisCofinalGenMixing_full hd hbeta)



theorem fmu_axisCofinal_event_exists_after
    {rho : Measure (ConfigSpace E)} [IsProbabilityMeasure rho]
    (axis : Nat → H)
    (hti : IsTranslationInvariant (G := H) rho)
    (hmix : fmu_AxisCofinalGenMixing axis rho)
    (s : Set (ConfigSpace E)) (hs : MeasurableSet s)
    (K : Nat) (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ k : Nat, K ≤ k ∧
      abs (rho.real (s ∩
          (shift (axis k) : ConfigSpace E → ConfigSpace E) ⁻¹' s) -
        (rho.real s) ^ 2) < 5 * epsilon := by
  obtain ⟨C, hCmem, hCsd⟩ := fmc_exists_cylinder_symmDiff_lt rho hs
    (ε := ENNReal.ofReal epsilon) (by simpa using hepsilon)
  have hCmeas : MeasurableSet C :=
    MeasurableSet.of_mem_measurableCylinders hCmem
  obtain ⟨k, hk, hmixC⟩ := hmix {C} (by
    intro A hA
    have hAC : A = C := Finset.mem_singleton.mp hA
    rw [hAC]
    exact hCmem) epsilon hepsilon K
  refine ⟨k, hk, ?_⟩
  let C' := (shift (axis k) : ConfigSpace E → ConfigSpace E) ⁻¹' C
  let s' := (shift (axis k) : ConfigSpace E → ConfigSpace E) ⁻¹' s
  have hC'meas : MeasurableSet C' :=
    hCmeas.preimage (measurable_shift (axis k))
  have hs'meas : MeasurableSet s' :=
    hs.preimage (measurable_shift (axis k))
  have hCsd' : rho.real (C ∆ s) < epsilon := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top rho _) (by simp)).2 hCsd
    rwa [ENNReal.toReal_ofReal hepsilon.le] at h
  have hC'sd' : rho.real (C' ∆ s') < epsilon := by
    have hpre : C' ∆ s' =
        (shift (axis k) : ConfigSpace E → ConfigSpace E) ⁻¹' (C ∆ s) := by
      ext x
      rfl
    have hmeasure : rho (C' ∆ s') = rho (C ∆ s) := by
      rw [hpre]
      exact (hti (axis k)).measure_preimage
        ((hCmeas.symmDiff hs).nullMeasurableSet)
    rw [Measure.real, hmeasure]
    exact hCsd'
  have hCs : abs (rho.real C - rho.real s) ≤ rho.real (C ∆ s) :=
    abs_measureReal_sub_le_measureReal_symmDiff
      hCmeas.nullMeasurableSet hs.nullMeasurableSet
  have hinter : abs (rho.real (C ∩ C') - rho.real (s ∩ s')) ≤
      rho.real (C ∆ s) + rho.real (C' ∆ s') := by
    have hsub : (C ∩ C') ∆ (s ∩ s') ⊆
        (C ∆ s) ∪ (C' ∆ s') := by
      intro x hx
      rcases hx with ⟨hxCC', hxss'⟩ | ⟨hxss', hxCC'⟩
      · obtain ⟨hxC, hxC'⟩ := hxCC'
        rw [Set.mem_inter_iff, not_and_or] at hxss'
        rcases hxss' with hxs | hxs'
        · exact Or.inl (Or.inl ⟨hxC, hxs⟩)
        · exact Or.inr (Or.inl ⟨hxC', hxs'⟩)
      · obtain ⟨hxs, hxs'⟩ := hxss'
        rw [Set.mem_inter_iff, not_and_or] at hxCC'
        rcases hxCC' with hxC | hxC'
        · exact Or.inl (Or.inr ⟨hxs, hxC⟩)
        · exact Or.inr (Or.inr ⟨hxs', hxC'⟩)
    calc
      abs (rho.real (C ∩ C') - rho.real (s ∩ s')) ≤
          rho.real ((C ∩ C') ∆ (s ∩ s')) :=
        abs_measureReal_sub_le_measureReal_symmDiff
          (hCmeas.inter hC'meas).nullMeasurableSet
          (hs.inter hs'meas).nullMeasurableSet
      _ ≤ rho.real ((C ∆ s) ∪ (C' ∆ s')) :=
        measureReal_mono hsub (by finiteness)
      _ ≤ rho.real (C ∆ s) + rho.real (C' ∆ s') :=
        measureReal_union_le _ _
  have hmix' : abs (rho.real (C ∩ C') - (rho.real C) ^ 2) < epsilon := by
    simpa only [Finset.mem_singleton, forall_const, C', pow_two] using
      hmixC C (by simp) C (by simp)
  have hsquares : abs ((rho.real C) ^ 2 - (rho.real s) ^ 2) ≤
      2 * rho.real (C ∆ s) := by
    have hCnn : 0 ≤ rho.real C := measureReal_nonneg
    have hsnn : 0 ≤ rho.real s := measureReal_nonneg
    have hCle : rho.real C ≤ 1 := measureReal_le_one
    have hsle : rho.real s ≤ 1 := measureReal_le_one
    calc
      abs (rho.real C ^ 2 - rho.real s ^ 2) =
          abs (rho.real C - rho.real s) *
            abs (rho.real C + rho.real s) := by
        rw [← abs_mul]
        ring_nf
      _ ≤ abs (rho.real C - rho.real s) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [abs_of_nonneg (by positivity)]
        linarith
      _ ≤ rho.real (C ∆ s) * 2 :=
        mul_le_mul_of_nonneg_right hCs (by norm_num)
      _ = 2 * rho.real (C ∆ s) := by ring
  have htriangle :
      abs (rho.real (s ∩ s') - (rho.real s) ^ 2) ≤
        abs (rho.real (s ∩ s') - rho.real (C ∩ C')) +
          (abs (rho.real (C ∩ C') - (rho.real C) ^ 2) +
            abs ((rho.real C) ^ 2 - (rho.real s) ^ 2)) := by
    calc
      abs (rho.real (s ∩ s') - (rho.real s) ^ 2) ≤
          abs (rho.real (s ∩ s') - rho.real (C ∩ C')) +
            abs (rho.real (C ∩ C') - (rho.real s) ^ 2) :=
        abs_sub_le _ _ _
      _ ≤ abs (rho.real (s ∩ s') - rho.real (C ∩ C')) +
          (abs (rho.real (C ∩ C') - (rho.real C) ^ 2) +
            abs ((rho.real C) ^ 2 - (rho.real s) ^ 2)) := by
        linarith [abs_sub_le (rho.real (C ∩ C'))
          ((rho.real C) ^ 2) ((rho.real s) ^ 2)]
  change abs (rho.real (s ∩ s') - (rho.real s) ^ 2) < 5 * epsilon
  calc
    abs (rho.real (s ∩ s') - (rho.real s) ^ 2) ≤
        abs (rho.real (s ∩ s') - rho.real (C ∩ C')) +
          (abs (rho.real (C ∩ C') - (rho.real C) ^ 2) +
            abs ((rho.real C) ^ 2 - (rho.real s) ^ 2)) := htriangle
    _ ≤ (rho.real (C ∆ s) + rho.real (C' ∆ s')) +
          (epsilon + 2 * rho.real (C ∆ s)) := by
      apply add_le_add
      · rw [abs_sub_comm]
        exact hinter
      · exact add_le_add hmix'.le hsquares
    _ < 5 * epsilon := by linarith



noncomputable def currentContinuityAxisSite
    {d : Nat} (hd : 1 ≤ d) (k : Nat) : Site d :=
  (FK.freeAxisTranslationPower hd k)⁻¹ • origin d


def CurrentContinuityFreeAxisLROZero
    (d : Nat) (hd : 1 ≤ d) (beta : Real) : Prop :=
  ∀ epsilon : Real, 0 < epsilon → ∃ K : Nat, ∀ k : Nat, K ≤ k →
    |currentContinuityFreeTwoPoint d beta (origin d)
      (currentContinuityAxisSite hd k)| < epsilon



def CurrentContinuityAxisConnectivityPersists
    (d : Nat) (hd : 1 ≤ d)
    (mu : Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  ∃ epsilon : Real, 0 < epsilon ∧ ∀ K : Nat, ∃ k : Nat, K ≤ k ∧
    epsilon ≤ infiniteTwoPointReal mu (origin d)
      (currentContinuityAxisSite hd k)

def CurrentContinuityAxisPercolationPrinciple
    (d : Nat) (hd : 1 ≤ d)
    (mu : Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  0 < mu.real (percolationEvent d) →
    CurrentContinuityAxisConnectivityPersists d hd mu



theorem currentContinuityAxisPercolationPrinciple_of_mixing
    (d : Nat) (hd : 1 ≤ d)
    (rho : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (rho : Measure (ConfigSpace (Sym2 (Site d)))))
    (hmix : fmu_AxisCofinalGenMixing
      (fun k => FK.freeAxisTranslationPower hd k)
      (rho : Measure (ConfigSpace (Sym2 (Site d)))))
    (hunique : (rho : Measure (ConfigSpace (Sym2 (Site d))))
      (atLeastTwoInfinite d) = 0) :
    CurrentContinuityAxisPercolationPrinciple d hd
      (rho : Measure (ConfigSpace (Sym2 (Site d)))) := by
  intro htheta
  let theta := (rho : Measure (ConfigSpace (Sym2 (Site d)))).real
    (percolationEvent d)
  let epsilon := theta ^ 2 / 2
  have htheta' : 0 < theta := htheta
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  refine ⟨epsilon, hepsilon, ?_⟩
  intro K
  let tolerance := theta ^ 2 / 20
  have htolerance : 0 < tolerance := by dsimp [tolerance]; positivity
  let E := clusterInfiniteEvent d (origin d)
  have hEmeas : MeasurableSet E :=
    measurableSet_clusterInfiniteEvent (origin d)
  obtain ⟨k, hk, hcorr⟩ := fmu_axisCofinal_event_exists_after
    (fun k => FK.freeAxisTranslationPower hd k) hti hmix E hEmeas
      K tolerance htolerance
  refine ⟨k, hk, ?_⟩
  have hEmass : (rho : Measure (ConfigSpace (Sym2 (Site d)))).real E =
      theta := rfl
  have hshift :
      (shift (FK.freeAxisTranslationPower hd k) :
        ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' E =
        clusterInfiniteEvent d (currentContinuityAxisSite hd k) := by
    simpa [E, currentContinuityAxisSite] using
      (shift_preimage_clusterInfiniteEvent (d := d)
        (FK.freeAxisTranslationPower hd k)
        (currentContinuityAxisSite hd k))
  have hcorrLower : epsilon ≤
      (rho : Measure (ConfigSpace (Sym2 (Site d)))).real
        (E ∩ (shift (FK.freeAxisTranslationPower hd k)) ⁻¹' E) := by
    have habs := (abs_lt.mp hcorr).1
    rw [hEmass] at habs
    dsimp [epsilon, tolerance] at habs ⊢
    nlinarith [sq_pos_of_pos htheta']
  rw [hshift] at hcorrLower
  exact hcorrLower.trans
    (infinite_cluster_inter_le_twoPoint
      (rho : Measure (ConfigSpace (Sym2 (Site d)))) hunique
      (origin d) (currentContinuityAxisSite hd k))

theorem currentContinuityMixedTraceLaw_axisPercolationPrinciple
    (d : Nat) (hd : 1 ≤ d) (beta : Real) (hbeta : 0 < beta) :
    CurrentContinuityAxisPercolationPrinciple d hd
      (currentContinuityMixedTraceLaw d beta hbeta : Measure _) := by
  apply currentContinuityAxisPercolationPrinciple_of_mixing
    d hd (currentContinuityMixedTraceLaw d beta hbeta)
    (currentContinuityMixedTraceLaw_isTranslationInvariant d beta hbeta)
  · rw [show currentContinuityMixedTraceLaw d beta hbeta =
        independentSuperposedTraceLaw
          (infiniteFreeCurrentMeasure d beta hbeta.le)
          (infinitePlusCurrentMeasure d beta hbeta.le) by
      exact independentSuperposedTraceLaw_comm _ _]
    exact freePlusSuperposedTraceLaw_axisCofinalGenMixing hd hbeta
  · exact currentContinuityMixedTraceLaw_uniqueInfiniteCluster
      d hd beta hbeta



theorem currentContinuity_no_axis_persistent_connectivity_of_freeAxisLROZero
    {d : Nat} (hd : 1 ≤ d) (beta : Real) (hbeta : 0 < beta)
    (hunique :
      (currentContinuityMixedTraceLaw d beta hbeta : Measure _)
        (atLeastTwoInfinite d) = 0)
    (hLRO : CurrentContinuityFreeAxisLROZero d hd beta) :
    ¬ CurrentContinuityAxisConnectivityPersists d hd
      (currentContinuityMixedTraceLaw d beta hbeta : Measure _) := by
  rintro ⟨epsilon, hepsilon, hpersist⟩
  obtain ⟨K, hK⟩ := hLRO epsilon hepsilon
  obtain ⟨k, hk, hklower⟩ := hpersist (max K 1)
  have hkK : K ≤ k := (le_max_left K 1).trans hk
  have hk1 : 1 ≤ k := (le_max_right K 1).trans hk
  have hxo : origin d ≠ currentContinuityAxisSite hd k := by
    intro h
    have hcoord := congrFun h ⟨0, hd⟩
    simp [currentContinuityAxisSite, FK.freeAxisTranslationPower,
      smul_site_apply, origin] at hcoord
    omega
  have hid := currentContinuity_mixed_twoPoint_identity
    beta hbeta hunique (origin d) (currentContinuityAxisSite hd k) hxo
  have hplus0 : 0 ≤ currentContinuityPlusTwoPoint d beta (origin d)
      (currentContinuityAxisSite hd k) := by
    rw [currentContinuityPlusTwoPoint_eq_plusCorr beta _ _ hxo]
    exact Sharpness.plusCorr_nonneg beta hbeta.le _ _
  have hplus1 : currentContinuityPlusTwoPoint d beta (origin d)
      (currentContinuityAxisSite hd k) ≤ 1 := by
    rw [currentContinuityPlusTwoPoint_eq_plusCorr beta _ _ hxo]
    exact Sharpness.plusCorr_le_one beta _ _
  have hfree := hK k hkK
  have habs :
      |currentContinuityPlusTwoPoint d beta (origin d)
          (currentContinuityAxisSite hd k) *
        currentContinuityFreeTwoPoint d beta (origin d)
          (currentContinuityAxisSite hd k)| < epsilon := by
    rw [abs_mul, abs_of_nonneg hplus0]
    calc
      currentContinuityPlusTwoPoint d beta (origin d)
            (currentContinuityAxisSite hd k) *
          |currentContinuityFreeTwoPoint d beta (origin d)
            (currentContinuityAxisSite hd k)|
          ≤ 1 * |currentContinuityFreeTwoPoint d beta (origin d)
            (currentContinuityAxisSite hd k)| :=
        mul_le_mul_of_nonneg_right hplus1 (abs_nonneg _)
      _ < 1 * epsilon := mul_lt_mul_of_pos_left hfree zero_lt_one
      _ = epsilon := one_mul _
  rw [hid] at habs
  unfold infiniteTwoPointReal at habs
  rw [abs_of_nonneg measureReal_nonneg] at habs
  exact (not_lt_of_ge hklower) habs


theorem currentContinuity_no_percolation_of_freeAxisLROZero
    {d : Nat} (hd : 1 ≤ d) (beta : Real) (hbeta : 0 < beta)
    (hLRO : CurrentContinuityFreeAxisLROZero d hd beta) :
    (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real
      (percolationEvent d) = 0 := by
  apply le_antisymm
  · by_contra hne
    have hpos : 0 <
        (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real
          (percolationEvent d) := lt_of_not_ge hne
    exact currentContinuity_no_axis_persistent_connectivity_of_freeAxisLROZero
      hd beta hbeta
      (currentContinuityMixedTraceLaw_uniqueInfiniteCluster d hd beta hbeta)
      hLRO
      (currentContinuityMixedTraceLaw_axisPercolationPrinciple
        d hd beta hbeta hpos)
  · exact measureReal_nonneg

end StatMech.FrontierB
