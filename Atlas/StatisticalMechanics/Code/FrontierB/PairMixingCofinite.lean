/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FK.FKMixingUpperClose

open MeasureTheory Set
open StatMech.ConfigSpace

namespace StatMech.FK

open ConfigSpace

variable {E G : Type*} [CommGroup G] [MulAction G E]



theorem fmu_pairMixing_exists_not_mem [Infinite G] [Countable E] [DecidableEq E]
    {mu : Measure (ConfigSpace E)} [IsProbabilityMeasure mu]
    (hti : IsTranslationInvariant (G := G) mu)
    (hmix : fmu_PairMixing (G := G) mu)
    (P : Finset (Finset E)) (K : Finset G) (delta : Real) (hdelta : 0 < delta) :
    ∃ g : G, g ∉ K ∧ ∀ T ∈ P, ∀ T' ∈ P,
      abs (mu.real (fmu_multiOpen T ∩
          (shift g : ConfigSpace E -> ConfigSpace E) ⁻¹' fmu_multiOpen T') -
        mu.real (fmu_multiOpen T) * mu.real (fmu_multiOpen T')) < delta := by
  classical
  obtain ⟨L, hL⟩ := Finset.exists_card_eq (α := G) (K.card + 1)
  let translated : G -> Finset E -> Finset E :=
    fun k T => T.image (fun e => k⁻¹ • e)
  let Q : Finset (Finset E) :=
    P ∪ L.biUnion (fun k => P.image (translated k))
  obtain ⟨h, hh⟩ := hmix Q delta hdelta
  have hexists : ∃ k ∈ L, h * k ∉ K := by
    by_contra hcontra
    push Not at hcontra
    have hsub : L.image (fun k => h * k) ⊆ K := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      exact hcontra k hk
    have hcard := Finset.card_le_card hsub
    have hinj : Function.Injective (fun k : G => h * k) := by
      intro a b hab
      exact mul_left_cancel hab
    rw [Finset.card_image_of_injective _ hinj, hL] at hcard
    omega
  obtain ⟨k, hkL, hkK⟩ := hexists
  refine ⟨h * k, hkK, ?_⟩
  intro T hTP T' hT'P
  let T'k := translated k T'
  have hTQ : T ∈ Q := Finset.mem_union_left _ hTP
  have hT'kQ : T'k ∈ Q := by
    apply Finset.mem_union_right
    rw [Finset.mem_biUnion]
    exact ⟨k, hkL, Finset.mem_image.mpr ⟨T', hT'P, rfl⟩⟩
  have hgood := hh T hTQ T'k hT'kQ
  have hTk : fmu_multiOpen T'k =
      (shift k : ConfigSpace E -> ConfigSpace E) ⁻¹' fmu_multiOpen T' := by
    simpa [T'k, translated] using (fmu_shift_multiOpen k T').symm
  have hcross : fmu_multiOpen T ∩
        (shift h : ConfigSpace E -> ConfigSpace E) ⁻¹' fmu_multiOpen T'k =
      fmu_multiOpen T ∩
        (shift (h * k) : ConfigSpace E -> ConfigSpace E) ⁻¹' fmu_multiOpen T' := by
    rw [hTk]
    ext omega
    simp only [mem_inter_iff, mem_preimage]
    rw [mul_comm h k, shift_mul]
    rfl
  have hmass : mu.real (fmu_multiOpen T'k) =
      mu.real (fmu_multiOpen T') := by
    rw [hTk]
    exact fmc_real_preimage_shift hti k (fmu_multiOpen_measurable T')
  rwa [hcross, hmass] at hgood




theorem fmu_pairMixing_exists_disjoint [Infinite G] [Countable E] [DecidableEq E]
    {mu : Measure (ConfigSpace E)} [IsProbabilityMeasure mu]
    (hsolution : ∀ a b : E, {g : G | g • a = b}.Finite)
    (hti : IsTranslationInvariant (G := G) mu)
    (hmix : fmu_PairMixing (G := G) mu)
    (P : Finset (Finset E)) (delta : Real) (hdelta : 0 < delta) :
    ∃ g : G, (∀ T ∈ P, ∀ T' ∈ P,
        Disjoint T (T'.image (fun e => g⁻¹ • e))) ∧
      ∀ T ∈ P, ∀ T' ∈ P,
        abs (mu.real (fmu_multiOpen T ∩
            (shift g : ConfigSpace E -> ConfigSpace E) ⁻¹' fmu_multiOpen T') -
          mu.real (fmu_multiOpen T) * mu.real (fmu_multiOpen T')) < delta := by
  classical
  let U : Finset E := P.biUnion id
  let bad : Set G := ⋃ a ∈ U, ⋃ b ∈ U, {g : G | g⁻¹ • a = b}
  have hsingle (a b : E) : {g : G | g⁻¹ • a = b}.Finite := by
    have heq : {g : G | g⁻¹ • a = b} = {g : G | g • b = a} := by
      ext g
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        have := congrArg (fun x => g • x) h
        simpa [smul_smul] using this.symm
      · intro h
        have := congrArg (fun x => g⁻¹ • x) h
        simpa [smul_smul] using this.symm
    rw [heq]
    exact hsolution b a
  have hbad : bad.Finite := by
    apply Set.Finite.biUnion U.finite_toSet
    intro a ha
    apply Set.Finite.biUnion U.finite_toSet
    intro b hb
    exact hsingle a b
  let K : Finset G := hbad.toFinset
  obtain ⟨g, hgK, hgood⟩ :=
    fmu_pairMixing_exists_not_mem hti hmix P K delta hdelta
  refine ⟨g, ?_, hgood⟩
  intro T hT T' hT'
  rw [Finset.disjoint_left]
  intro e heT heT'g
  rw [Finset.mem_image] at heT'g
  obtain ⟨e', he'T', heq⟩ := heT'g
  apply hgK
  change g ∈ hbad.toFinset
  rw [Set.Finite.mem_toFinset]
  have he'U : e' ∈ U := Finset.mem_biUnion.mpr ⟨T', hT', he'T'⟩
  have heU : e ∈ U := Finset.mem_biUnion.mpr ⟨T, hT, heT⟩
  exact Set.mem_biUnion he'U (Set.mem_biUnion heU (by
    simpa only [Set.mem_setOf_eq] using heq))



theorem fmu_finsetExpansion_pairMixing [Infinite G] [Countable E]
    [DecidableEq E] {mu : Measure (ConfigSpace E)} [IsProbabilityMeasure mu]
    (hsolution : ∀ a b : E, {g : G | g • a = b}.Finite)
    (hti : IsTranslationInvariant (G := G) mu)
    (hmix : fmu_PairMixing (G := G) mu)
    {I : Type*} [DecidableEq I] (indices : Finset I)
    (support : I -> Finset E) (c c' : I -> Real)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ g : G, (∀ i ∈ indices, ∀ j ∈ indices,
        Disjoint (support i) ((support j).image (fun e => g⁻¹ • e))) ∧
      abs ((∫ omega, (∑ i ∈ indices, c i * fmu_moInd (support i) omega) *
          (∑ j ∈ indices, c' j * fmu_moInd (support j) (shift g omega)) ∂mu) -
        (∑ i ∈ indices, c i * mu.real (fmu_multiOpen (support i))) *
          (∑ j ∈ indices, c' j * mu.real (fmu_multiOpen (support j)))) < epsilon := by
  classical
  let P := indices.image support
  let W := ∑ i ∈ indices, ∑ j ∈ indices, |c i * c' j|
  have hW : 0 <= W := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact abs_nonneg _
  let delta := epsilon / (W + 1)
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  obtain ⟨g, hdisj, hgood⟩ :=
    fmu_pairMixing_exists_disjoint hsolution hti hmix P delta hdelta
  refine ⟨g, ?_, ?_⟩
  · intro i hi j hj
    exact hdisj (support i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      (support j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  have hint :
      (∫ omega, (∑ i ∈ indices, c i * fmu_moInd (support i) omega) *
          (∑ j ∈ indices, c' j * fmu_moInd (support j) (shift g omega)) ∂mu) =
        ∑ i ∈ indices, ∑ j ∈ indices, c i * c' j *
          mu.real (fmu_multiOpen (support i) ∩
            (shift g : ConfigSpace E -> ConfigSpace E) ⁻¹'
              fmu_multiOpen (support j)) := by
    have hpoint : ∀ omega,
        (∑ i ∈ indices, c i * fmu_moInd (support i) omega) *
            (∑ j ∈ indices, c' j * fmu_moInd (support j) (shift g omega)) =
          ∑ i ∈ indices, ∑ j ∈ indices,
            (c i * c' j) * (fmu_moInd (support i) omega *
              fmu_moInd (support j) (shift g omega)) := by
      intro omega
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    simp_rw [hpoint]
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [MeasureTheory.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [MeasureTheory.integral_const_mul]
        congr 1
        rw [fmu_moInd_mul_shift_eq g (support i) (support j)]
        rw [MeasureTheory.integral_indicator_const (1 : Real)
          ((fmu_multiOpen_measurable (support i)).inter
            ((fmu_multiOpen_measurable (support j)).preimage
              (measurable_shift g)))]
        simp
      · intro j hj
        exact (fmu_integrable_moInd_mul_shift g (support i) (support j)).const_mul _
    · intro i hi
      apply MeasureTheory.integrable_finsetSum
      intro j hj
      exact (fmu_integrable_moInd_mul_shift g (support i) (support j)).const_mul _
  rw [hint, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  have hdiff (i : I) :
      (∑ j ∈ indices, c i * c' j *
          mu.real (fmu_multiOpen (support i) ∩
            (shift g : ConfigSpace E -> ConfigSpace E) ⁻¹'
              fmu_multiOpen (support j))) -
        ∑ j ∈ indices,
          (c i * mu.real (fmu_multiOpen (support i))) *
            (c' j * mu.real (fmu_multiOpen (support j))) =
      ∑ j ∈ indices, c i * c' j *
        (mu.real (fmu_multiOpen (support i) ∩
            (shift g : ConfigSpace E -> ConfigSpace E) ⁻¹'
              fmu_multiOpen (support j)) -
          mu.real (fmu_multiOpen (support i)) *
            mu.real (fmu_multiOpen (support j))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [hdiff]
  calc
    abs (∑ i ∈ indices, ∑ j ∈ indices, c i * c' j *
        (mu.real (fmu_multiOpen (support i) ∩
            (shift g : ConfigSpace E -> ConfigSpace E) ⁻¹'
              fmu_multiOpen (support j)) -
          mu.real (fmu_multiOpen (support i)) *
            mu.real (fmu_multiOpen (support j))))
        <= ∑ i ∈ indices, ∑ j ∈ indices, abs (c i * c' j *
          (mu.real (fmu_multiOpen (support i) ∩
              (shift g : ConfigSpace E -> ConfigSpace E) ⁻¹'
                fmu_multiOpen (support j)) -
            mu.real (fmu_multiOpen (support i)) *
              mu.real (fmu_multiOpen (support j)))) := by
          apply (Finset.abs_sum_le_sum_abs _ _).trans
          apply Finset.sum_le_sum
          intro i hi
          exact Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ i ∈ indices, ∑ j ∈ indices, |c i * c' j| * delta := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact (hgood (support i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
            (support j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)).le
    _ = W * delta := by
          dsimp [W]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
    _ < epsilon := by
          dsimp [delta]
          have hne : W + 1 ≠ 0 := by positivity
          have hpos : 0 < epsilon / (W + 1) := by positivity
          calc
            W * (epsilon / (W + 1)) < (W + 1) * (epsilon / (W + 1)) :=
              mul_lt_mul_of_pos_right (by linarith) hpos
            _ = epsilon := mul_div_cancel₀ epsilon hne



theorem fmu_finsetExpansion_family_pairMixing [Infinite G] [Countable E]
    [DecidableEq E] {mu : Measure (ConfigSpace E)} [IsProbabilityMeasure mu]
    (hsolution : ∀ a b : E, {g : G | g • a = b}.Finite)
    (hti : IsTranslationInvariant (G := G) mu)
    (hmix : fmu_PairMixing (G := G) mu)
    {I : Type*} [DecidableEq I] (indices : Finset I)
    (support : I -> Finset E) (coeffs : Finset (I -> Real))
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ g : G, (∀ i ∈ indices, ∀ j ∈ indices,
        Disjoint (support i) ((support j).image (fun e => g⁻¹ • e))) ∧
      ∀ c ∈ coeffs, ∀ c' ∈ coeffs,
        abs ((∫ omega, (∑ i ∈ indices, c i * fmu_moInd (support i) omega) *
            (∑ j ∈ indices, c' j * fmu_moInd (support j) (shift g omega)) ∂mu) -
          (∑ i ∈ indices, c i * mu.real (fmu_multiOpen (support i))) *
            (∑ j ∈ indices, c' j * mu.real (fmu_multiOpen (support j)))) <
          epsilon := by
  classical
  let M := ∑ c ∈ coeffs, ∑ i ∈ indices, |c i|
  have hM : 0 <= M := by
    apply Finset.sum_nonneg
    intro c hc
    apply Finset.sum_nonneg
    intro i hi
    exact abs_nonneg _
  let delta := epsilon / (M * M + 1)
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  let P := indices.image support
  obtain ⟨g, hdisj, hgood⟩ :=
    fmu_pairMixing_exists_disjoint hsolution hti hmix P delta hdelta
  refine ⟨g, ?_, ?_⟩
  · intro i hi j hj
    exact hdisj (support i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      (support j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  intro c hc c' hc'
  have hcM : (∑ i ∈ indices, |c i|) <= M := by
    dsimp [M]
    exact Finset.single_le_sum
      (fun a ha => Finset.sum_nonneg fun i hi => abs_nonneg (a i)) hc
  have hc'M : (∑ i ∈ indices, |c' i|) <= M := by
    dsimp [M]
    exact Finset.single_le_sum
      (fun a ha => Finset.sum_nonneg fun i hi => abs_nonneg (a i)) hc'
  have hint :
      (∫ omega, (∑ i ∈ indices, c i * fmu_moInd (support i) omega) *
          (∑ j ∈ indices, c' j * fmu_moInd (support j) (shift g omega)) ∂mu) =
        ∑ i ∈ indices, ∑ j ∈ indices, c i * c' j *
          mu.real (fmu_multiOpen (support i) ∩
            (shift g : ConfigSpace E -> ConfigSpace E) ⁻¹'
              fmu_multiOpen (support j)) := by
    have hpoint : ∀ omega,
        (∑ i ∈ indices, c i * fmu_moInd (support i) omega) *
            (∑ j ∈ indices, c' j * fmu_moInd (support j) (shift g omega)) =
          ∑ i ∈ indices, ∑ j ∈ indices,
            (c i * c' j) * (fmu_moInd (support i) omega *
              fmu_moInd (support j) (shift g omega)) := by
      intro omega
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    simp_rw [hpoint]
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [MeasureTheory.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [MeasureTheory.integral_const_mul]
        congr 1
        rw [fmu_moInd_mul_shift_eq g (support i) (support j)]
        rw [MeasureTheory.integral_indicator_const (1 : Real)
          ((fmu_multiOpen_measurable (support i)).inter
            ((fmu_multiOpen_measurable (support j)).preimage
              (measurable_shift g)))]
        simp
      · intro j hj
        exact (fmu_integrable_moInd_mul_shift g (support i) (support j)).const_mul _
    · intro i hi
      apply MeasureTheory.integrable_finsetSum
      intro j hj
      exact (fmu_integrable_moInd_mul_shift g (support i) (support j)).const_mul _
  rw [hint, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  have hdiff (i : I) :
      (∑ j ∈ indices, c i * c' j *
          mu.real (fmu_multiOpen (support i) ∩
            (shift g : ConfigSpace E -> ConfigSpace E) ⁻¹'
              fmu_multiOpen (support j))) -
        ∑ j ∈ indices,
          (c i * mu.real (fmu_multiOpen (support i))) *
            (c' j * mu.real (fmu_multiOpen (support j))) =
      ∑ j ∈ indices, c i * c' j *
        (mu.real (fmu_multiOpen (support i) ∩
            (shift g : ConfigSpace E -> ConfigSpace E) ⁻¹'
              fmu_multiOpen (support j)) -
          mu.real (fmu_multiOpen (support i)) *
            mu.real (fmu_multiOpen (support j))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [hdiff]
  calc
    abs (∑ i ∈ indices, ∑ j ∈ indices, c i * c' j *
        (mu.real (fmu_multiOpen (support i) ∩
            (shift g : ConfigSpace E -> ConfigSpace E) ⁻¹'
              fmu_multiOpen (support j)) -
          mu.real (fmu_multiOpen (support i)) *
            mu.real (fmu_multiOpen (support j))))
        <= ∑ i ∈ indices, ∑ j ∈ indices, |c i| * |c' j| * delta := by
          calc
            _ <= ∑ i ∈ indices, ∑ j ∈ indices, abs (c i * c' j *
                (mu.real (fmu_multiOpen (support i) ∩
                    (shift g : ConfigSpace E -> ConfigSpace E) ⁻¹'
                      fmu_multiOpen (support j)) -
                  mu.real (fmu_multiOpen (support i)) *
                    mu.real (fmu_multiOpen (support j)))) := by
                  apply (Finset.abs_sum_le_sum_abs _ _).trans
                  apply Finset.sum_le_sum
                  intro i hi
                  exact Finset.abs_sum_le_sum_abs _ _
            _ <= ∑ i ∈ indices, ∑ j ∈ indices, |c i| * |c' j| * delta := by
                  apply Finset.sum_le_sum
                  intro i hi
                  apply Finset.sum_le_sum
                  intro j hj
                  rw [abs_mul, abs_mul]
                  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
                  exact (hgood (support i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
                    (support j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)).le
    _ = (∑ i ∈ indices, |c i|) * (∑ j ∈ indices, |c' j|) * delta := by
          rw [Finset.sum_mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
    _ <= (M * M) * delta := by
          apply mul_le_mul_of_nonneg_right _ hdelta.le
          exact mul_le_mul hcM hc'M
            (Finset.sum_nonneg fun i hi => abs_nonneg (c' i)) hM
    _ < epsilon := by
          dsimp [delta]
          have hne : M * M + 1 ≠ 0 := by positivity
          have hpos : 0 < epsilon / (M * M + 1) := by positivity
          calc
            M * M * (epsilon / (M * M + 1)) <
                (M * M + 1) * (epsilon / (M * M + 1)) :=
              mul_lt_mul_of_pos_right (by linarith) hpos
            _ = epsilon := mul_div_cancel₀ epsilon hne

end StatMech.FK
