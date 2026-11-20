/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.FKMixingUpperClose

open MeasureTheory Set
open scoped BigOperators

namespace StatMech.FK

open ConfigSpace

variable {E G : Type*} [Group G] [MulAction G E]
variable {mu : Measure (ConfigSpace E)}


theorem fmu_real_inter_shift_eq_cross_sum [Countable E]
    [IsProbabilityMeasure mu]
    (g : G) {A B : Set (ConfigSpace E)}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (P Q : Finset (Finset E)) (c e : Finset E -> Real)
    (hAexp : forall omega,
      A.indicator (fun _ => (1 : Real)) omega =
        ∑ T ∈ P, c T * fmu_moInd T omega)
    (hBexp : forall omega,
      B.indicator (fun _ => (1 : Real)) omega =
        ∑ U ∈ Q, e U * fmu_moInd U omega) :
    mu.real (A ∩ (shift g) ⁻¹' B) =
      ∑ T ∈ P, ∑ U ∈ Q, c T * e U *
        mu.real (fmu_multiOpen T ∩
          (shift g : ConfigSpace E -> ConfigSpace E) ⁻¹'
            fmu_multiOpen U) := by
  classical
  have hAB : MeasurableSet (A ∩ (shift g) ⁻¹' B) :=
    hA.inter (hB.preimage (measurable_shift g))
  have hkey : mu.real (A ∩ (shift g) ⁻¹' B) =
      ∫ omega, A.indicator (fun _ => (1 : Real)) omega *
        B.indicator (fun _ => (1 : Real)) (shift g omega) ∂mu := by
    rw [show mu.real (A ∩ (shift g) ⁻¹' B) =
        ∫ omega, (A ∩ (shift g) ⁻¹' B).indicator
          (fun _ => (1 : Real)) omega ∂mu from by
      rw [integral_indicator_const (1 : Real) hAB]
      simp]
    apply integral_congr_ae
    filter_upwards with omega
    by_cases ha : omega ∈ A <;>
      by_cases hb : shift g omega ∈ B <;>
      simp [ha, hb]
  rw [hkey]
  simp_rw [hAexp, hBexp]
  have hpoint : forall omega,
      (∑ T ∈ P, c T * fmu_moInd T omega) *
          (∑ U ∈ Q, e U * fmu_moInd U (shift g omega)) =
        ∑ T ∈ P, ∑ U ∈ Q, (c T * e U) *
          (fmu_moInd T omega * fmu_moInd U (shift g omega)) := by
    intro omega
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    apply Finset.sum_congr rfl
    intro U hU
    ring
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro T hT
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro U hU
      rw [integral_const_mul]
      congr 1
      rw [fmu_moInd_mul_shift_eq g T U]
      rw [integral_indicator_const (1 : Real)
        ((fmu_multiOpen_measurable T).inter
          ((fmu_multiOpen_measurable U).preimage (measurable_shift g)))]
      simp
    · intro U hU
      exact (fmu_integrable_moInd_mul_shift g T U).const_mul _
  · intro T hT
    apply integrable_finsetSum
    intro U hU
    exact (fmu_integrable_moInd_mul_shift g T U).const_mul _

set_option maxHeartbeats 2000000 in



theorem fmu_genMixing_of_pairMixing [Countable E]
    [IsProbabilityMeasure mu]
    (hmix : fmu_PairMixing (G := G) mu) :
    fmu_GenMixing (G := G) mu := by
  classical
  intro family hfamily epsilon hepsilon
  let members := family.attach
  let support (A : ↑family) : Finset (Finset E) :=
    (fmu_cylinder_expand A.1 (hfamily A.1 A.2)).choose
  let baseCoeff (A : ↑family) : Finset E -> Real :=
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
  let coeff (A : ↑family) : Finset E -> Real := fun T =>
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
  let coeffs : Finset (Finset E -> Real) := members.image coeff
  let M : Real := ∑ c ∈ coeffs, ∑ T ∈ indices, abs (c T)
  have hM : 0 <= M := by
    dsimp [M]
    positivity
  let delta := epsilon / (M * M + 1)
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  obtain ⟨g, hgood⟩ := hmix indices delta hdelta
  refine ⟨g, ?_⟩
  intro A hA B hB
  let a : ↑family := ⟨A, hA⟩
  let b : ↑family := ⟨B, hB⟩
  have ha : coeff a ∈ coeffs :=
    Finset.mem_image.mpr ⟨a, Finset.mem_attach _ a, rfl⟩
  have hb : coeff b ∈ coeffs :=
    Finset.mem_image.mpr ⟨b, Finset.mem_attach _ b, rfl⟩
  have hca : (∑ T ∈ indices, abs (coeff a T)) <= M := by
    dsimp [M]
    exact Finset.single_le_sum
      (fun c hc => Finset.sum_nonneg fun T hT => abs_nonneg (c T)) ha
  have hcb : (∑ T ∈ indices, abs (coeff b T)) <= M := by
    dsimp [M]
    exact Finset.single_le_sum
      (fun c hc => Finset.sum_nonneg fun T hT => abs_nonneg (c T)) hb
  have hAmeas : MeasurableSet A :=
    MeasurableSet.of_mem_measurableCylinders (hfamily A hA)
  have hBmeas : MeasurableSet B :=
    MeasurableSet.of_mem_measurableCylinders (hfamily B hB)
  rw [fmu_real_inter_shift_eq_cross_sum g hAmeas hBmeas
      indices indices (coeff a) (coeff b) (hexp a) (hexp b),
    fmu_real_eq_sum hAmeas indices (coeff a) (hexp a),
    fmu_real_eq_sum hBmeas indices (coeff b) (hexp b),
    Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  have hdiff (T : Finset E) :
      (∑ U ∈ indices, coeff a T * coeff b U *
          mu.real (fmu_multiOpen T ∩
            (shift g : ConfigSpace E -> ConfigSpace E) ⁻¹'
              fmu_multiOpen U)) -
        (∑ U ∈ indices,
          (coeff a T * mu.real (fmu_multiOpen T)) *
            (coeff b U * mu.real (fmu_multiOpen U))) =
      ∑ U ∈ indices, coeff a T * coeff b U *
        (mu.real (fmu_multiOpen T ∩
            (shift g : ConfigSpace E -> ConfigSpace E) ⁻¹'
              fmu_multiOpen U) -
          mu.real (fmu_multiOpen T) *
            mu.real (fmu_multiOpen U)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro U hU
    ring
  simp_rw [hdiff]
  calc
    abs (∑ T ∈ indices, ∑ U ∈ indices,
        coeff a T * coeff b U *
          (mu.real (fmu_multiOpen T ∩
              (shift g : ConfigSpace E -> ConfigSpace E) ⁻¹'
                fmu_multiOpen U) -
            mu.real (fmu_multiOpen T) *
              mu.real (fmu_multiOpen U))) <=
      ∑ T ∈ indices, ∑ U ∈ indices,
        abs (coeff a T) * abs (coeff b U) * delta := by
      calc
        _ <= ∑ T ∈ indices, abs (∑ U ∈ indices,
            coeff a T * coeff b U *
              (mu.real (fmu_multiOpen T ∩
                  (shift g : ConfigSpace E -> ConfigSpace E) ⁻¹'
                    fmu_multiOpen U) -
                mu.real (fmu_multiOpen T) *
                  mu.real (fmu_multiOpen U))) :=
          Finset.abs_sum_le_sum_abs _ _
        _ <= _ := by
          apply Finset.sum_le_sum
          intro T hT
          calc
            _ <= ∑ U ∈ indices, abs (coeff a T * coeff b U *
                (mu.real (fmu_multiOpen T ∩
                    (shift g : ConfigSpace E -> ConfigSpace E) ⁻¹'
                      fmu_multiOpen U) -
                  mu.real (fmu_multiOpen T) *
                    mu.real (fmu_multiOpen U))) :=
              Finset.abs_sum_le_sum_abs _ _
            _ <= _ := by
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
    _ <= M * M * delta := by
      apply mul_le_mul_of_nonneg_right _ hdelta.le
      exact mul_le_mul hca hcb
        (Finset.sum_nonneg fun U hU => abs_nonneg _)
        hM
    _ < epsilon := by
      dsimp [delta]
      have hden : M * M + 1 ≠ 0 := by positivity
      have hpos : 0 < epsilon / (M * M + 1) := by positivity
      calc
        M * M * (epsilon / (M * M + 1)) <
            (M * M + 1) * (epsilon / (M * M + 1)) :=
          mul_lt_mul_of_pos_right (by linarith) hpos
        _ = epsilon := mul_div_cancel₀ epsilon hden

end StatMech.FK
