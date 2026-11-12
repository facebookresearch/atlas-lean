/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FK.FKUniquenessSkeleton
import Code.FK.Ergodicity

open MeasureTheory
open scoped BigOperators StatMech

namespace StatMech
namespace FK

section Finite

variable {E : Type*} [Fintype E] [DecidableEq E]

private noncomputable def emi_gap (z : ConfigSpace E × ConfigSpace E) : ℝ :=
  ∑ e : E, ((if z.2 e then (1 : ℝ) else 0) - (if z.1 e then (1 : ℝ) else 0))

private theorem emi_bool_gap_nonneg {b c : Bool} (h : b ≤ c) :
    (0 : ℝ) ≤ (if c then 1 else 0) - (if b then 1 else 0) := by
  cases b <;> cases c <;> norm_num at h ⊢
  exact (by decide : ¬(true ≤ false)) h

private theorem emi_bool_gap_eq_one {b c : Bool} (h : b ≤ c) (hne : b ≠ c) :
    (if c then (1 : ℝ) else 0) - (if b then (1 : ℝ) else 0) = 1 := by
  cases b <;> cases c
  · exact (hne rfl).elim
  · norm_num
  · exact ((by decide : ¬(true ≤ false)) h).elim
  · exact (hne rfl).elim

private theorem emi_gap_nonneg_of_le {z : ConfigSpace E × ConfigSpace E}
    (hz : z.1 ≤ z.2) : 0 ≤ emi_gap z := by
  unfold emi_gap
  apply Finset.sum_nonneg
  intro e _
  exact emi_bool_gap_nonneg (hz e)

private theorem emi_one_le_gap_of_le_ne {z : ConfigSpace E × ConfigSpace E}
    (hz : z.1 ≤ z.2) (hne : z.1 ≠ z.2) : 1 ≤ emi_gap z := by
  have hex : ∃ e : E, z.1 e ≠ z.2 e := by
    by_contra h
    apply hne
    funext e
    exact not_ne_iff.mp (not_exists.mp h e)
  obtain ⟨e, he⟩ := hex
  unfold emi_gap
  calc
    (1 : ℝ) =
        (if z.2 e then (1 : ℝ) else 0) - (if z.1 e then (1 : ℝ) else 0) :=
      (emi_bool_gap_eq_one (hz e) he).symm
    _ ≤ ∑ i ∈ Finset.univ,
        ((if z.2 i then (1 : ℝ) else 0) - (if z.1 i then (1 : ℝ) else 0)) :=
      Finset.single_le_sum (fun i _ => emi_bool_gap_nonneg (hz i)) (Finset.mem_univ e)
    _ = ∑ i : E,
        ((if z.2 i then (1 : ℝ) else 0) - (if z.1 i then (1 : ℝ) else 0)) := rfl



theorem emi_mass_eq_of_edgeMarg_eq
    {P : ConfigSpace E × ConfigSpace E → ℝ} {μ ν : ConfigSpace E → ℝ}
    (hP : IsMonotoneCouplingFun P μ ν)
    (hmarg : ∀ e, edgeMargProb μ e = edgeMargProb ν e) : μ = ν := by
  classical
  have htotal : ∑ z : ConfigSpace E × ConfigSpace E, emi_gap z * P z = 0 := by
    rw [show (∑ z : ConfigSpace E × ConfigSpace E, emi_gap z * P z) =
        ∑ e : E, (edgeMargProb ν e - edgeMargProb μ e) by
      calc
        ∑ z : ConfigSpace E × ConfigSpace E, emi_gap z * P z =
            ∑ z : ConfigSpace E × ConfigSpace E, ∑ e : E,
              ((if z.2 e then (1 : ℝ) else 0) - (if z.1 e then (1 : ℝ) else 0)) * P z := by
          apply Finset.sum_congr rfl
          intro z _
          rw [emi_gap, Finset.sum_mul]
        _ = ∑ e : E, ∑ z : ConfigSpace E × ConfigSpace E,
              ((if z.2 e then (1 : ℝ) else 0) - (if z.1 e then (1 : ℝ) else 0)) * P z :=
          Finset.sum_comm
        _ = ∑ e : E, (edgeMargProb ν e - edgeMargProb μ e) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [edgeMarg_eq_coupling_snd hP e, edgeMarg_eq_coupling_fst hP e,
            ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro z _
          ring]
    exact Finset.sum_eq_zero fun e _ => by rw [hmarg e]; ring
  have hoff : ∀ z : ConfigSpace E × ConfigSpace E, z.1 ≠ z.2 → P z = 0 := by
    intro z hne
    by_cases hle : z.1 ≤ z.2
    · have hterm_nonneg : ∀ w : ConfigSpace E × ConfigSpace E, 0 ≤ emi_gap w * P w := by
        intro w
        by_cases hw : w.1 ≤ w.2
        · exact mul_nonneg (emi_gap_nonneg_of_le hw) (hP.nonneg w)
        · rw [hP.supportLE w hw, mul_zero]
      have hsingle : emi_gap z * P z ≤
          ∑ w : ConfigSpace E × ConfigSpace E, emi_gap w * P w :=
        Finset.single_le_sum (fun w _ => hterm_nonneg w) (Finset.mem_univ z)
      have hPle : P z ≤ emi_gap z * P z := by
        have := mul_le_mul_of_nonneg_right (emi_one_le_gap_of_le_ne hle hne) (hP.nonneg z)
        simpa using this
      rw [htotal] at hsingle
      exact le_antisymm (hPle.trans hsingle) (hP.nonneg z)
    · exact hP.supportLE z hle
  funext ω
  rw [← hP.fst_marginal ω, ← hP.snd_marginal ω]
  calc
    ∑ y : ConfigSpace E, P (ω, y) = P (ω, ω) := by
      rw [Finset.sum_eq_single ω]
      · intro y _ hy; exact hoff (ω, y) (fun h => hy h.symm)
      · simp
    _ = ∑ x : ConfigSpace E, P (x, ω) := by
      symm
      rw [Finset.sum_eq_single ω]
      · intro x _ hx; exact hoff (x, ω) (by simpa [eq_comm] using hx)
      · simp

end Finite

section Infinite

variable {E : Type*} [DecidableEq E]





theorem infiniteMeasure_eq_of_edgeMarg_eq
    (μ ν : Measure (ConfigSpace E)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hdom : μ ≼ ν)
    (hmarg : ∀ e : E, μ.real {ω | ω e = true} = ν.real {ω | ω e = true}) :
    μ = ν := by
  classical
  have hcyl : ∀ (F : Finset E) (A : Set (ConfigSpace F)),
      μ (cylinder F A) = ν (cylinder F A) := by
    intro F A
    let r : ConfigSpace E → ConfigSpace F := Finset.restrict F
    have hr : Measurable r :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply (i : E))
    let μF : ConfigSpace F → ℝ := fun η => μ.real (r ⁻¹' {η})
    let νF : ConfigSpace F → ℝ := fun η => ν.real (r ⁻¹' {η})
    have hμF : 0 ≤ μF := fun _ => measureReal_nonneg
    have hνF : 0 ≤ νF := fun _ => measureReal_nonneg
    have hsumμ : ∑ η, μF η = 1 := fuc_sum_real_preimage_eq_one μ r hr
    have hsumν : ∑ η, νF η = 1 := fuc_sum_real_preimage_eq_one ν r hr
    have hrealμ : ∀ B : Set (ConfigSpace F),
        (measOfMass μF).real B = μ.real (r ⁻¹' B) := by
      intro B
      rw [measOfMass_real_eq_indicator_sum μF hμF]
      exact (fuc_real_preimage_eq_indicator_sum μ r hr B).symm
    have hrealν : ∀ B : Set (ConfigSpace F),
        (measOfMass νF).real B = ν.real (r ⁻¹' B) := by
      intro B
      rw [measOfMass_real_eq_indicator_sum νF hνF]
      exact (fuc_real_preimage_eq_indicator_sum ν r hr B).symm
    have hdomF : measOfMass μF ≼ measOfMass νF := by
      intro B _hB hBinc
      rw [hrealμ B, hrealν B]
      apply hdom (r ⁻¹' B) (hr MeasurableSet.of_discrete)
      intro ω ω' hle hω
      exact hBinc (fun i => hle i.1) hω
    obtain ⟨P, hP⟩ := fuc_isMonotoneCouplingFun_of_dominated
      hμF hνF hsumμ hsumν hdomF
    have hmargF : ∀ e : F, edgeMargProb μF e = edgeMargProb νF e := by
      intro e
      let B : Set (ConfigSpace F) := {η | η e = true}
      have hμedge : edgeMargProb μF e = μ.real (r ⁻¹' B) := by
        calc
          edgeMargProb μF e = eventMassProb μF B := by
            unfold edgeMargProb eventMassProb B
            apply Finset.sum_congr rfl
            intro η _
            by_cases hη : η e = true <;> simp [Set.indicator, hη]
          _ = μ.real (r ⁻¹' B) := (fuc_real_preimage_eq_indicator_sum μ r hr B).symm
      have hνedge : edgeMargProb νF e = ν.real (r ⁻¹' B) := by
        calc
          edgeMargProb νF e = eventMassProb νF B := by
            unfold edgeMargProb eventMassProb B
            apply Finset.sum_congr rfl
            intro η _
            by_cases hη : η e = true <;> simp [Set.indicator, hη]
          _ = ν.real (r ⁻¹' B) := (fuc_real_preimage_eq_indicator_sum ν r hr B).symm
      rw [hμedge, hνedge]
      have hpre : r ⁻¹' B = {ω : ConfigSpace E | ω e.1 = true} := by
        ext ω
        rfl
      rw [hpre, hmarg e.1]
    have hmass : μF = νF := emi_mass_eq_of_edgeMarg_eq hP hmargF
    have hreal : μ.real (cylinder F A) = ν.real (cylinder F A) := by
      change μ.real (r ⁻¹' A) = ν.real (r ⁻¹' A)
      rw [← hrealμ A, ← hrealν A, hmass]
    unfold Measure.real at hreal
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _)).mp hreal
  apply ext_of_generate_finite (measurableCylinders (fun _ : E => Bool))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro C hC
    obtain ⟨F, A, _hA, rfl⟩ := (mem_measurableCylinders C).mp hC
    exact hcyl F A
  · rw [measure_univ, measure_univ]

end Infinite

end FK
end StatMech
