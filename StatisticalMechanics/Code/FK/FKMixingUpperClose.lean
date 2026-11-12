/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































































import Mathlib
import Code.FK.FKMixingClose
import Code.FK.CylinderDecayClose

open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open ConfigSpace

variable {E : Type*} {G : Type*} [Group G] [MulAction G E]




def fmu_multiOpen (T : Finset E) : Set (ConfigSpace E) := {ω | ∀ e ∈ T, ω e = true}


noncomputable def fmu_xR (ω : ConfigSpace E) (e : E) : ℝ := if ω e then 1 else 0


noncomputable def fmu_moInd (T : Finset E) (ω : ConfigSpace E) : ℝ := ∏ e ∈ T, fmu_xR ω e


theorem fmu_moInd_eq_indicator (T : Finset E) (ω : ConfigSpace E) :
    fmu_moInd T ω = (fmu_multiOpen T).indicator (fun _ => (1:ℝ)) ω := by
  unfold fmu_moInd fmu_xR fmu_multiOpen; classical
  by_cases h : ω ∈ {ω : ConfigSpace E | ∀ e ∈ T, ω e = true}
  · rw [Set.indicator_of_mem h]; apply Finset.prod_eq_one; intro e he; rw [if_pos (h e he)]
  · rw [Set.indicator_of_notMem h]; simp only [Set.mem_setOf_eq, not_forall] at h
    obtain ⟨e, he, hee⟩ := h; apply Finset.prod_eq_zero he; rw [if_neg (by simpa using hee)]


theorem fmu_multiOpen_measurable [Countable E] (T : Finset E) :
    MeasurableSet (fmu_multiOpen T) := by
  have : fmu_multiOpen T = ⋂ e ∈ T, {ω : ConfigSpace E | ω e = true} := by
    ext ω; simp only [fmu_multiOpen, Set.mem_setOf_eq, Set.mem_iInter]
  rw [this]
  exact MeasurableSet.biInter T.countable_toSet
    (fun e _ => measurableSet_eq_fun (measurable_pi_apply e) measurable_const)


theorem fmu_multiOpen_isIncreasing (T : Finset E) : IsIncreasing (fmu_multiOpen T) := by
  intro a b hab ha e he
  have hle := hab e
  rw [ha e he] at hle
  exact le_antisymm (by simp) hle


theorem fmu_shift_multiOpen [DecidableEq E] (g : G) (T : Finset E) :
    (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' (fmu_multiOpen T)
      = fmu_multiOpen (T.image (fun e => g⁻¹ • e)) := by
  ext ω
  simp only [Set.mem_preimage, fmu_multiOpen, Set.mem_setOf_eq, shift_apply, Finset.mem_image,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]




theorem fmu_indicator_mul_indicator (A B : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    A.indicator (fun _ => (1:ℝ)) ω * B.indicator (fun _ => (1:ℝ)) ω
      = (A ∩ B).indicator (fun _ => (1:ℝ)) ω := by
  rw [← Set.inter_indicator_mul]; simp


theorem fmu_moInd_comp_shift (g : G) (T : Finset E) (ω : ConfigSpace E) :
    fmu_moInd T (shift g ω)
      = ((shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T).indicator
          (fun _ => (1:ℝ)) ω := by
  rw [fmu_moInd_eq_indicator]
  exact (Set.indicator_comp_right (s := fmu_multiOpen T)
    (f := (shift g : ConfigSpace E → ConfigSpace E)) (g := fun _ => (1:ℝ)) (x := ω)).symm


theorem fmu_moInd_mul_shift_eq [Countable E] (g : G) (T T' : Finset E) :
    (fun ω => fmu_moInd T ω * fmu_moInd T' (shift g ω))
      = (fmu_multiOpen T ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T').indicator
          (fun _ => (1:ℝ)) := by
  funext ω; rw [fmu_moInd_eq_indicator, fmu_moInd_comp_shift, fmu_indicator_mul_indicator]

variable {μ : Measure (ConfigSpace E)} [IsProbabilityMeasure μ]

theorem fmu_integrable_moInd [Countable E] (T : Finset E) : Integrable (fmu_moInd T) μ := by
  have : fmu_moInd T = (fmu_multiOpen T).indicator (fun _ => (1:ℝ)) := by
    funext ω; exact fmu_moInd_eq_indicator T ω
  rw [this]; exact (MeasureTheory.integrable_const (1:ℝ)).indicator (fmu_multiOpen_measurable T)

theorem fmu_integrable_moInd_mul_shift [Countable E] (g : G) (T T' : Finset E) :
    Integrable (fun ω => fmu_moInd T ω * fmu_moInd T' (shift g ω)) μ := by
  rw [fmu_moInd_mul_shift_eq g T T']
  exact (MeasureTheory.integrable_const (1:ℝ)).indicator
    ((fmu_multiOpen_measurable T).inter
      ((fmu_multiOpen_measurable T').preimage (measurable_shift g)))

theorem fmu_integral_moInd [Countable E] (T : Finset E) :
    (∫ ω, fmu_moInd T ω ∂μ) = μ.real (fmu_multiOpen T) := by
  simp_rw [fmu_moInd_eq_indicator]
  rw [MeasureTheory.integral_indicator_const (1:ℝ) (fmu_multiOpen_measurable T)]; simp









noncomputable def fmu_traceInd (F : Finset E) (τ : E → Bool) (ω : ConfigSpace E) : ℝ :=
  if (∀ e ∈ F, ω e = τ e) then 1 else 0


noncomputable def fmu_traceCoef [DecidableEq E] (F : Finset E) (τ : E → Bool) (T : Finset E) : ℝ :=
  (∏ e ∈ T, (if τ e then (1:ℝ) else -1)) * (∏ e ∈ F \ T, (if τ e then (0:ℝ) else 1))


theorem fmu_traceInd_eq_prod (F : Finset E) (τ : E → Bool) (ω : ConfigSpace E) :
    fmu_traceInd F τ ω = ∏ e ∈ F, (if τ e then fmu_xR ω e else (1 - fmu_xR ω e)) := by
  unfold fmu_traceInd fmu_xR; classical
  by_cases h : ∀ e ∈ F, ω e = τ e
  · rw [if_pos h]; symm; apply Finset.prod_eq_one; intro e he
    have : ω e = τ e := h e he
    rcases hτ : τ e with _ | _ <;> rw [hτ] at this <;> simp_all
  · rw [if_neg h]; symm
    rw [not_forall] at h; obtain ⟨e, he⟩ := h; rw [Classical.not_imp] at he
    obtain ⟨heF, hev⟩ := he
    apply Finset.prod_eq_zero heF
    rcases hτ : τ e with _ | _ <;> rcases hω : ω e with _ | _ <;> simp_all


theorem fmu_traceInd_expand [DecidableEq E] (F : Finset E) (τ : E → Bool) (ω : ConfigSpace E) :
    fmu_traceInd F τ ω = ∑ T ∈ F.powerset, fmu_traceCoef F τ T * fmu_moInd T ω := by
  rw [fmu_traceInd_eq_prod]
  have hfac : ∀ e, (if τ e then fmu_xR ω e else (1 - fmu_xR ω e))
      = (if τ e then (1:ℝ) else -1) * fmu_xR ω e + (if τ e then (0:ℝ) else 1) := by
    intro e; rcases τ e with _ | _
    · simp only [Bool.false_eq_true, if_false]; ring
    · simp only [if_true]; ring
  simp_rw [hfac]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl; intro T hT
  unfold fmu_traceCoef fmu_moInd; rw [Finset.prod_mul_distrib]; ring


theorem fmu_cylinder_indicator_eq_sum_traceInd [DecidableEq E] (F : Finset E)
    (Sf : Finset (↥F → Bool)) (ω : ConfigSpace E) :
    (cylinder F (↑Sf : Set (↥F → Bool))).indicator (fun _ => (1:ℝ)) ω
      = ∑ σ ∈ Sf, fmu_traceInd F (fun e => if h : e ∈ F then σ ⟨e, h⟩ else false) ω := by
  classical
  by_cases hmem : ω ∈ cylinder F (↑Sf : Set (↥F → Bool))
  · rw [Set.indicator_of_mem hmem]
    rw [mem_cylinder] at hmem
    rw [Finset.sum_eq_single (F.restrict ω)]
    · unfold fmu_traceInd; rw [if_pos]
      intro e he; simp only []; rw [dif_pos he, Finset.restrict_def]
    · intro σ hσ hne
      unfold fmu_traceInd; rw [if_neg]
      intro hcontra
      apply hne; funext e
      have := hcontra e.1 e.2
      simp only [Finset.restrict_def] at this ⊢
      rw [this]; simp [e.2]
    · intro h; exact absurd (Finset.mem_coe.mp hmem) h
  · rw [Set.indicator_of_notMem hmem]
    rw [mem_cylinder] at hmem
    symm; apply Finset.sum_eq_zero; intro σ hσ
    unfold fmu_traceInd; rw [if_neg]
    intro hcontra; apply hmem
    have : F.restrict ω = σ := by
      funext e; have := hcontra e.1 e.2; simp only [Finset.restrict_def] at this ⊢
      rw [this]; simp [e.2]
    rw [Finset.mem_coe, this]; exact hσ




theorem fmu_cylinder_expand [DecidableEq E] (A : Set (ConfigSpace E))
    (hA : A ∈ measurableCylinders (fun _ : E => Bool)) :
    ∃ (P : Finset (Finset E)) (c : Finset E → ℝ),
      ∀ ω, A.indicator (fun _ => (1:ℝ)) ω = ∑ T ∈ P, c T * fmu_moInd T ω := by
  classical
  rw [mem_measurableCylinders] at hA
  obtain ⟨F, S, hSmeas, rfl⟩ := hA
  set Sf : Finset (↥F → Bool) := S.toFinset with hSf
  have hScoe : S = (↑Sf : Set (↥F → Bool)) := by rw [hSf, Set.coe_toFinset]
  refine ⟨F.powerset, fun T => ∑ σ ∈ Sf,
      fmu_traceCoef F (fun e => if h : e ∈ F then σ ⟨e, h⟩ else false) T, ?_⟩
  intro ω
  rw [hScoe, fmu_cylinder_indicator_eq_sum_traceInd F Sf ω]
  simp_rw [fmu_traceInd_expand F]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro T hT
  rw [Finset.sum_mul]




theorem fmu_real_eq_sum [Countable E] {C : Set (ConfigSpace E)} (hC : MeasurableSet C)
    (P : Finset (Finset E)) (c : Finset E → ℝ)
    (hexp : ∀ ω, C.indicator (fun _ => (1:ℝ)) ω = ∑ T ∈ P, c T * fmu_moInd T ω) :
    μ.real C = ∑ T ∈ P, c T * μ.real (fmu_multiOpen T) := by
  have h1 : μ.real C = ∫ ω, C.indicator (fun _ => (1:ℝ)) ω ∂μ := by
    rw [MeasureTheory.integral_indicator_const (1:ℝ) hC]; simp
  rw [h1]
  simp_rw [hexp]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl; intro T hT
    rw [MeasureTheory.integral_const_mul, fmu_integral_moInd]
  · intro T hT
    exact (fmu_integrable_moInd T).const_mul _



theorem fmu_real_inter_shift_eq_sum [Countable E] (g : G) {C : Set (ConfigSpace E)}
    (hC : MeasurableSet C)
    (P : Finset (Finset E)) (c : Finset E → ℝ)
    (hexp : ∀ ω, C.indicator (fun _ => (1:ℝ)) ω = ∑ T ∈ P, c T * fmu_moInd T ω) :
    μ.real (C ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' C)
      = ∑ T ∈ P, ∑ T' ∈ P, c T * c T' *
          μ.real (fmu_multiOpen T ∩
            (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T') := by
  classical
  have hmeas2 : MeasurableSet (C ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' C) :=
    hC.inter (hC.preimage (measurable_shift g))
  have hkey : μ.real (C ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' C)
      = ∫ ω, (C.indicator (fun _ => (1:ℝ)) ω) * (C.indicator (fun _ => (1:ℝ)) (shift g ω)) ∂μ := by
    rw [show μ.real (C ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' C)
          = ∫ ω, (C ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' C).indicator
            (fun _ => (1:ℝ)) ω ∂μ from by
      rw [MeasureTheory.integral_indicator_const (1:ℝ) hmeas2]; simp]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with ω
    have hcomp : C.indicator (fun _ => (1:ℝ)) (shift g ω)
        = ((shift g : ConfigSpace E → ConfigSpace E) ⁻¹' C).indicator (fun _ => (1:ℝ)) ω :=
      (Set.indicator_comp_right (s := C)
        (f := (shift g : ConfigSpace E → ConfigSpace E)) (g := fun _ => (1:ℝ)) (x := ω)).symm
    rw [hcomp, fmu_indicator_mul_indicator]
  rw [hkey]
  simp_rw [hexp]
  have hpoint : ∀ ω, (∑ T ∈ P, c T * fmu_moInd T ω) *
      (∑ T' ∈ P, c T' * fmu_moInd T' (shift g ω))
      = ∑ T ∈ P, ∑ T' ∈ P, (c T * c T') * (fmu_moInd T ω * fmu_moInd T' (shift g ω)) := by
    intro ω
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro T hT
    apply Finset.sum_congr rfl; intro T' hT'; ring
  simp_rw [hpoint]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl; intro T hT
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl; intro T' hT'
      rw [MeasureTheory.integral_const_mul]
      congr 1
      rw [fmu_moInd_mul_shift_eq g T T']
      rw [MeasureTheory.integral_indicator_const (1:ℝ)
        ((fmu_multiOpen_measurable T).inter
          ((fmu_multiOpen_measurable T').preimage (measurable_shift g)))]
      simp
    · intro T' hT'
      exact (fmu_integrable_moInd_mul_shift g T T').const_mul _
  · intro T hT
    apply MeasureTheory.integrable_finsetSum
    intro T' hT'
    exact (fmu_integrable_moInd_mul_shift g T T').const_mul _













def fmu_PairMixing (μ : Measure (ConfigSpace E)) : Prop :=
  ∀ (P : Finset (Finset E)) (δ : ℝ), 0 < δ →
    ∃ g : G, ∀ T ∈ P, ∀ T' ∈ P,
      |μ.real (fmu_multiOpen T ∩
          (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T')
        - μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T')| < δ






theorem fmu_selfMixing_one_of_pairMixing [Countable E] (hmix : fmu_PairMixing (G := G) μ)
    {C : Set (ConfigSpace E)} (hC : MeasurableSet C)
    (P : Finset (Finset E)) (c : Finset E → ℝ)
    (hexp : ∀ ω, C.indicator (fun _ => (1:ℝ)) ω = ∑ T ∈ P, c T * fmu_moInd T ω)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : G, |μ.real (C ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' C)
        - (μ.real C) ^ 2| < ε := by
  classical
  set W := ∑ T ∈ P, ∑ T' ∈ P, |c T * c T'| with hW
  have hWnn : 0 ≤ W := by
    apply Finset.sum_nonneg; intro T hT; apply Finset.sum_nonneg; intro T' hT'; positivity
  set δ := ε / (W + 1) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨g, hg⟩ := hmix P δ hδpos
  refine ⟨g, ?_⟩
  rw [fmu_real_inter_shift_eq_sum g hC P c hexp]
  have hsq : (μ.real C) ^ 2 = ∑ T ∈ P, ∑ T' ∈ P,
      c T * c T' * (μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T')) := by
    rw [show (μ.real C) ^ 2 = μ.real C * μ.real C from sq _]
    rw [fmu_real_eq_sum hC P c hexp, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro T hT
    apply Finset.sum_congr rfl; intro T' hT'; ring
  rw [hsq, ← Finset.sum_sub_distrib]
  have hdiff : ∀ T : Finset E,
      (∑ T' ∈ P, c T * c T' *
        μ.real (fmu_multiOpen T ∩
          (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T'))
      - (∑ T' ∈ P, c T * c T' * (μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T')))
      = ∑ T' ∈ P, c T * c T' *
          (μ.real (fmu_multiOpen T ∩
              (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T')
            - μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T')) := by
    intro T
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro T' hT'; ring
  simp_rw [hdiff]
  calc |∑ T ∈ P, ∑ T' ∈ P, c T * c T' *
          (μ.real (fmu_multiOpen T ∩
              (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T')
            - μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T'))|
      ≤ ∑ T ∈ P, ∑ T' ∈ P, |c T * c T' *
          (μ.real (fmu_multiOpen T ∩
              (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T')
            - μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T'))| := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum; intro T hT
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ P, ∑ T' ∈ P, |c T * c T'| * δ := by
        apply Finset.sum_le_sum; intro T hT
        apply Finset.sum_le_sum; intro T' hT'
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (le_of_lt (hg T hT T' hT')) (abs_nonneg _)
    _ = W * δ := by
        rw [hW, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro T hT
        rw [Finset.sum_mul]
    _ < ε := by
        rw [hδ]
        have hW1 : (W + 1) ≠ 0 := by positivity
        have hdpos : (0:ℝ) < ε / (W + 1) := by positivity
        calc W * (ε / (W + 1)) < (W+1) * (ε / (W+1)) :=
              mul_lt_mul_of_pos_right (by linarith) hdpos
          _ = ε := mul_div_cancel₀ ε hW1








theorem fmu_selfMixing_of_pairMixing [Countable E] (hmix : fmu_PairMixing (G := G) μ) :
    fmc_SelfMixing (G := G) μ := by
  classical
  intro A hA ε hε
  obtain ⟨P, c, hexp⟩ := fmu_cylinder_expand A hA
  have hAmeas : MeasurableSet A := MeasurableSet.of_mem_measurableCylinders hA
  exact fmu_selfMixing_one_of_pairMixing hmix hAmeas P c hexp ε hε






theorem fmu_isErgodic_of_pairMixing [Countable E]
    (hμ : IsTranslationInvariant (G := G) μ) (hmix : fmu_PairMixing (G := G) μ) :
    IsErgodic (G := G) μ :=
  fmc_isErgodic_of_selfMixing hμ (fmu_selfMixing_of_pairMixing hmix)








theorem fmu_dirac_mem (g : G) (T T' : Finset E) :
    (fun _ : E => true) ∈ fmu_multiOpen T ∩
      (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T' := by
  refine ⟨?_, ?_⟩
  · intro e he; rfl
  · intro e he; rfl


theorem fmu_pairMixing_dirac [Countable E] [MeasurableSingletonClass (ConfigSpace E)] :
    fmu_PairMixing (G := G) (Measure.dirac (fun _ : E => true)) := by
  intro P δ hδ
  refine ⟨1, ?_⟩
  intro T hT T' hT'
  
  have hmem1 : (fun _ : E => true) ∈ fmu_multiOpen T := fun e he => rfl
  have hmem2 : (fun _ : E => true) ∈ fmu_multiOpen T' := fun e he => rfl
  have hmemI : (fun _ : E => true) ∈ fmu_multiOpen T ∩
      (shift (1 : G) : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T' :=
    fmu_dirac_mem 1 T T'
  have hmeasT : MeasurableSet (fmu_multiOpen T) := fmu_multiOpen_measurable T
  have hmeasT' : MeasurableSet (fmu_multiOpen T') := fmu_multiOpen_measurable T'
  have hmeasI : MeasurableSet (fmu_multiOpen T ∩
      (shift (1 : G) : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T') :=
    hmeasT.inter (hmeasT'.preimage (measurable_shift 1))
  have e1 : (Measure.dirac (fun _ : E => true)).real (fmu_multiOpen T) = 1 := by
    rw [Measure.real, MeasureTheory.Measure.dirac_apply' _ hmeasT, Set.indicator_of_mem hmem1]; simp
  have e2 : (Measure.dirac (fun _ : E => true)).real (fmu_multiOpen T') = 1 := by
    rw [Measure.real, MeasureTheory.Measure.dirac_apply' _ hmeasT', Set.indicator_of_mem hmem2]; simp
  have eI : (Measure.dirac (fun _ : E => true)).real (fmu_multiOpen T ∩
      (shift (1 : G) : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T') = 1 := by
    rw [Measure.real, MeasureTheory.Measure.dirac_apply' _ hmeasI, Set.indicator_of_mem hmemI]; simp
  rw [e1, e2, eI]; simpa using hδ








theorem fmu_multiOpen_mem_measurableCylinders [DecidableEq E] (T : Finset E) :
    fmu_multiOpen T ∈ measurableCylinders (fun _ : E => Bool) := by
  rw [mem_measurableCylinders]
  refine ⟨T, {σ : (↥T → Bool) | ∀ e, σ e = true}, MeasurableSet.of_discrete, ?_⟩
  ext ω
  simp only [fmu_multiOpen, Set.mem_setOf_eq, mem_cylinder, Finset.restrict_def]
  exact ⟨fun h e => h e.1 e.2, fun h e he => h ⟨e, he⟩⟩



def fmu_GenMixing (μ : Measure (ConfigSpace E)) : Prop :=
  ∀ (𝒜 : Finset (Set (ConfigSpace E))),
    (∀ A ∈ 𝒜, A ∈ measurableCylinders (fun _ : E => Bool)) →
    ∀ δ : ℝ, 0 < δ →
    ∃ g : G, ∀ A ∈ 𝒜, ∀ B ∈ 𝒜,
      |μ.real (A ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' B)
        - μ.real A * μ.real B| < δ





theorem fmu_pairMixing_of_genMixing [DecidableEq E] (h : fmu_GenMixing (G := G) μ) :
    fmu_PairMixing (G := G) μ := by
  intro P δ hδ
  
  obtain ⟨g, hg⟩ := h (P.image fmu_multiOpen)
    (by intro A hA; rw [Finset.mem_image] at hA; obtain ⟨T, hT, rfl⟩ := hA
        exact fmu_multiOpen_mem_measurableCylinders T) δ hδ
  refine ⟨g, ?_⟩
  intro T hT T' hT'
  exact hg (fmu_multiOpen T) (Finset.mem_image_of_mem _ hT)
    (fmu_multiOpen T') (Finset.mem_image_of_mem _ hT')














def fmu_UpperDecay (μ : Measure (ConfigSpace E)) : Prop :=
  ∀ (P : Finset (Finset E)) (δ : ℝ), 0 < δ →
    ∃ g : G, ∀ T ∈ P, ∀ T' ∈ P,
      μ.real (fmu_multiOpen T ∩
          (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T')
        ≤ μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T') + δ




theorem fmu_pair_fkg_lower [Countable E] {μ : Measure (ConfigSpace E)} [IsProbabilityMeasure μ]
    (hμ : IsTranslationInvariant (G := G) μ)
    (hPA : ∀ {A B : Set (ConfigSpace E)}, IsIncreasing A → IsIncreasing B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (g : G) (T T' : Finset E) :
    μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T')
      ≤ μ.real (fmu_multiOpen T ∩
          (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T') := by
  have hTinc : IsIncreasing (fmu_multiOpen T) := fmu_multiOpen_isIncreasing T
  have hT'inc : IsIncreasing ((shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T') :=
    fmc_shift_isIncreasing (fmu_multiOpen_isIncreasing T') g
  have hTmeas : MeasurableSet (fmu_multiOpen T) := fmu_multiOpen_measurable T
  have hT'meas : MeasurableSet ((shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T') :=
    (fmu_multiOpen_measurable T').preimage (measurable_shift g)
  have hfkg := hPA hTinc hT'inc hTmeas hT'meas
  rwa [fmc_real_preimage_shift hμ g (fmu_multiOpen_measurable T')] at hfkg





theorem fmu_pairMixing_of_upperDecay [Countable E] {μ : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μ]
    (hμ : IsTranslationInvariant (G := G) μ)
    (hPA : ∀ {A B : Set (ConfigSpace E)}, IsIncreasing A → IsIncreasing B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (hup : fmu_UpperDecay (G := G) μ) :
    fmu_PairMixing (G := G) μ := by
  intro P δ hδ
  obtain ⟨g, hg⟩ := hup P (δ / 2) (by linarith)
  refine ⟨g, ?_⟩
  intro T hT T' hT'
  have hlow := fmu_pair_fkg_lower hμ hPA g T T'
  have hup' := hg T hT T' hT'
  
  rw [abs_of_nonneg (by linarith)]
  linarith



theorem fmu_upperDecay_dirac [Countable E] [MeasurableSingletonClass (ConfigSpace E)] :
    fmu_UpperDecay (G := G) (Measure.dirac (fun _ : E => true)) := by
  intro P δ hδ
  obtain ⟨g, hg⟩ := fmu_pairMixing_dirac (G := G) (E := E) P δ hδ
  refine ⟨g, fun T hT T' hT' => ?_⟩
  have := hg T hT T' hT'
  have h2 := (abs_lt.mp this).2
  linarith












theorem fmu_wiredIV_fkg_multiOpen {d : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (s₁ s₂ : Finset (Sym2 (Site d))) :
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s₁)
      * (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s₂)
      ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen s₁ ∩ fmu_multiOpen s₂) := by
  classical
  
  obtain ⟨N, t, ht⟩ := cdc_finset_in_box (s₁ ∪ s₂)
  set t₁ := t.filter (fun eb => edgeIncl d N eb ∈ s₁) with ht1
  set t₂ := t.filter (fun eb => edgeIncl d N eb ∈ s₂) with ht2
  have hsplit : ∀ (sᵢ : Finset (Sym2 (Site d))) (tᵢ : Finset (Sym2 (boxVerts d N))),
      tᵢ = t.filter (fun eb => edgeIncl d N eb ∈ sᵢ) →
      (sᵢ ⊆ s₁ ∪ s₂) → sᵢ = tᵢ.image (edgeIncl d N) := by
    intro sᵢ tᵢ htᵢ hsub
    ext e
    simp only [htᵢ, Finset.mem_image, Finset.mem_filter]
    constructor
    · intro he
      have : e ∈ s₁ ∪ s₂ := hsub he
      rw [ht, Finset.mem_image] at this
      obtain ⟨eb, heb, rfl⟩ := this
      exact ⟨eb, ⟨heb, he⟩, rfl⟩
    · rintro ⟨eb, ⟨_, hin⟩, rfl⟩; exact hin
  have h1 : s₁ = t₁.image (edgeIncl d N) := hsplit s₁ t₁ ht1 Finset.subset_union_left
  have h2 : s₂ = t₂.image (edgeIncl d N) := hsplit s₂ t₂ ht2 Finset.subset_union_right
  have e1 : fmu_multiOpen s₁ = boxRestrict d N ⁻¹' (cdc_boxMultiOpenEvent N t₁) := by
    rw [show fmu_multiOpen s₁ = cdc_multiOpenEvent s₁ from rfl, h1,
      cdc_multiOpenEvent_image_eq_boxRestrict]
  have e2 : fmu_multiOpen s₂ = boxRestrict d N ⁻¹' (cdc_boxMultiOpenEvent N t₂) := by
    rw [show fmu_multiOpen s₂ = cdc_multiOpenEvent s₂ from rfl, h2,
      cdc_multiOpenEvent_image_eq_boxRestrict]
  rw [e1, e2]
  exact ivp_iv_fkg_wired N hp hp1 (cdc_boxMultiOpenEvent_isIncreasing N t₁)
    (cdc_boxMultiOpenEvent_isIncreasing N t₂)




theorem fmu_wiredIV_pairMixing_of_upperDecay {d : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hup : fmu_UpperDecay (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :
    fmu_PairMixing (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) := by
  classical
  set μ := (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
    : Measure (ConfigSpace (Sym2 (Site d)))) with hμdef
  have hμ : IsTranslationInvariant (G := Multiplicative (Site d)) μ :=
    flc_wiredIV_isTranslationInvariant hp hp1
  intro P δ hδ
  obtain ⟨g, hg⟩ := hup P (δ / 2) (by linarith)
  refine ⟨g, ?_⟩
  intro T hT T' hT'
  
  have hlow : μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T')
      ≤ μ.real (fmu_multiOpen T ∩
          (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
            ⁻¹' fmu_multiOpen T') := by
    rw [fmu_shift_multiOpen g T']
    have hfkg := fmu_wiredIV_fkg_multiOpen hp hp1 T (T'.image (fun e => g⁻¹ • e))
    
    have htrans : μ.real (fmu_multiOpen (T'.image (fun e => g⁻¹ • e))) = μ.real (fmu_multiOpen T') := by
      rw [← fmu_shift_multiOpen g T']
      exact fmc_real_preimage_shift hμ g (fmu_multiOpen_measurable T')
    rw [htrans] at hfkg
    exact hfkg
  have hup' := hg T hT T' hT'
  rw [abs_of_nonneg (by linarith)]
  linarith








variable {d : ℕ}




theorem fmu_wiredIV_isErgodic_of_pairMixing {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hmix : fmu_PairMixing (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :
    IsErgodic (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  fmu_isErgodic_of_pairMixing (flc_wiredIV_isTranslationInvariant hp hp1) hmix







theorem fmu_wiredIV_isErgodic_of_upperDecay {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hup : fmu_UpperDecay (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :
    IsErgodic (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  fmu_wiredIV_isErgodic_of_pairMixing hp hp1 (fmu_wiredIV_pairMixing_of_upperDecay hp hp1 hup)



theorem fmu_freeIV_isErgodic_of_pairMixing {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hmix : fmu_PairMixing (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :
    IsErgodic (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  fmu_isErgodic_of_pairMixing (bdp_freeIV_isTranslationInvariant hp hp1) hmix

end FK

end StatMech
