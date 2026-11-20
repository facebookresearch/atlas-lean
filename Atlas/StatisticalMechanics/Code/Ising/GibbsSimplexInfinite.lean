/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































































import Mathlib
import Code.Ising.GibbsSimplex
import Code.Ising.GibbsExtreme
import Code.Ising.GibbsChoquet
import Code.Foundations.StochasticDomination

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


















theorem gsi_dlr_real_eq_integral (β h : ℝ) (μ : Measure (ConfigSpace (Site d)))
    [IsProbabilityMeasure μ]
    (hμ : IsDLRState d β h μ) (n : ℕ) {A : Set (ConfigSpace (Site d))} (hA : MeasurableSet A) :
    μ.real A = ∫ ω, (fvMeasure ω n (bondFinsetTouch d n) β h).real A ∂μ := by
  set m := outsideSigma (box d n) with hm
  set hmle := outsideSigma_le (box d n)
  set ind := A.indicator (fun _ => (1 : ℝ)) with hind
  have hindint : Integrable ind μ := by
    rw [hind]; exact (integrable_const (1 : ℝ)).indicator hA
  haveI : SigmaFinite (μ.trim hmle) := by
    haveI : IsFiniteMeasure (μ.trim hmle) := by
      refine ⟨?_⟩
      rw [trim_measurableSet_eq hmle MeasurableSet.univ]; exact measure_lt_top μ _
    infer_instance
  have hcond : ∫ ω, (μ[ind | m]) ω ∂μ = ∫ ω, ind ω ∂μ := integral_condExp hmle
  have hint_ind : ∫ ω, ind ω ∂μ = μ.real A := by rw [hind]; exact integral_indicator_one hA
  rw [hint_ind] at hcond
  
  have hker : (fun ω ↦ ((gibbsConditional μ (box d n)) ω).real A) =ᵐ[μ] μ⟦A | m⟧ :=
    gibbsConditional_ae_eq_condExp μ (box d n) hA
  
  have hdlr : (fun ω ↦ ((gibbsConditional μ (box d n)) ω).real A)
      =ᵐ[μ] (fun ω ↦ (fvMeasure ω n (bondFinsetTouch d n) β h).real A) := by
    filter_upwards [hμ n] with ω hω; rw [hω]
  have hfv : (fun ω ↦ (fvMeasure ω n (bondFinsetTouch d n) β h).real A) =ᵐ[μ] μ⟦A | m⟧ :=
    hdlr.symm.trans hker
  rw [← hcond]
  refine integral_congr_ae ?_
  rw [hind]; exact hfv.symm





theorem fvMeasure_real_integrable (β h : ℝ) (μ : Measure (ConfigSpace (Site d)))
    [IsProbabilityMeasure μ] (n : ℕ) (B : Finset (Sym2 (Site d)))
    {A : Set (ConfigSpace (Site d))} (hA : MeasurableSet A) :
    Integrable (fun ω => (fvMeasure ω n B β h).real A) μ := by
  have hmeas : Measurable (fun η : ConfigSpace (Site d) => (fvMeasure η n B β h).real A) := by
    unfold Measure.real
    exact ENNReal.measurable_toReal.comp
      ((meas_fvMeasure_coe n B β h hA).mono (outsideSigma_le (box d n)) le_rfl)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  refine HasFiniteIntegral.of_bounded (C := 1) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one
















theorem gsi_dlr_real_le_plusMeasure (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (μ : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure μ]
    (hμ : IsDLRState d β h μ) (n : ℕ) {A : Set (ConfigSpace (Site d))}
    (hA : MeasurableSet A) (hAinc : IsIncreasing A) :
    μ.real A ≤ (plusMeasure d n β h : Measure (ConfigSpace (Site d))).real A := by
  rw [gsi_dlr_real_eq_integral β h μ hμ n hA]
  have hpt : ∀ ω, (fvMeasure ω n (bondFinsetTouch d n) β h).real A
      ≤ (fvMeasure (plusField d) n (bondFinsetTouch d n) β h).real A :=
    fun ω => fvMeasure_le_plusField n (bondFinsetTouch d n) β h hβ hh ω A hA hAinc
  calc ∫ ω, (fvMeasure ω n (bondFinsetTouch d n) β h).real A ∂μ
      ≤ ∫ _ω, (fvMeasure (plusField d) n (bondFinsetTouch d n) β h).real A ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall (fun _ => measureReal_nonneg))
          (integrable_const _) (Eventually.of_forall hpt)
    _ = (plusMeasure d n β h : Measure (ConfigSpace (Site d))).real A := by
        rw [integral_const, probReal_univ, smul_eq_mul, one_mul]; rfl








theorem gsi_minusMeasure_le_dlr_real (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (μ : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure μ]
    (hμ : IsDLRState d β h μ) (n : ℕ) {A : Set (ConfigSpace (Site d))}
    (hA : MeasurableSet A) (hAinc : IsIncreasing A) :
    (minusMeasure d n β h : Measure (ConfigSpace (Site d))).real A ≤ μ.real A := by
  rw [gsi_dlr_real_eq_integral β h μ hμ n hA]
  have hpt : ∀ ω, (fvMeasure (minusField d) n (bondFinsetTouch d n) β h).real A
      ≤ (fvMeasure ω n (bondFinsetTouch d n) β h).real A :=
    fun ω => fvMeasure_minusField_le n (bondFinsetTouch d n) β h hβ hh ω A hA hAinc
  calc (minusMeasure d n β h : Measure (ConfigSpace (Site d))).real A
      = ∫ _ω, (fvMeasure (minusField d) n (bondFinsetTouch d n) β h).real A ∂μ := by
        rw [integral_const, probReal_univ, smul_eq_mul, one_mul]; rfl
    _ ≤ ∫ ω, (fvMeasure ω n (bondFinsetTouch d n) β h).real A ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall (fun _ => measureReal_nonneg))
          (fvMeasure_real_integrable β h μ n _ hA) (Eventually.of_forall hpt)


















theorem gsi_dlr_le_plusState_closed (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (μ : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure μ]
    (hμ : IsDLRState d β h μ) {A : Set (ConfigSpace (Site d))}
    (hAcl : IsClosed A) (hAinc : IsIncreasing A) :
    μ.real A ≤ (plusState d β h : Measure (ConfigSpace (Site d))).real A := by
  have hA : MeasurableSet A := hAcl.measurableSet
  obtain ⟨φ, hφ, hconv⟩ := plusState_isInfiniteVolumeState d β h
  
  have hfinE : ∀ n, μ A ≤ (plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))) A := by
    intro n
    have := gsi_dlr_real_le_plusMeasure β h hβ hh μ hμ (φ n) hA hAinc
    unfold Measure.real at this
    rwa [ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)] at this
  have hpm : (atTop.limsup fun n =>
      ((plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))) A))
        ≤ (plusState d β h : Measure (ConfigSpace (Site d))) A := by
    have := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hconv hAcl
    simpa [Function.comp] using this
  have hle1 : (μ A) ≤ atTop.limsup fun n =>
      ((plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))) A) :=
    le_limsup_of_le (by isBoundedDefault) (fun b hb => by
      obtain ⟨n, hn⟩ := hb.exists; exact (hfinE n).trans hn)
  have hle2 : μ A ≤ (plusState d β h : Measure (ConfigSpace (Site d))) A := hle1.trans hpm
  unfold Measure.real
  rw [ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
  exact hle2










theorem gsi_minusState_le_dlr_open (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (μ : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure μ]
    (hμ : IsDLRState d β h μ) {A : Set (ConfigSpace (Site d))}
    (hAop : IsOpen A) (hAinc : IsIncreasing A) :
    (minusState d β h : Measure (ConfigSpace (Site d))).real A ≤ μ.real A := by
  have hA : MeasurableSet A := hAop.measurableSet
  obtain ⟨φ, hφ, hconv⟩ := minusState_isInfiniteVolumeState d β h
  have hfinE : ∀ n, (minusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))) A ≤ μ A := by
    intro n
    have := gsi_minusMeasure_le_dlr_real β h hβ hh μ hμ (φ n) hA hAinc
    unfold Measure.real at this
    rwa [ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)] at this
  have hpm : (minusState d β h : Measure (ConfigSpace (Site d))) A ≤
      atTop.liminf fun n => ((minusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))) A) := by
    have := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hconv hAop
    simpa [Function.comp] using this
  have hle1 : (atTop.liminf fun n =>
      ((minusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))) A)) ≤ μ A :=
    liminf_le_of_le (by isBoundedDefault) (fun b hb => by
      obtain ⟨n, hn⟩ := hb.exists; exact hn.trans (hfinE n))
  have hle2 : (minusState d β h : Measure (ConfigSpace (Site d))) A ≤ μ A := hpm.trans hle1
  unfold Measure.real
  rw [ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
  exact hle2









def StochasticallyDominatedClopen {E : Type*}
    (μ ν : Measure (ConfigSpace E)) : Prop :=
  ∀ A : Set (ConfigSpace E), IsClopen A → IsUpperSet A → μ.real A ≤ ν.real A

@[inherit_doc]
scoped infix:50 " ≼c " => StochasticallyDominatedClopen


@[refl] theorem StochasticallyDominatedClopen.refl {E : Type*}
    (μ : Measure (ConfigSpace E)) : μ ≼c μ := fun _ _ _ => le_refl _


theorem StochasticallyDominatedClopen.trans {E : Type*} {μ ν ρ : Measure (ConfigSpace E)}
    (h₁ : μ ≼c ν) (h₂ : ν ≼c ρ) : μ ≼c ρ :=
  fun A hA hAu => (h₁ A hA hAu).trans (h₂ A hA hAu)



theorem StochasticallyDominated.toClopen {E : Type*} [Countable E]
    {μ ν : Measure (ConfigSpace E)} (h : μ ≼ ν) : μ ≼c ν :=
  fun A hA hAu => h A hA.2.measurableSet hAu













theorem gsi_infinite_volume_sandwich (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (μ : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure μ]
    (hμ : IsDLRState d β h μ) :
    (minusState d β h : Measure (ConfigSpace (Site d))) ≼c μ
    ∧ μ ≼c (plusState d β h : Measure (ConfigSpace (Site d))) := by
  refine ⟨fun A hAcl hAu => ?_, fun A hAcl hAu => ?_⟩
  · exact gsi_minusState_le_dlr_open β h hβ hh μ hμ hAcl.2 hAu
  · exact gsi_dlr_le_plusState_closed β h hβ hh μ hμ hAcl.1 hAu










variable {E : Type*}


def clopenUpSystem (E : Type*) : Set (Set (ConfigSpace E)) :=
  {A | IsClopen A ∧ IsUpperSet A}


theorem isPiSystem_clopenUp : IsPiSystem (clopenUpSystem E) := by
  rintro A ⟨hAc, hAu⟩ B ⟨hBc, hBu⟩ _
  exact ⟨hAc.inter hBc, hAu.inter hBu⟩



theorem upTrue_isClopen (x : E) : IsClopen {ω : ConfigSpace E | ω x = true} := by
  have hpre : {ω : ConfigSpace E | ω x = true} = (ConfigSpace.eval x) ⁻¹' {true} := by
    ext ω; simp [ConfigSpace.eval]
  rw [hpre]
  exact ⟨(isClosed_discrete _).preimage (continuous_apply x),
    (isOpen_discrete _).preimage (continuous_apply x)⟩


theorem upTrue_mem_clopen (x : E) : {ω : ConfigSpace E | ω x = true} ∈ clopenUpSystem E :=
  ⟨upTrue_isClopen x, upTrue_isUpperSet x⟩





theorem generateFrom_clopenUp [Countable E] :
    MeasurableSpace.generateFrom (clopenUpSystem E)
      = (inferInstance : MeasurableSpace (ConfigSpace E)) := by
  apply le_antisymm
  · apply generateFrom_le; rintro A ⟨hAc, _⟩; exact hAc.2.measurableSet
  · rw [ConfigSpace.measurableSpace_eq_iSup_comap]
    refine iSup_le (fun x => ?_)
    set G := MeasurableSpace.generateFrom (clopenUpSystem E) with hG
    have hT : MeasurableSet[G] {ω : ConfigSpace E | ω x = true} :=
      measurableSet_generateFrom (upTrue_mem_clopen x)
    have hTc : MeasurableSet[G] {ω : ConfigSpace E | ω x = true}ᶜ := hT.compl
    have hEmpty : MeasurableSet[G] (∅ : Set (ConfigSpace E)) := @MeasurableSet.empty _ G
    intro s hs
    obtain ⟨t, _, rfl⟩ := hs
    classical
    have key : (ConfigSpace.eval x) ⁻¹' t
        = (if true ∈ t then {ω : ConfigSpace E | ω x = true} else ∅)
          ∪ (if false ∈ t then {ω : ConfigSpace E | ω x = true}ᶜ else ∅) := by
      ext ω
      simp only [Set.mem_preimage, ConfigSpace.eval_apply, Set.mem_union]
      cases hw : ω x <;> simp [hw]
    change MeasurableSet[G] _
    rw [key]
    refine (?_ : MeasurableSet[G] _).union (?_ : MeasurableSet[G] _)
    · split <;> [exact hT; exact hEmpty]
    · split <;> [exact hTc; exact hEmpty]










theorem gsi_clopen_antisymm [Countable E] {μ ν : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h₁ : μ ≼c ν) (h₂ : ν ≼c μ) : μ = ν := by
  refine ext_of_generate_finite (clopenUpSystem E)
    generateFrom_clopenUp.symm isPiSystem_clopenUp ?_ ?_
  · rintro A ⟨hAc, hAu⟩
    have hre : μ.real A = ν.real A := le_antisymm (h₁ A hAc hAu) (h₂ A hAc hAu)
    unfold Measure.real at hre
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ A) (measure_ne_top ν A)).mp hre
  · rw [measure_univ, measure_univ]










theorem gsi_gibbs_unique_of_phases_eq (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (μ : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure μ]
    (hμ : IsDLRState d β h μ)
    (hphase : (plusState d β h : Measure (ConfigSpace (Site d)))
      = (minusState d β h : Measure (ConfigSpace (Site d)))) :
    μ = (minusState d β h : Measure (ConfigSpace (Site d))) := by
  obtain ⟨hlow, hhigh⟩ := gsi_infinite_volume_sandwich β h hβ hh μ hμ
  have hhigh' : μ ≼c (minusState d β h : Measure (ConfigSpace (Site d))) := by
    rw [← hphase]; exact hhigh
  exact gsi_clopen_antisymm hhigh' hlow

end Ising

end StatMech
