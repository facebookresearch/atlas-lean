/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































































import Code.Ising.PlusStateTIClose
import Code.Ising.IsingPlusErgodicClose
import Code.Ising.FVConsistencyProve

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace
open StatMech.FK

variable {d : ℕ}













theorem iti_glue_plusField_le {n : ℕ} (σ : {x // x ∈ box d n} → Bool) :
    glue (plusField d) σ ≤ plusField d := by
  intro x; simp only [plusField]; cases (glue (plusField d) σ x) <;> simp

set_option maxHeartbeats 1600000 in











theorem iti_crossbox_dom (n m : ℕ) (hnm : n ≤ m) {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    {A : Set (ConfigSpace (Site d))} (hAmeas : MeasurableSet A) (hAinc : IsIncreasing A) :
    (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real A
      ≤ (plusMeasure d n β h : Measure (ConfigSpace (Site d))).real A := by
  have hLHSm : (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real A
      = ∑ σ : {x // x ∈ box d m} → Bool,
          fvProb (plusField d) m (bondFinsetTouch d m) β h σ
            * Set.indicator A (fun _ => (1:ℝ)) (glue (plusField d) σ) := by
    rw [plusMeasure_coe]; exact fvMeasure_real_eq (plusField d) m (bondFinsetTouch d m) β h hAmeas
  have hcons := consistency_double_sum hnm (plusField d) β h (Set.indicator A (fun _ => (1:ℝ)))
  rw [hLHSm, ← hcons]
  
  have hbound : ∀ σ : {x // x ∈ box d m} → Bool,
      (∑ τ : {x // x ∈ box d n} → Bool,
          fvProb (glue (plusField d) σ) n (bondFinsetTouch d n) β h τ
            * Set.indicator A (fun _ => (1:ℝ)) (glue (glue (plusField d) σ) τ))
        ≤ (plusMeasure d n β h : Measure (ConfigSpace (Site d))).real A := by
    intro σ
    have hd1 : (∑ τ : {x // x ∈ box d n} → Bool,
          fvProb (glue (plusField d) σ) n (bondFinsetTouch d n) β h τ
            * Set.indicator A (fun _ => (1:ℝ)) (glue (glue (plusField d) σ) τ))
        = (fvMeasure (glue (plusField d) σ) n (bondFinsetTouch d n) β h).real A :=
      (fvMeasure_real_eq (glue (plusField d) σ) n (bondFinsetTouch d n) β h hAmeas).symm
    have hdom : (fvMeasure (glue (plusField d) σ) n (bondFinsetTouch d n) β h).real A
        ≤ (fvMeasure (plusField d) n (bondFinsetTouch d n) β h).real A :=
      fvMeasure_dominated n (bondFinsetTouch d n) β h hβ hh
        (glue (plusField d) σ) (plusField d) (iti_glue_plusField_le σ) A hAmeas hAinc
    rw [hd1, plusMeasure_coe]; exact hdom
  calc ∑ σ : {x // x ∈ box d m} → Bool,
          fvProb (plusField d) m (bondFinsetTouch d m) β h σ
            * (∑ τ : {x // x ∈ box d n} → Bool,
                fvProb (glue (plusField d) σ) n (bondFinsetTouch d n) β h τ
                  * Set.indicator A (fun _ => (1:ℝ)) (glue (glue (plusField d) σ) τ))
      ≤ ∑ σ : {x // x ∈ box d m} → Bool,
          fvProb (plusField d) m (bondFinsetTouch d m) β h σ
            * ((plusMeasure d n β h : Measure (ConfigSpace (Site d))).real A) := by
        apply Finset.sum_le_sum
        intro σ _
        exact mul_le_mul_of_nonneg_left (hbound σ) (fvProb_nonneg _ _ _ _ _ _)
    _ = (plusMeasure d n β h : Measure (ConfigSpace (Site d))).real A := by
        rw [← Finset.sum_mul,
          fvProb_sum_eq_one (plusField d) m (bondFinsetTouch d m) β h, one_mul]






theorem iti_plus_multiOpen_antitone {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    (T : Finset (Site d)) {n m : ℕ} (hnm : n ≤ m) :
    (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (E := Site d) T)
      ≤ (plusMeasure d n β h : Measure (ConfigSpace (Site d))).real
          (fmu_multiOpen (E := Site d) T) :=
  iti_crossbox_dom n m hnm hβ hh
    (IsClopen.measurableSet_configSpace (ipe_multiOpen_isClopen T))
    (fmu_multiOpen_isIncreasing T)








noncomputable def iti_monomialCM (T : Finset (Site d)) : C(ConfigSpace (Site d), ℝ) :=
  ∏ x ∈ T, pstc_coordCM x



theorem iti_prod_coordCM_eq_indicator (T : Finset (Site d)) (ω : ConfigSpace (Site d)) :
    (∏ x ∈ T, pstc_coordCM x ω)
      = (fmu_multiOpen (E := Site d) T).indicator (fun _ => (1:ℝ)) ω := by
  simp only [pstc_coordCM_apply]
  by_cases h : ω ∈ fmu_multiOpen (E := Site d) T
  · rw [Set.indicator_of_mem h]; exact Finset.prod_eq_one fun x hx => by rw [if_pos (h x hx)]
  · rw [Set.indicator_of_notMem h]
    simp only [fmu_multiOpen, Set.mem_setOf_eq, not_forall] at h
    obtain ⟨x, hx, hxx⟩ := h
    exact Finset.prod_eq_zero hx (by rw [if_neg (by simpa using hxx)])

@[simp] theorem iti_monomialCM_apply (T : Finset (Site d)) (ω : ConfigSpace (Site d)) :
    iti_monomialCM T ω = (fmu_multiOpen (E := Site d) T).indicator (fun _ => (1:ℝ)) ω := by
  rw [iti_monomialCM, ContinuousMap.prod_apply]; exact iti_prod_coordCM_eq_indicator T ω


theorem iti_monomialCM_empty : iti_monomialCM (∅ : Finset (Site d)) = 1 := by
  rw [iti_monomialCM, Finset.prod_empty]


theorem iti_monomialCM_singleton (x : Site d) :
    iti_monomialCM ({x} : Finset (Site d)) = pstc_coordCM x := by
  rw [iti_monomialCM, Finset.prod_singleton]



theorem iti_monomialCM_mul (T₁ T₂ : Finset (Site d)) :
    iti_monomialCM T₁ * iti_monomialCM T₂ = iti_monomialCM (T₁ ∪ T₂) := by
  apply ContinuousMap.ext; intro ω
  simp only [ContinuousMap.mul_apply, iti_monomialCM_apply]
  have hinter : fmu_multiOpen (E := Site d) (T₁ ∪ T₂)
      = fmu_multiOpen (E := Site d) T₁ ∩ fmu_multiOpen (E := Site d) T₂ := by
    ext ω'; simp only [fmu_multiOpen, Set.mem_setOf_eq, Set.mem_inter_iff, Finset.mem_union]
    constructor
    · intro hh; exact ⟨fun e he => hh e (Or.inl he), fun e he => hh e (Or.inr he)⟩
    · rintro ⟨h1, h2⟩ e (he | he)
      · exact h1 e he
      · exact h2 e he
  rw [hinter]
  have := Set.inter_indicator_mul (s := fmu_multiOpen (E := Site d) T₁)
    (t := fmu_multiOpen (E := Site d) T₂) (fun _ => (1:ℝ)) (fun _ => (1:ℝ)) ω
  simp only [mul_one] at this
  rw [this]




theorem iti_closure_isMonomial {hh : C(ConfigSpace (Site d), ℝ)}
    (hmem : hh ∈ Submonoid.closure (Set.range (pstc_coordCM (d := d)))) :
    ∃ T : Finset (Site d), hh = iti_monomialCM T := by
  induction hmem using Submonoid.closure_induction with
  | mem x hx => obtain ⟨e, rfl⟩ := hx; exact ⟨{e}, (iti_monomialCM_singleton e).symm⟩
  | one => exact ⟨∅, (iti_monomialCM_empty).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨T₁, rfl⟩ := hx; obtain ⟨T₂, rfl⟩ := hy
    exact ⟨T₁ ∪ T₂, iti_monomialCM_mul T₁ T₂⟩




noncomputable def iti_monomialBcf (T : Finset (Site d)) : ConfigSpace (Site d) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact (iti_monomialCM T)



theorem iti_integral_monomialBcf (T : Finset (Site d)) (μ : Measure (ConfigSpace (Site d)))
    [IsFiniteMeasure μ] :
    (∫ ω, iti_monomialBcf T ω ∂μ) = μ.real (fmu_multiOpen (E := Site d) T) := by
  have heq : (fun ω => iti_monomialBcf T ω)
      = Set.indicator (fmu_multiOpen (E := Site d) T) (fun _ => (1 : ℝ)) := by
    funext ω
    simp only [iti_monomialBcf, BoundedContinuousFunction.mkOfCompact_apply, iti_monomialCM,
      ContinuousMap.prod_apply]
    exact iti_prod_coordCM_eq_indicator T ω
  rw [heq, MeasureTheory.integral_indicator_const (1 : ℝ)
    (ipe_multiOpen_isClopen T).isClosed.measurableSet]
  simp [Measure.real]




theorem iti_monomialBcf_comp_shift (T : Finset (Site d)) (g : Multiplicative (Site d))
    (ω : ConfigSpace (Site d)) :
    iti_monomialBcf T (shift g ω) = iti_monomialBcf (T.image (fun x => g⁻¹ • x)) ω := by
  simp only [iti_monomialBcf, BoundedContinuousFunction.mkOfCompact_apply, iti_monomialCM,
    ContinuousMap.prod_apply]
  rw [iti_prod_coordCM_eq_indicator, iti_prod_coordCM_eq_indicator]
  rw [show (fmu_multiOpen (E := Site d) T).indicator (fun _ => (1:ℝ)) (shift g ω)
      = ((shift g) ⁻¹' (fmu_multiOpen (E := Site d) T)).indicator (fun _ => (1:ℝ)) ω from by
    by_cases hm : shift g ω ∈ fmu_multiOpen (E := Site d) T
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show ω ∈ _ from hm)]
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (show ω ∉ _ from hm)]]
  rw [fmu_shift_multiOpen g T]





theorem iti_decayFun_monomial (μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (g : Multiplicative (Site d)) (T : Finset (Site d)) (n : ℕ) :
    pstc_decayFun μ g (iti_monomialBcf T) n
      = ((μ n : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (E := Site d) T))
        - ((μ n : Measure (ConfigSpace (Site d))).real
            (fmu_multiOpen (E := Site d) (T.image (fun x => g⁻¹ • x)))) := by
  unfold pstc_decayFun
  rw [iti_integral_monomialBcf T]
  congr 1
  rw [show (fun ω => iti_monomialBcf T (shift g ω))
      = (fun ω => iti_monomialBcf (T.image (fun x => g⁻¹ • x)) ω) from
        funext (fun ω => iti_monomialBcf_comp_shift T g ω)]
  rw [iti_integral_monomialBcf (T.image (fun x => g⁻¹ • x))]








theorem iti_plus_multiOpen_tendsto (β h : ℝ) (φ : ℕ → ℕ) (T : Finset (Site d))
    (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h)) :
    Tendsto (fun n => (plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) T)) atTop
      (𝓝 ((plusState d β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) T))) :=
  StatMech.WeakConvergesTo.tendsto_real_of_isClopen hconv (ipe_multiOpen_isClopen T)













def iti_PlusMultiHomogeneous (β h : ℝ) (g : Multiplicative (Site d)) : Prop :=
  ∀ T : Finset (Site d),
    (plusState d β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (E := Site d) T)
      = (plusState d β h : Measure (ConfigSpace (Site d))).real
          (fmu_multiOpen (E := Site d) (T.image (fun x => g⁻¹ • x)))




theorem iti_plusMultiHomogeneous_one (β h : ℝ) :
    iti_PlusMultiHomogeneous β h (1 : Multiplicative (Site d)) := by
  intro T
  have hTeq : T.image (fun x => (1 : Multiplicative (Site d))⁻¹ • x) = T := by
    rw [Finset.image_congr (g := id) (fun x _ => by simp), Finset.image_id]
  rw [hTeq]








theorem iti_decayFun_monomial_tendsto_zero (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h))
    (hhom : iti_PlusMultiHomogeneous β h g) (T : Finset (Site d)) :
    Tendsto (pstc_decayFun (fun n => plusMeasure d (φ n) β h) g (iti_monomialBcf T))
      atTop (𝓝 0) := by
  have hdecay : pstc_decayFun (fun n => plusMeasure d (φ n) β h) g (iti_monomialBcf T)
      = fun n =>
        ((plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real
            (fmu_multiOpen (E := Site d) T))
          - ((plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real
              (fmu_multiOpen (E := Site d) (T.image (fun x => g⁻¹ • x)))) := by
    funext n; exact iti_decayFun_monomial _ g T n
  rw [hdecay]
  have h1 := iti_plus_multiOpen_tendsto β h φ T hconv
  have h2 := iti_plus_multiOpen_tendsto β h φ (T.image (fun x => g⁻¹ • x)) hconv
  have hsub := h1.sub h2
  rw [← hhom T, sub_self] at hsub
  exact hsub




theorem iti_decayFun_add (μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (g : Multiplicative (Site d)) (f f' : ConfigSpace (Site d) →ᵇ ℝ) (n : ℕ) :
    pstc_decayFun μ g (f + f') n = pstc_decayFun μ g f n + pstc_decayFun μ g f' n := by
  simp only [pstc_decayFun, BoundedContinuousFunction.coe_add, Pi.add_apply]
  have h1 : (∫ x, (f x + f' x) ∂(μ n : Measure _))
      = (∫ x, f x ∂(μ n : Measure _)) + ∫ x, f' x ∂(μ n : Measure _) :=
    integral_add (f.integrable _) (f'.integrable _)
  have h2 : (∫ x, (f (shift g x) + f' (shift g x)) ∂(μ n : Measure _))
      = (∫ x, f (shift g x) ∂(μ n : Measure _)) + ∫ x, f' (shift g x) ∂(μ n : Measure _) :=
    integral_add ((f.compContinuous ⟨shift g, continuous_shift g⟩).integrable _)
      ((f'.compContinuous ⟨shift g, continuous_shift g⟩).integrable _)
  rw [h1, h2]; ring


theorem iti_decayFun_smul (μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (g : Multiplicative (Site d)) (c : ℝ) (f : ConfigSpace (Site d) →ᵇ ℝ) (n : ℕ) :
    pstc_decayFun μ g (c • f) n = c * pstc_decayFun μ g f n := by
  simp only [pstc_decayFun, BoundedContinuousFunction.coe_smul, smul_eq_mul]
  rw [integral_const_mul, integral_const_mul]; ring


theorem iti_decayFun_zero (μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (g : Multiplicative (Site d)) (n : ℕ) :
    pstc_decayFun μ g (0 : ConfigSpace (Site d) →ᵇ ℝ) n = 0 := by
  simp only [pstc_decayFun, BoundedContinuousFunction.coe_zero, Pi.zero_apply, integral_zero,
    sub_zero]





noncomputable def iti_decaySet (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ) :
    Submodule ℝ C(ConfigSpace (Site d), ℝ) where
  carrier := {hh | Tendsto (pstc_decayFun (fun n => plusMeasure d (φ n) β h) g
      (BoundedContinuousFunction.mkOfCompact hh)) atTop (𝓝 0)}
  add_mem' {hh hh'} h1 h2 := by
    simp only [Set.mem_setOf_eq] at h1 h2 ⊢
    have hsum := h1.add h2; rw [add_zero] at hsum
    refine hsum.congr (fun n => ?_)
    rw [BoundedContinuousFunction.mkOfCompact_add, iti_decayFun_add]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    have hz : pstc_decayFun (fun n => plusMeasure d (φ n) β h) g
        (BoundedContinuousFunction.mkOfCompact (0 : C(ConfigSpace (Site d), ℝ)))
      = fun _ => (0:ℝ) := by
      funext n; rw [BoundedContinuousFunction.mkOfCompact_zero, iti_decayFun_zero]
    rw [hz]; exact tendsto_const_nhds
  smul_mem' c hh h1 := by
    simp only [Set.mem_setOf_eq] at h1 ⊢
    have hsmul := h1.const_mul c; rw [mul_zero] at hsmul
    refine hsmul.congr (fun n => ?_)
    have hms : BoundedContinuousFunction.mkOfCompact (c • hh)
        = c • BoundedContinuousFunction.mkOfCompact hh := rfl
    rw [hms, iti_decayFun_smul]









theorem iti_cylinderAlg_le_decaySet (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h))
    (hhom : iti_PlusMultiHomogeneous β h g) :
    Subalgebra.toSubmodule (pstc_cylinderAlg d) ≤ iti_decaySet β h g φ := by
  unfold pstc_cylinderAlg
  rw [Algebra.adjoin_eq_span, Submodule.span_le]
  intro hh hmem
  obtain ⟨T, rfl⟩ := iti_closure_isMonomial hmem
  change Tendsto (pstc_decayFun (fun n => plusMeasure d (φ n) β h) g
      (BoundedContinuousFunction.mkOfCompact (iti_monomialCM T))) atTop (𝓝 0)
  exact iti_decayFun_monomial_tendsto_zero β h g φ hconv hhom T






theorem iti_plusCylinderDecay_of_homogeneous (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h))
    (hhom : iti_PlusMultiHomogeneous β h g) :
    pstc_PlusCylinderDecay β h g φ := by
  intro f hf
  obtain ⟨hh, hhmem, rfl⟩ := hf
  exact iti_cylinderAlg_le_decaySet β h g φ hconv hhom hhmem











theorem iti_plusState_isTranslationInvariant_of_homogeneous (β h : ℝ)
    (hhom : ∀ g : Multiplicative (Site d), iti_PlusMultiHomogeneous β h g) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  pstc_plusState_isTranslationInvariant_of_cylinderDecay β h
    (fun g φ _ hconv => iti_plusCylinderDecay_of_homogeneous β h g φ hconv (hhom g))







theorem iti_plusState_isErgodic_of_homogeneous_upperDecay {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    (hhom : ∀ g : Multiplicative (Site d), iti_PlusMultiHomogeneous β h g)
    (hup : fmu_UpperDecay (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d)))) :
    IsErgodic (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  ipe_plusState_isErgodic_of_upperDecay hβ h
    (iti_plusState_isTranslationInvariant_of_homogeneous β h hhom) hup




theorem iti_plusState_isInvariantExtremePoint_of_homogeneous_upperDecay {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    (hhom : ∀ g : Multiplicative (Site d), iti_PlusMultiHomogeneous β h g)
    (hup : fmu_UpperDecay (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d)))) :
    StatMech.FK.IsInvariantExtremePoint (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  ipe_plusState_isInvariantExtremePoint_of_upperDecay hβ h
    (iti_plusState_isTranslationInvariant_of_homogeneous β h hhom) hup

end Ising

end StatMech
