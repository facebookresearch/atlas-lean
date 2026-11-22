/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RegularConditionalDistribution
import Mathlib.Tactic.NormNum

/-!
# Tests for regular conditional distributions

Signature restatements of the three public theorems in
`MathlibExt.Probability.RegularConditionalDistribution`, a hand-built
Dirac family for a constant random variable, and a concrete computation:
conditioning a `Bool`-valued random variable on itself gives the Dirac
measure at positive-mass observed values. The additional tests cover
arbitrary sub-sigma-algebras and null-state measurability and range defects;
the Dirac family remains valid without positive singleton masses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExtTest.Probability.RegularConditionalDistribution

variable {α β Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [MeasurableSpace Ω] {μ : Measure α}

/-- The kernel-form packaging restates with the exact public signature. -/
example [StandardBorelSpace Ω] [Nonempty Ω] [IsFiniteMeasure μ]
    {X : α → β} {Y : α → Ω} (hX : Measurable X) (hY : Measurable Y) :
    IsRegularConditionalDistribution (condDistrib Y X μ) Y X μ :=
  condDistrib_isRegularConditionalDistribution hX hY

/-- The kernel-form existence theorem restates with the exact public signature. -/
example [StandardBorelSpace Ω] [Nonempty Ω] [IsFiniteMeasure μ]
    {X : α → β} {Y : α → Ω} (hX : Measurable X) (hY : Measurable Y) :
    ∃ κ : Kernel β Ω, IsRegularConditionalDistribution κ Y X μ :=
  exists_regularConditionalDistribution hX hY

/-- The family-form existence theorem restates with the exact public signature. -/
example [StandardBorelSpace Ω] [Nonempty Ω] [IsFiniteMeasure μ]
    {X : α → β} {Y : α → Ω} (hX : Measurable X) (hY : Measurable Y) :
    ∃ rcd : α → Measure Ω,
      RegularConditionalDistribution rcd Y (mβ.comap X) μ :=
  exists_regularConditionalDistribution_family hX hY

section ConstantRandomVariable

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : @Measure Ω mΩ} [IsProbabilityMeasure P]
  {S : Type*} [MeasurableSpace S] {c : S} {𝒢 : MeasurableSpace Ω}

/-- The Dirac family at `c` is a regular conditional distribution for the
constant random variable `ω ↦ c` given any sub-σ-algebra `𝒢`: the
conditional probability of `A` is `1` if `c ∈ A` and `0` otherwise. -/
theorem regularConditionalDistribution_dirac_const (h𝒢 : 𝒢 ≤ mΩ) :
    RegularConditionalDistribution (fun _ : Ω => Measure.dirac c) (fun _ => c) 𝒢 P where
  conditioning_le := h𝒢
  measurable_target := measurable_const
  measurable_eval := fun _ => measurable_const
  mass_le_one := fun _ => prob_le_one
  ae_eq_condexp := by
    intro A hA
    by_cases hc : c ∈ A
    · have hpre : (fun _ : Ω => c) ⁻¹' A = Set.univ := Set.preimage_const_of_mem hc
      have hcond : P⟦(fun _ : Ω => c) ⁻¹' A | 𝒢⟧ = fun _ => (1 : ℝ) := by
        rw [hpre, Set.indicator_univ]
        exact condExp_const (μ := P) h𝒢 (1 : ℝ)
      rw [hcond]
      exact Filter.Eventually.of_forall fun _ => by
        simp [Measure.dirac_apply_of_mem hc]
    · have hpre : (fun _ : Ω => c) ⁻¹' A = ∅ := Set.preimage_const_of_notMem hc
      have hcond : P⟦(fun _ : Ω => c) ⁻¹' A | 𝒢⟧ = 0 := by
        rw [hpre, Set.indicator_empty]
        exact condExp_zero
      rw [hcond]
      exact Filter.Eventually.of_forall fun _ => by
        have h0 : Measure.dirac c A = 0 := by
          rw [Measure.dirac_apply' _ hA, Set.indicator_of_notMem hc]
        simp [h0]
  ae_isProbabilityMeasure := Filter.Eventually.of_forall fun _ => inferInstance

end ConstantRandomVariable

section BoolSelfConditioning

variable {μ : Measure Bool} [IsFiniteMeasure μ]

/-- Conditioning a `Bool`-valued random variable on itself gives the Dirac
measure at the observed value when the singleton masses are nonzero. -/
theorem condDistrib_id_id_bool (hμ : ∀ b : Bool, μ {b} ≠ 0) (b : Bool) :
    condDistrib id id μ b = Measure.dirac b := by
  classical
  apply Measure.ext
  intro s hs
  have hjoint : μ.map (fun a : Bool => (id a, id a)) ({b} ×ˢ s) =
      if b ∈ s then μ {b} else 0 := by
    rw [Measure.map_apply (by fun_prop) ((measurableSet_singleton b).prod hs)]
    have hpre : (fun a : Bool => (id a, id a)) ⁻¹' ({b} ×ˢ s) = {b} ∩ s := by
      ext a
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff,
        Set.mem_singleton_iff, id_eq]
    rw [hpre]
    by_cases hb : b ∈ s
    · rw [Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hb)]
      simp only [hb, ite_true]
    · have hempty : ({b} : Set Bool) ∩ s = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro a ⟨rfl, ha⟩
        exact hb ha
      rw [hempty]
      simp only [hb, ite_false, measure_empty]
  rw [condDistrib_apply_of_ne_zero measurable_id measurable_id b
    (by rw [Measure.map_id]; exact hμ b) s, Measure.map_id]
  rw [hjoint]
  by_cases hb : b ∈ s
  · simp only [hb, ite_true]
    rw [ENNReal.inv_mul_cancel (hμ b) (measure_ne_top μ _),
      Measure.dirac_apply_of_mem hb]
  · simp only [hb, ite_false]
    rw [mul_zero]
    rw [show Measure.dirac b s = 0 from by
      rw [Measure.dirac_apply' _ hs, Set.indicator_of_notMem hb]]

/-- The Dirac family is a regular conditional distribution for the identity
random variable on `Bool` given `σ(id)`. -/
theorem regularConditionalDistribution_bool_self (hμ : ∀ b : Bool, μ {b} ≠ 0) :
    RegularConditionalDistribution (fun b : Bool => Measure.dirac b) id
      (MeasurableSpace.comap id inferInstance) μ where
  conditioning_le := measurable_id.comap_le
  measurable_target := measurable_id
  measurable_eval := fun hA => by
    rw [MeasurableSpace.comap_id]
    simpa only [Kernel.id_apply] using
      (Kernel.measurable_coe (Kernel.id : Kernel Bool Bool) hA)
  mass_le_one := fun _ => prob_le_one
  ae_eq_condexp := by
    intro A hA
    have hfun : (fun ω : Bool => ((Measure.dirac ω) A).toReal) =
        fun ω => (condDistrib id id μ (id ω)).real A := by
      funext ω
      simp only [condDistrib_id_id_bool hμ, id_eq, measureReal_def]
    rw [hfun]
    exact condDistrib_ae_eq_condExp measurable_id measurable_id hA
  ae_isProbabilityMeasure := Filter.Eventually.of_forall fun _ => inferInstance

end BoolSelfConditioning


section GeneralSubsigma

/-- The general family API has no conditioning random variable or countability
premise on the sub-sigma-algebra. -/
example [StandardBorelSpace Ω] [Nonempty Ω] [IsFiniteMeasure μ]
    {𝒢 : MeasurableSpace α} {Y : α → Ω} (h𝒢 : 𝒢 ≤ mα)
    (hY : @Measurable α Ω mα ‹MeasurableSpace Ω› Y) :
    ∃ rcd : α → Measure Ω, RegularConditionalDistribution rcd Y 𝒢 μ :=
  exists_regularConditionalDistribution_family_of_le h𝒢 hY

/-- An ambient-measurable target that is not conditioning-measurable still
has a family distribution. This detects a shadowed conditioning-space instance. -/
theorem general_subsigma_bool_nonmeasurable_target :
    (¬ Measurable[⊥] (id : Bool → Bool)) ∧
    ∃ rcd : Bool → Measure Bool,
      RegularConditionalDistribution rcd id ⊥ (Measure.dirac true) := by
  refine ⟨?_, exists_regularConditionalDistribution_family_of_le bot_le measurable_id⟩
  intro h
  obtain ⟨c, hc⟩ := eq_const_of_measurable_bot h
  have heq := (congrFun hc false).trans (congrFun hc true).symm
  simpa using heq

end GeneralSubsigma

section NullStates

private theorem ae_at_true {p : Bool → Prop} (h : p true) :
    ∀ᵐ b ∂(Measure.dirac true : Measure Bool), p b :=
  (ae_dirac_iff (Set.to_countable {b | p b}).measurableSet).mpr h

/-- The two original family fields accept a non-bottom-measurable evaluation
at the null state `false`. -/
theorem null_state_measurability_old_fields :
    (∀ {A : Set Bool}, MeasurableSet A →
      (fun b => (Measure.dirac b A).toReal) =ᵐ[Measure.dirac true]
        (Measure.dirac true)⟦(fun _ : Bool => true) ⁻¹' A | ⊥⟧) ∧
    (∀ᵐ b ∂(Measure.dirac true : Measure Bool), IsProbabilityMeasure (Measure.dirac b)) := by
  constructor
  · intro A hA
    have heq : (fun b : Bool => (Measure.dirac b A).toReal) =ᵐ[Measure.dirac true]
        fun _ => (Measure.dirac true A).toReal := ae_at_true rfl
    exact heq.trans ((regularConditionalDistribution_dirac_const
      (P := Measure.dirac true) (c := true) (𝒢 := ⊥) bot_le).ae_eq_condexp hA)
  · exact Filter.Eventually.of_forall fun _ => inferInstance

/-- Conditioning measurability rejects the family accepted by the old fields. -/
theorem null_state_measurability_rejected :
    ¬ RegularConditionalDistribution (fun b : Bool => Measure.dirac b)
      (fun _ => true) ⊥ (Measure.dirac true) := by
  intro h
  obtain ⟨c, hc⟩ := eq_const_of_measurable_bot
    (h.measurable_eval (measurableSet_singleton true))
  have heq := (congrFun hc false).trans (congrFun hc true).symm
  simpa [Measure.dirac_apply' _ (measurableSet_singleton true)] using heq

noncomputable def nullStateMassFamily (b : Bool) : Measure Bool :=
  if b then Measure.dirac true else (2 : ENNReal) • Measure.dirac true

/-- The old fields also accept mass two at a null state. All evaluations in
this example are measurable for the conditioning sigma-algebra `⊤`. -/
theorem null_state_mass_old_fields :
    (∀ {A : Set Bool}, MeasurableSet A →
      (fun b => (nullStateMassFamily b A).toReal) =ᵐ[Measure.dirac true]
        (Measure.dirac true)⟦(fun _ : Bool => true) ⁻¹' A | ⊤⟧) ∧
    (∀ᵐ b ∂(Measure.dirac true : Measure Bool),
      IsProbabilityMeasure (nullStateMassFamily b)) ∧
    (∀ {A : Set Bool}, MeasurableSet A →
      Measurable[⊤] fun b => nullStateMassFamily b A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    have heq : (fun b => (nullStateMassFamily b A).toReal) =ᵐ[Measure.dirac true]
        fun _ => (Measure.dirac true A).toReal :=
      ae_at_true (by simp [nullStateMassFamily])
    have htop : (⊤ : MeasurableSpace Bool) ≤ (inferInstance : MeasurableSpace Bool) := by
      intro s _
      exact (Set.to_countable s).measurableSet
    exact heq.trans ((regularConditionalDistribution_dirac_const
      (P := Measure.dirac true) (c := true) (𝒢 := ⊤) htop).ae_eq_condexp hA)
  · exact ae_at_true (by
      simpa [nullStateMassFamily] using
        (inferInstance : IsProbabilityMeasure (Measure.dirac true : Measure Bool)))
  · intro A _
    exact Measurable.of_comap_le le_top

/-- The pointwise `[0,1]` range rejects the independent mass-bound defect. -/
theorem null_state_mass_rejected :
    ¬ RegularConditionalDistribution nullStateMassFamily
      (fun _ : Bool => true) ⊤ (Measure.dirac true) := by
  intro h
  have hmass := h.mass_le_one false
  norm_num [nullStateMassFamily, Measure.smul_apply] at hmass

/-- Self-conditioning has a Dirac family for every finite measure, including
zero singleton masses. The kernel identity used here is almost everywhere. -/
theorem regularConditionalDistribution_bool_self_ae {μ : Measure Bool} [IsFiniteMeasure μ] :
    RegularConditionalDistribution (fun b : Bool => Measure.dirac b) id
      (MeasurableSpace.comap id inferInstance) μ where
  conditioning_le := measurable_id.comap_le
  measurable_target := measurable_id
  measurable_eval := fun hA => by
    rw [MeasurableSpace.comap_id]
    simpa only [Kernel.id_apply] using
      (Kernel.measurable_coe (Kernel.id : Kernel Bool Bool) hA)
  mass_le_one := fun _ => prob_le_one
  ae_eq_condexp := by
    intro A hA
    have hid : condDistrib id id μ =ᵐ[μ] (Kernel.id : Kernel Bool Bool) := by
      simpa only [Measure.map_id] using
        (condDistrib_self (μ := μ) (Y := id) aemeasurable_id)
    filter_upwards [hid, condDistrib_ae_eq_condExp measurable_id measurable_id hA] with b hb hcond
    simpa only [id_eq, hb, Kernel.id_apply, measureReal_def] using hcond
  ae_isProbabilityMeasure := Filter.Eventually.of_forall fun _ => inferInstance

/-- The null atom is explicit in the concrete self-conditioning client. -/
example : (Measure.dirac true : Measure Bool) {false} = 0 ∧
    RegularConditionalDistribution (fun b : Bool => Measure.dirac b) id
      (MeasurableSpace.comap id inferInstance) (Measure.dirac true) := by
  refine ⟨by simp, regularConditionalDistribution_bool_self_ae⟩

/-- The finite-measure extension includes the zero measure. -/
example : RegularConditionalDistribution (fun b : Bool => Measure.dirac b) id
    (MeasurableSpace.comap id inferInstance) (0 : Measure Bool) :=
  regularConditionalDistribution_bool_self_ae

end NullStates


section RawSourceRefinement

/-- At the null state `false`, this raw source family assigns one even to
the empty set. At `true`, it agrees with the Dirac probability measure. -/
noncomputable def rawNullStateFamily (b : Bool) (A : Set Bool) : ℝ :=
  if b then (Measure.dirac true A).toReal else 1

/-- The raw family satisfies all Lecture 26 source clauses, with the sole
exceptional sample point `false` having zero probability. -/
theorem rawNullStateFamily_source_clauses :
    (∀ b A, 0 ≤ rawNullStateFamily b A ∧ rawNullStateFamily b A ≤ 1) ∧
    (∀ {A : Set Bool}, MeasurableSet A →
      Measurable[⊤] fun b => rawNullStateFamily b A) ∧
    (∀ {A : Set Bool}, MeasurableSet A →
      (fun b => rawNullStateFamily b A) =ᵐ[Measure.dirac true]
        (Measure.dirac true)⟦(fun _ : Bool => true) ⁻¹' A | ⊤⟧) ∧
    (∀ᵐ b ∂(Measure.dirac true : Measure Bool), ∃ ν : Measure Bool,
      IsProbabilityMeasure ν ∧ ∀ A, MeasurableSet A → rawNullStateFamily b A = (ν A).toReal) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b A
    cases b
    · simp [rawNullStateFamily]
    · change 0 ≤ (Measure.dirac true A).toReal ∧ (Measure.dirac true A).toReal ≤ 1
      refine ⟨ENNReal.toReal_nonneg, ?_⟩
      simpa only [measureReal_def] using
        (measureReal_le_one (μ := Measure.dirac true) (s := A))
  · intro A _
    exact Measurable.of_comap_le le_top
  · intro A hA
    have heq : (fun b => rawNullStateFamily b A) =ᵐ[Measure.dirac true]
        fun _ => (Measure.dirac true A).toReal := ae_at_true (by simp [rawNullStateFamily])
    have htop : (⊤ : MeasurableSpace Bool) ≤ (inferInstance : MeasurableSpace Bool) := by
      intro s _
      exact (Set.to_countable s).measurableSet
    exact heq.trans ((regularConditionalDistribution_dirac_const
      (P := Measure.dirac true) (c := true) (𝒢 := ⊤) htop).ae_eq_condexp hA)
  · exact ae_at_true ⟨Measure.dirac true, inferInstance,
      fun A _ => by simp [rawNullStateFamily]⟩

/-- The exceptional point is null, and its empty-set value is one. -/
theorem rawNullStateFamily_exceptional_empty :
    (Measure.dirac true : Measure Bool) {false} = 0 ∧ rawNullStateFamily false ∅ = 1 := by
  simp [rawNullStateFamily]

/-- This valid raw source family has no pointwise measure-valued representation. -/
theorem rawNullStateFamily_not_pointwise_measure :
    ¬ ∃ rcd : Bool → Measure Bool, ∀ b A, MeasurableSet A →
      (rcd b A).toReal = rawNullStateFamily b A := by
  rintro ⟨rcd, hrcd⟩
  have h := hrcd false ∅ MeasurableSet.empty
  simp [rawNullStateFamily] at h

/-- The general-G measure-valued witness supplies the raw source existence
clauses without asserting representation of every raw family. -/
theorem measure_valued_witness_gives_raw_family
    [StandardBorelSpace Ω] [Nonempty Ω] [IsFiniteMeasure μ]
    {𝒢 : MeasurableSpace α} {Y : α → Ω} (h𝒢 : 𝒢 ≤ mα)
    (hY : @Measurable α Ω mα ‹MeasurableSpace Ω› Y) :
    ∃ p : α → Set Ω → ℝ,
      (∀ a A, 0 ≤ p a A ∧ p a A ≤ 1) ∧
      (∀ {A : Set Ω}, MeasurableSet A → Measurable[𝒢] fun a => p a A) ∧
      (∀ {A : Set Ω}, MeasurableSet A →
        (fun a => p a A) =ᵐ[μ] μ⟦Y ⁻¹' A | 𝒢⟧) ∧
      (∀ᵐ a ∂μ, ∃ ν : Measure Ω, IsProbabilityMeasure ν ∧
        ∀ A, MeasurableSet A → p a A = (ν A).toReal) := by
  obtain ⟨rcd, hrcd⟩ := exists_regularConditionalDistribution_family_of_le (μ := μ) h𝒢 hY
  refine ⟨fun a A => (rcd a A).toReal, ?_, ?_, hrcd.ae_eq_condexp, ?_⟩
  · intro a A
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    have hbound : rcd a A ≤ 1 :=
      (measure_mono (Set.subset_univ A)).trans (hrcd.mass_le_one a)
    simpa using ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤) hbound
  · exact fun hA => (hrcd.measurable_eval hA).ennreal_toReal
  · filter_upwards [hrcd.ae_isProbabilityMeasure] with a ha
    exact ⟨rcd a, ha, fun A _ => rfl⟩

end RawSourceRefinement

section KernelMeasurabilitySetup

/-- A constant Markov kernel with explicitly top conditioning/outcome spaces. -/
noncomputable def boolTopDiracKernel :
    @Kernel Bool Bool (⊤ : MeasurableSpace Bool) (⊤ : MeasurableSpace Bool) :=
  @Kernel.const Bool Bool (⊤ : MeasurableSpace Bool) (⊤ : MeasurableSpace Bool)
    (@Measure.dirac Bool (⊤ : MeasurableSpace Bool) true)

/-- The identity is not measurable from bottom to top; both spaces are explicit. -/
theorem bool_id_not_measurable_bot_top :
    ¬ @Measurable Bool Bool (⊥ : MeasurableSpace Bool) (⊤ : MeasurableSpace Bool) id := by
  intro h
  have htop : @MeasurableSet Bool (⊤ : MeasurableSpace Bool) ({true} : Set Bool) := by trivial
  have hbot := h htop
  change @MeasurableSet Bool (⊥ : MeasurableSpace Bool) ({true} : Set Bool) at hbot
  rcases MeasurableSpace.measurableSet_bot_iff.mp hbot with hempty | huniv
  · have htrue : true ∈ ({true} : Set Bool) := by simp
    rw [hempty] at htrue
    simpa using htrue
  · have hfalse : false ∈ ({true} : Set Bool) := by rw [huniv]; simp
    simpa using hfalse

/-- The old kernel fields accept a nonmeasurable conditioning map when the
source measure is zero on the bottom measurable space. -/
theorem kernel_nonmeasurable_conditioning_zero_old_fields :
    IsMarkovKernel boolTopDiracKernel ∧
    (∀ {s : Set Bool}, @MeasurableSet Bool (⊤ : MeasurableSpace Bool) s →
      (fun a : Bool => (boolTopDiracKernel (id a)).real s) =ᵐ[(0 : @Measure Bool ⊥)]
        (0 : @Measure Bool ⊥)⟦(fun _ : Bool => true) ⁻¹' s |
          MeasurableSpace.comap (id : Bool → Bool) (⊤ : MeasurableSpace Bool)⟧) := by
  refine ⟨?_, fun _ => by
    rw [ae_zero]
    change True
    trivial⟩
  change IsMarkovKernel (@Kernel.const Bool Bool ⊤ ⊤ (@Measure.dirac Bool ⊤ true))
  infer_instance

/-- The explicit conditioning-measurability field rejects this zero-measure case. -/
theorem kernel_nonmeasurable_conditioning_zero_rejected :
    ¬ @IsRegularConditionalDistribution Bool Bool Bool ⊥ ⊤ ⊤
      boolTopDiracKernel (fun _ => true) id (0 : @Measure Bool ⊥) := by
  intro h
  exact bool_id_not_measurable_bot_top h.measurable_conditioning

/-- The old fields also accept a nonmeasurable target with a measurable
constant conditioning map under the explicit bottom-space zero measure. -/
theorem kernel_nonmeasurable_target_zero_old_fields :
    IsMarkovKernel boolTopDiracKernel ∧
    (∀ {s : Set Bool}, @MeasurableSet Bool (⊤ : MeasurableSpace Bool) s →
      (fun a : Bool => (boolTopDiracKernel true).real s) =ᵐ[(0 : @Measure Bool ⊥)]
        (0 : @Measure Bool ⊥)⟦(id : Bool → Bool) ⁻¹' s |
          MeasurableSpace.comap (fun _ : Bool => true) (⊤ : MeasurableSpace Bool)⟧) := by
  refine ⟨?_, fun _ => by
    rw [ae_zero]
    change True
    trivial⟩
  change IsMarkovKernel (@Kernel.const Bool Bool ⊤ ⊤ (@Measure.dirac Bool ⊤ true))
  infer_instance

/-- The target-measurability field rejects the independent target-map defect. -/
theorem kernel_nonmeasurable_target_zero_rejected :
    ¬ @IsRegularConditionalDistribution Bool Bool Bool ⊥ ⊤ ⊤
      boolTopDiracKernel id (fun _ => true) (0 : @Measure Bool ⊥) := by
  intro h
  exact bool_id_not_measurable_bot_top h.measurable_target

end KernelMeasurabilitySetup

end MathlibExtTest.Probability.RegularConditionalDistribution
