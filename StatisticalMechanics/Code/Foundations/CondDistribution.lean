/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































import Code.Foundations.ConfigSpace

open MeasureTheory ProbabilityTheory MeasurableSpace

namespace StatMech







section SubSigma

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (μ : Measure Ω) [IsFiniteMeasure μ] (m : MeasurableSpace Ω)




noncomputable def regularCondDistrib : @Kernel Ω Ω m mΩ :=
  condExpKernel (mΩ := mΩ) μ m



instance isMarkovKernel_regularCondDistrib :
    @IsMarkovKernel Ω Ω m mΩ (regularCondDistrib (mΩ := mΩ) μ m) := by
  unfold regularCondDistrib; infer_instance




theorem regularCondDistrib_comp_trim (hm : m ≤ mΩ) :
    (regularCondDistrib (mΩ := mΩ) μ m) ∘ₘ μ.trim hm = μ := by
  unfold regularCondDistrib
  exact condExpKernel_comp_trim (Ω := Ω) (m := m) (mΩ := mΩ) (μ := μ) hm





theorem regularCondDistrib_compProd_trim (hm : m ≤ mΩ) :
    (μ.trim hm) ⊗ₘ (regularCondDistrib (mΩ := mΩ) μ m)
      = @Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) (fun ω ↦ (id ω, id ω)) μ := by
  unfold regularCondDistrib
  exact compProd_trim_condExpKernel (Ω := Ω) (m := m) (mΩ := mΩ) (μ := μ) hm





theorem condExp_ae_eq_integral_regularCondDistrib (hm : m ≤ mΩ)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(regularCondDistrib (mΩ := mΩ) μ m) ω := by
  unfold regularCondDistrib
  exact condExp_ae_eq_integral_condExpKernel (Ω := Ω) (m := m) (mΩ := mΩ) (μ := μ) hm hf




theorem regularCondDistrib_ae_eq_condExp (hm : m ≤ mΩ)
    {s : Set Ω} (hs : @MeasurableSet Ω mΩ s) :
    (fun ω ↦ ((regularCondDistrib (mΩ := mΩ) μ m) ω).real s) =ᵐ[μ] μ⟦s | m⟧ := by
  unfold regularCondDistrib
  exact condExpKernel_ae_eq_condExp (Ω := Ω) (m := m) (mΩ := mΩ) (μ := μ) hm hs

end SubSigma








section Map

variable {Ω β : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  [mβ : MeasurableSpace β] (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → β)




noncomputable def condDistribGiven : Kernel β Ω := condDistrib id X μ


instance isMarkovKernel_condDistribGiven : IsMarkovKernel (condDistribGiven μ X) := by
  unfold condDistribGiven; infer_instance




theorem condDistribGiven_disintegrate :
    (μ.map X) ⊗ₘ condDistribGiven μ X = μ.map fun a ↦ (X a, a) := by
  unfold condDistribGiven
  exact compProd_map_condDistrib (Y := id) (X := X) (μ := μ) (mβ := mβ) aemeasurable_id



theorem condDistribGiven_comp (hX : AEMeasurable X μ) :
    condDistribGiven μ X ∘ₘ (μ.map X) = μ := by
  unfold condDistribGiven
  have h := condDistrib_comp_map (Y := (id : Ω → Ω)) (X := X) (μ := μ) hX aemeasurable_id
  rwa [Measure.map_id] at h




theorem condDistribGiven_ae_eq_condExp (hX : Measurable X) {s : Set Ω} (hs : MeasurableSet s) :
    (fun a ↦ (condDistribGiven μ X (X a)).real s) =ᵐ[μ] μ⟦s | mβ.comap X⟧ := by
  unfold condDistribGiven
  have h := condDistrib_ae_eq_condExp (Y := (id : Ω → Ω)) (X := X) (μ := μ) hX measurable_id hs
  simpa using h

end Map










section ConfigSpace

variable {E : Type*} [Countable E]



example : StandardBorelSpace (ConfigSpace E) := inferInstance




@[reducible] noncomputable def outsideSigma (Λ : Set E) : MeasurableSpace (ConfigSpace E) :=
  ⨆ e ∈ Λᶜ, MeasurableSpace.comap (ConfigSpace.eval e) inferInstance

omit [Countable E] in

theorem outsideSigma_le (Λ : Set E) :
    outsideSigma Λ ≤ (inferInstance : MeasurableSpace (ConfigSpace E)) :=
  iSup₂_le fun e _ => (ConfigSpace.measurable_eval e).comap_le





noncomputable def gibbsConditional (μ : Measure (ConfigSpace E)) [IsFiniteMeasure μ]
    (Λ : Set E) : @Kernel (ConfigSpace E) (ConfigSpace E) (outsideSigma Λ) _ :=
  regularCondDistrib μ (outsideSigma Λ)


instance isMarkovKernel_gibbsConditional
    (μ : Measure (ConfigSpace E)) [IsFiniteMeasure μ] (Λ : Set E) :
    @IsMarkovKernel (ConfigSpace E) (ConfigSpace E) (outsideSigma Λ) _ (gibbsConditional μ Λ) := by
  unfold gibbsConditional
  exact isMarkovKernel_regularCondDistrib μ (outsideSigma Λ)




theorem gibbsConditional_comp_trim
    (μ : Measure (ConfigSpace E)) [IsFiniteMeasure μ] (Λ : Set E) :
    gibbsConditional μ Λ ∘ₘ μ.trim (outsideSigma_le Λ) = μ := by
  unfold gibbsConditional
  exact regularCondDistrib_comp_trim μ (outsideSigma Λ) (outsideSigma_le Λ)



theorem gibbsConditional_compProd_trim
    (μ : Measure (ConfigSpace E)) [IsFiniteMeasure μ] (Λ : Set E) :
    (μ.trim (outsideSigma_le Λ)) ⊗ₘ (gibbsConditional μ Λ)
      = @Measure.map (ConfigSpace E) (ConfigSpace E × ConfigSpace E) _
          ((outsideSigma Λ).prod inferInstance) (fun ω ↦ (id ω, id ω)) μ := by
  unfold gibbsConditional
  exact regularCondDistrib_compProd_trim μ (outsideSigma Λ) (outsideSigma_le Λ)




theorem gibbsConditional_ae_eq_condExp
    (μ : Measure (ConfigSpace E)) [IsFiniteMeasure μ] (Λ : Set E)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s) :
    (fun ω ↦ ((gibbsConditional μ Λ) ω).real s) =ᵐ[μ] μ⟦s | outsideSigma Λ⟧ := by
  unfold gibbsConditional
  exact regularCondDistrib_ae_eq_condExp μ (outsideSigma Λ) (outsideSigma_le Λ) hs

end ConfigSpace

end StatMech
