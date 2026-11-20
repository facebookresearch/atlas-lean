/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































import Mathlib
import Code.FK.Ergodicity
import Code.Inequalities.ReimerCompression

open Set MeasureTheory ProbabilityTheory MeasurableSpace
open scoped ENNReal NNReal

namespace StatMech.Walls

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {E : Type*}












theorem bfc2_dependsOn_measurableSet_iSup {T : Set E}
    {B : Set (ConfigSpace E)} (hBmeas : MeasurableSet B) (hB : DependsOn B T) :
    MeasurableSet[⨆ e ∈ T, MeasurableSpace.comap (fun ω : ConfigSpace E => ω e) inferInstance] B := by
  classical
  
  let ιf : (↥T → Bool) → ConfigSpace E :=
    fun y e => if h : e ∈ T then y ⟨e, h⟩ else false
  
  have hπM : @Measurable (ConfigSpace E) (↥T → Bool)
      (⨆ e ∈ T, MeasurableSpace.comap (fun ω : ConfigSpace E => ω e) inferInstance) _
      (fun (ω : ConfigSpace E) (i : ↥T) => ω (i : E)) := by
    rw [measurable_iff_comap_le]
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
      Function.comp_def, iSup_le_iff]
    intro i
    exact le_iSup₂ (f := fun e (_ : e ∈ T) =>
      MeasurableSpace.comap (fun ω : ConfigSpace E => ω e)
        (inferInstance : MeasurableSpace Bool)) (i : E) i.2
  
  have hιM : @Measurable (↥T → Bool) (ConfigSpace E) inferInstance inferInstance ιf :=
    measurable_pi_lambda ιf (fun e => by
      by_cases h : e ∈ T
      · simp only [ιf, dif_pos h]; exact measurable_pi_apply _
      · simp only [ιf, dif_neg h]; exact measurable_const)
  
  have hC : MeasurableSet (ιf ⁻¹' B) := hιM hBmeas
  have hpre : (fun (ω : ConfigSpace E) (i : ↥T) => ω (i : E)) ⁻¹' (ιf ⁻¹' B) = B := by
    ext ω
    simp only [Set.mem_preimage]
    have hag : agreeOn T ω (ιf (fun (i : ↥T) => ω (i : E))) := by
      intro e he
      change (if h : e ∈ T then (fun (i : ↥T) => ω (i : E)) ⟨e, h⟩ else false) = ω e
      rw [dif_pos he]
    exact (hB ω (ιf (fun (i : ↥T) => ω (i : E))) hag).symm
  rw [← hpre]
  exact hπM hC
















theorem bfc2_indep_finite_cofinite (p : ℝ≥0) (hp : p ≤ 1)
    (I : Finset E) {A B : Set (ConfigSpace E)}
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hA : DependsOn A (↑I : Set E)) (hB : DependsOn B (↑I : Set E)ᶜ) :
    bernoulliProductMeasure (E := E) p hp (A ∩ B)
      = bernoulliProductMeasure (E := E) p hp A
        * bernoulliProductMeasure (E := E) p hp B := by
  classical
  set μ := bernoulliProductMeasure (E := E) p hp with hμ
  
  set mc : E → MeasurableSpace (ConfigSpace E) :=
    fun e => MeasurableSpace.comap (fun ω : ConfigSpace E => ω e) inferInstance with hmc
  
  have hiIndep : iIndep mc μ :=
    (iIndepFun_iff_iIndep (fun _ : E => (inferInstance : MeasurableSpace Bool))
      (fun (e : E) (ω : ConfigSpace E) => ω e) μ).mp (StatMech.FK.bernoulli_iIndepFun (E := E) p hp)
  have h_le : ∀ e, mc e ≤ (inferInstance : MeasurableSpace (ConfigSpace E)) :=
    fun e => (measurable_pi_apply e).comap_le
  
  have hIndep : Indep (⨆ e ∈ (↑I : Set E), mc e) (⨆ e ∈ (↑I : Set E)ᶜ, mc e) μ :=
    ProbabilityTheory.indep_biSup_compl h_le hiIndep (↑I : Set E)
  
  have hAM : MeasurableSet[⨆ e ∈ (↑I : Set E), mc e] A :=
    bfc2_dependsOn_measurableSet_iSup hAmeas hA
  have hBM : MeasurableSet[⨆ e ∈ (↑I : Set E)ᶜ, mc e] B :=
    bfc2_dependsOn_measurableSet_iSup hBmeas hB
  exact (hIndep.indepSet_of_measurableSet hAM hBM).measure_inter_eq_mul

end StatMech.Walls
