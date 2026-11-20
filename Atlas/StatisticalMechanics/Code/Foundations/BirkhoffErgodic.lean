/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































import Mathlib
import Code.Foundations.BirkhoffPointwise

open MeasureTheory Filter Finset Function MeasurableSpace
open scoped Topology ENNReal

namespace StatMech

namespace BirkhoffAE

namespace Ergodic

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {f : α → ℝ}












theorem birkhoffLimit_ae_eq_const (hT : _root_.Ergodic T μ) [IsProbabilityMeasure μ]
    (hf : Integrable f μ) :
    birkhoffLimit T f =ᵐ[μ] Function.const α (∫ x, f x ∂μ) := by
  
  obtain ⟨c, hc⟩ := hT.ae_eq_const_of_ae_eq_comp_ae
    (integrable_birkhoffLimit hT.toMeasurePreserving hf).aestronglyMeasurable
    (by filter_upwards with x; exact birkhoffLimit_comp x)
  
  have hint : ∫ x, birkhoffLimit T f x ∂μ = ∫ x, f x ∂μ := by
    have := setIntegral_birkhoffLimit hT.toMeasurePreserving hf
      (E := Set.univ) MeasurableSet.univ (fun x => by simp)
    simpa using this.symm
  
  have hc_int : ∫ x, birkhoffLimit T f x ∂μ = c := by
    rw [integral_congr_ae hc]; simp
  
  have hceq : c = ∫ x, f x ∂μ := by rw [← hc_int, hint]
  rwa [hceq] at hc









theorem tendsto_birkhoffAverage_integral_ae (hT : _root_.Ergodic T μ) [IsProbabilityMeasure μ]
    (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 (∫ y, f y ∂μ)) := by
  filter_upwards [tendsto_birkhoffAverage_ae hT.toMeasurePreserving hf,
    birkhoffLimit_ae_eq_const hT hf] with x hx hxc
  
  rwa [hxc] at hx






theorem tendsto_birkhoffSum_div_integral_ae (hT : _root_.Ergodic T μ) [IsProbabilityMeasure μ]
    (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f (T^[k] x)) atTop
      (𝓝 (∫ y, f y ∂μ)) := by
  filter_upwards [tendsto_birkhoffAverage_integral_ae hT hf] with x hx
  
  have heq : (fun n => birkhoffAverage ℝ T f n x)
      = (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f (T^[k] x)) := by
    funext n; simp [birkhoffAverage, birkhoffSum, smul_eq_mul]
  rwa [heq] at hx

end Ergodic

end BirkhoffAE

end StatMech
