/-
Copyright (c) 2026 Paul-Antoine Bonin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Antoine Bonin
-/
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# CDIS Probabilités IV: continuous images of convergent sequences

* id 72: if `f` is continuous, then `X_n → X` almost surely implies `f(X_n) → f(X)` almost
  surely, and `X_n → X` in probability implies `f(X_n) → f(X)` in probability.

The second part goes through the subsequence characterisation of convergence in probability
(`exists_seq_tendstoInMeasure_atTop_iff`): every subsequence has a further subsequence that
converges almost surely, and continuity preserves that.
-/

open MeasureTheory Filter Topology

namespace CDIS

variable {Ω E F : Type*} [MeasurableSpace Ω] {P : Measure Ω} [MetricSpace E] [MetricSpace F]
  {f : E → F} {X : ℕ → Ω → E} {Y : Ω → E}

/-- CDIS P.IV, id 72 (1): almost sure convergence is preserved by continuous maps. -/
theorem tendsto_ae_comp_continuous (hf : Continuous f)
    (h : ∀ᵐ ω ∂P, Tendsto (fun n ↦ X n ω) atTop (𝓝 (Y ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ f (X n ω)) atTop (𝓝 (f (Y ω))) :=
  h.mono fun _ hω ↦ (hf.tendsto _).comp hω

/-- CDIS P.IV, id 72 (2): convergence in probability is preserved by continuous maps. -/
theorem tendstoInMeasure_comp_continuous [IsFiniteMeasure P] (hf : Continuous f)
    (hX : ∀ n, AEStronglyMeasurable (X n) P) (h : TendstoInMeasure P X atTop Y) :
    TendstoInMeasure P (fun n ω ↦ f (X n ω)) atTop (fun ω ↦ f (Y ω)) := by
  rw [exists_seq_tendstoInMeasure_atTop_iff fun n ↦ hf.comp_aestronglyMeasurable (hX n)]
  intro ns hns
  obtain ⟨ns', hns', hae⟩ := (exists_seq_tendstoInMeasure_atTop_iff hX).1 h ns hns
  exact ⟨ns', hns', hae.mono fun _ hω ↦ (hf.tendsto _).comp hω⟩

end CDIS
