/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Function.ScheffeLemma
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace MathlibExtTest.MeasureTheory.Function.ScheffeLemma

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
  {f : ℕ → α → ℝ} {g : α → ℝ}

/-- Scheffé's lemma restates with the exact public signature. -/
example (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : MemLp g 1 μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hnorm : Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 (eLpNorm g 1 μ))) :
    Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0) :=
  scheffe_lemma hfm hg hae hnorm

/-- Convergence in measure plus convergence of the `L¹` norms restates with
the exact public signature. -/
example (hf : ∀ n, MemLp (f n) 1 μ) (hg : MemLp g 1 μ)
    (hfg : TendstoInMeasure μ f atTop g)
    (hnorm : Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 (eLpNorm g 1 μ))) :
    Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0) :=
  tendsto_eLpNorm_one_of_tendstoInMeasure_of_tendsto_eLpNorm hf hg hfg hnorm

/-- Convergence in measure plus convergence of the `L¹` norms implies
uniform integrability, with the exact public signature. -/
example (hf : ∀ n, MemLp (f n) 1 μ) (hg : MemLp g 1 μ)
    (hfg : TendstoInMeasure μ f atTop g)
    (hnorm : Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 (eLpNorm g 1 μ))) :
    UniformIntegrable f 1 μ :=
  uniformIntegrable_of_tendstoInMeasure_of_tendsto_eLpNorm hf hg hfg hnorm

/-- The TFAE restates with the exact public signature. -/
example [IsFiniteMeasure μ] (hf : ∀ n, MemLp (f n) 1 μ) (hg : MemLp g 1 μ)
    (hfg : TendstoInMeasure μ f atTop g) :
    [UniformIntegrable f 1 μ,
     Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0),
     Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 (eLpNorm g 1 μ))].TFAE :=
  uniformIntegrable_tfae_of_tendstoInMeasure hf hg hfg

/-- Constant sequence: a.e. convergence and norm convergence are both
trivial, so Scheffé's lemma gives `L¹` convergence (to `0`). -/
example (hg : MemLp g 1 μ) :
    Tendsto (fun _n : ℕ => eLpNorm ((fun _ : ℕ => g) _n - g) 1 μ) atTop (𝓝 0) :=
  scheffe_lemma (fun _ => hg.aestronglyMeasurable) hg
    (ae_of_all μ fun _ => tendsto_const_nhds) tendsto_const_nhds

/-- In integral form: if `f n → g` a.e. and `∫ |f n| → ∫ |g|`, then
`∫ |f n - g| → 0`. -/
example (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : MemLp g 1 μ)
    (hf_int : ∀ n, Integrable (f n) μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hnorm_int : Tendsto (fun n => ∫ ω, (|f n ω|) ∂μ) atTop (𝓝 (∫ ω, (|g ω|) ∂μ))) :
    Tendsto (fun n => ∫ ω, (|f n ω - g ω|) ∂μ) atTop (𝓝 0) := by
  have hg_int : Integrable g μ := memLp_one_iff_integrable.mp hg
  have hf_memLp : ∀ n, MemLp (f n) 1 μ := fun n => memLp_one_iff_integrable.mpr (hf_int n)
  have hnorm : Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 (eLpNorm g 1 μ)) := by
    have e1 : ∀ n, eLpNorm (f n) 1 μ = ENNReal.ofReal (∫ ω, (|f n ω|) ∂μ) := fun n => by
      rw [eLpNorm_one_eq_lintegral_enorm (hf_memLp n).aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm (hf_int n)]
      simp only [Real.norm_eq_abs]
    have e2 : eLpNorm g 1 μ = ENNReal.ofReal (∫ ω, (|g ω|) ∂μ) := by
      rw [eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm hg_int]
      simp only [Real.norm_eq_abs]
    rw [show (fun n => eLpNorm (f n) 1 μ) = fun n => ENNReal.ofReal (∫ ω, (|f n ω|) ∂μ) from
      funext e1, e2]
    exact ENNReal.tendsto_ofReal hnorm_int
  have hL1 := scheffe_lemma hfm hg hae hnorm
  have hne : ∀ n, eLpNorm (f n - g) 1 μ ≠ ⊤ := fun n => ((hf_memLp n).sub hg).eLpNorm_lt_top.ne
  have hto : Tendsto (fun n => (eLpNorm (f n - g) 1 μ).toReal) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff hne).mpr hL1
  have eto : ∀ n, (eLpNorm (f n - g) 1 μ).toReal = ∫ ω, (|f n ω - g ω|) ∂μ := fun n => by
    rw [eLpNorm_one_eq_lintegral_enorm ((hf_memLp n).sub hg).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hf_int n).sub hg_int),
      ENNReal.toReal_ofReal (integral_nonneg (fun ω => norm_nonneg _))]
    simp only [Real.norm_eq_abs, Pi.sub_apply]
  rw [show (fun n => ∫ ω, (|f n ω - g ω|) ∂μ) =
      fun n => (eLpNorm (f n - g) 1 μ).toReal from funext (fun n => (eto n).symm)]
  exact hto

#print axioms scheffe_lemma
#print axioms tendsto_eLpNorm_one_of_tendstoInMeasure_of_tendsto_eLpNorm
#print axioms uniformIntegrable_of_tendstoInMeasure_of_tendsto_eLpNorm
#print axioms uniformIntegrable_tfae_of_tendstoInMeasure

end MathlibExtTest.MeasureTheory.Function.ScheffeLemma
