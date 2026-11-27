/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Moments.Variance
import MathlibExt.Probability.MonteCarloRate

/-!
# Bühlmann moments in a finite mixture

Draw a class `θ` from `μ`, then a tuple from the product of `n` copies of `ν θ`.
The first marginal of this joint law is `μ` (`Measure.fst_compProd`). The coordinates are
independent under each product law, not necessarily under the mixture. Integrating against
the kernel, rather than dividing by the mass of a class, also covers classes of mass zero.

## Reference

* [*Bühlmann Model*](https://home.cc.umanitoba.ca/~farhadi/ACT4630Winter2017/Buhlmann.pdf),
  ACT 4630, University of Manitoba, Winter 2017. Page 1 defines EPV and VHM. In “Derivation
  of the Credibility factor in Bühlmann Model”, p. 3 centres the sample mean at the class
  mean, and p. 4, (4), gives the residual second moment as EPV divided by sample size.
  The identities below are the consequences for the finite joint model.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.FiniteMixture

variable {Θ S : Type*} [MeasurableSpace Θ] [MeasurableSpace S]

/-- The sampling kernel at `θ` is the product of `n` copies of the component law `ν θ`.
Thus `μ ⊗ₘ sampleKernel n ν` retains the single class draw along with the whole sample. -/
noncomputable def sampleKernel [Finite Θ] [MeasurableSingletonClass Θ]
    (n : ℕ) (ν : Θ → Measure S) : Kernel Θ (Fin n → S) :=
  Kernel.ofFunOfCountable fun θ => Measure.pi fun _ : Fin n => ν θ

instance [Finite Θ] [MeasurableSingletonClass Θ] (n : ℕ) (ν : Θ → Measure S)
    [∀ θ, IsProbabilityMeasure (ν θ)] : IsMarkovKernel (sampleKernel n ν) where
  isProbabilityMeasure θ := inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin n => ν θ))

private theorem product_moments [Finite S] [MeasurableSingletonClass S]
    (q : Measure S) [IsProbabilityMeasure q] (f : S → ℝ) (n : ℕ) (hn : 0 < n) :
    let Q := Measure.pi fun _ : Fin n => q
    let B := fun x : Fin n → S => (∑ i, f (x i)) / (n : ℝ)
    (∫ x, B x ∂Q) = (∫ s, f s ∂q) ∧ variance B Q = variance f q / n := by
  let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hf : HasLaw f (q.map f) q := hasLaw_map Measurable.of_discrete.aemeasurable
  have hcoord (i : Fin n) : IdentDistrib (fun x : Fin n → S => f (x i)) f
      (Measure.pi fun _ : Fin n => q) q :=
    (hf.comp (measurePreserving_eval (fun _ : Fin n => q) i).hasLaw).identDistrib hf
  constructor
  · simpa only [Fintype.card_fin] using integral_sample_mean
      (X := fun (i : Fin n) (x : Fin n → S) => f (x i)) (fun _ => Integrable.of_finite)
      (fun i => (hcoord i).integral_eq)
  · simpa only [Fintype.card_fin] using variance_sample_mean
      (X := fun (i : Fin n) (x : Fin n → S) => f (x i)) (fun _ => MemLp.of_discrete)
      (iIndepFun_pi (μ := fun _ : Fin n => q) (X := fun _ => f)
        (fun _ => Measurable.of_discrete.aemeasurable)) (fun i => (hcoord i).variance_eq)

/-- **Bühlmann moment identities.** In a finite latent mixture with `n ≥ 1` observations,
let `m θ` and `v θ` be the mean and variance of the real observation under component `ν θ`.
Under the joint law of class and sample, the covariance of the class mean and the sample
mean is `Var_μ(m)`; the variance of the sample mean is `Var_μ(m) + E_μ[v] / n`. -/
theorem buhlmann_moments [Finite Θ] [Finite S] [MeasurableSingletonClass Θ]
    [MeasurableSingletonClass S] (μ : Measure Θ) [IsProbabilityMeasure μ]
    (ν : Θ → Measure S) [∀ θ, IsProbabilityMeasure (ν θ)] (f : S → ℝ) (n : ℕ) (hn : 0 < n) :
    let P := μ ⊗ₘ sampleKernel n ν
    let m := fun θ => ∫ s, f s ∂ν θ
    let v := fun θ => variance f (ν θ)
    let B := fun x : Fin n → S => (∑ i, f (x i)) / (n : ℝ)
    covariance (fun z => m z.1) (fun z => B z.2) P = variance m μ ∧
      variance (fun z => B z.2) P = variance m μ + (∫ θ, v θ ∂μ) / n := by
  intro P m v B
  let κ := sampleKernel n ν
  have hprod (θ : Θ) : (∫ x, B x ∂κ θ) = m θ ∧ variance B (κ θ) = v θ / n :=
    product_moments (ν θ) f n hn
  have tower (g : Θ × (Fin n → S) → ℝ) :
      (∫ z, g z ∂P) = ∫ θ, ∫ x, g (θ, x) ∂κ θ ∂μ :=
    Measure.integral_compProd Integrable.of_finite
  have hθ : HasLaw Prod.fst μ P := ⟨measurable_fst.aemeasurable, Measure.fst_compProd μ κ⟩
  have hM : (∫ z, m z.1 ∂P) = ∫ θ, m θ ∂μ := hθ.integral_comp (f := m) .of_discrete
  have hB : (∫ z, B z.2 ∂P) = ∫ θ, m θ ∂μ := by
    rw [tower]; simp only [(hprod _).1]
  have hMB : (∫ z, m z.1 * B z.2 ∂P) = ∫ θ, m θ ^ 2 ∂μ := by
    rw [tower]; simp only [integral_const_mul, (hprod _).1, sq]
  have hsecond (θ : Θ) : (∫ x, B x ^ 2 ∂κ θ) = m θ ^ 2 + v θ / n := by
    have h := variance_eq_sub (μ := κ θ) (X := B) MemLp.of_discrete
    change variance B (κ θ) = (∫ x, B x ^ 2 ∂κ θ) - (∫ x, B x ∂κ θ) ^ 2 at h
    rw [(hprod θ).1, (hprod θ).2] at h
    linarith
  have hBB : (∫ z, B z.2 ^ 2 ∂P) = (∫ θ, m θ ^ 2 ∂μ) + (∫ θ, v θ ∂μ) / n := by
    rw [tower]; simp only [hsecond, integral_add Integrable.of_finite Integrable.of_finite,
      integral_div]
  rw [variance_eq_sub (μ := μ) (X := m) MemLp.of_discrete,
    covariance_eq_sub MemLp.of_discrete MemLp.of_discrete, variance_eq_sub MemLp.of_discrete]
  change (∫ z, m z.1 * B z.2 ∂P) - (∫ z, m z.1 ∂P) * (∫ z, B z.2 ∂P) = _ ∧
    (∫ z, B z.2 ^ 2 ∂P) - (∫ z, B z.2 ∂P) ^ 2 = _
  rw [hMB, hM, hB, hBB]
  simp only [Pi.pow_apply]
  constructor <;> ring

end MathlibExt.Probability.FiniteMixture
