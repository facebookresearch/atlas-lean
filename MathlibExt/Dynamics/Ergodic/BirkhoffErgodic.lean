/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Dynamics.Ergodic.KingmanSigned.BirkhoffPointwise

/-!
# Birkhoff's ergodic theorem for ergodic maps: the limit is the mean

For an ergodic measure-preserving `T` on a probability space and integrable `f`, the pointwise
Birkhoff limit `StatMech.BirkhoffAE.birkhoffLimit T f` (from
`MathlibExt.Dynamics.Ergodic.KingmanSigned.BirkhoffPointwise`) is almost everywhere the constant
`∫ f dμ`, so the ergodic averages `(1/n) ∑_{k<n} f ∘ T^k` converge to `∫ f dμ` almost everywhere.
The convergence of `birkhoffAverage` itself is
`MathlibExt.Dynamics.Ergodic.BirkhoffWanted.birkhoff_pointwise_ergodic`.

## Main results

* `StatMech.BirkhoffAE.Ergodic.birkhoffLimit_ae_eq_const`: `birkhoffLimit T f = ∫ f dμ` a.e.
* `StatMech.BirkhoffAE.Ergodic.tendsto_birkhoffSum_div_integral_ae`: the explicit averages
  `n⁻¹ ∑_{k<n} f (T^[k] x)` tend to `∫ f dμ` a.e.

## References

* G. D. Birkhoff, *Proof of the ergodic theorem*, Proc. Natl. Acad. Sci. USA 17 (1931), 656–660.
-/

@[expose] public section

open MeasureTheory Filter Finset Function MeasurableSpace
open scoped Topology ENNReal

namespace StatMech

namespace BirkhoffAE

namespace Ergodic

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {f : α → ℝ}

/-- For ergodic `T`, the Birkhoff limit of `f` is a.e. equal to the constant `∫ f dμ`. -/
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

/-- **Birkhoff's ergodic theorem**, ergodic case, with explicit averages: `n⁻¹ ∑_{k<n} f (T^[k] x)`
tends to `∫ f dμ` for a.e. `x`. Birkhoff, *Proof of the ergodic theorem*, 1931. -/
theorem tendsto_birkhoffSum_div_integral_ae (hT : _root_.Ergodic T μ) [IsProbabilityMeasure μ]
    (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f (T^[k] x)) atTop
      (𝓝 (∫ y, f y ∂μ)) := by
  filter_upwards [MathlibExt.Dynamics.Ergodic.BirkhoffWanted.birkhoff_pointwise_ergodic hT hf]
    with x hx
  have heq : (fun n => birkhoffAverage ℝ T f n x)
      = (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f (T^[k] x)) := by
    funext n; simp [birkhoffAverage, birkhoffSum, smul_eq_mul]
  rwa [heq] at hx

end Ergodic

end BirkhoffAE

end StatMech
