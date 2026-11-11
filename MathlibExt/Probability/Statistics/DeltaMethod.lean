/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Slutsky
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# The delta method

If `r n • (X n - θ)` converges in distribution to `Z` with `r n → ∞`, and `g` is Fréchet
differentiable at `θ` with derivative `L`, then `r n • (g (X n) - g θ)` converges in distribution
to `L Z`. This is the first-order delta method; nothing here concerns the second-order limit law
in the degenerate case `L = 0`, where the conclusion only says that the first-order scaled
differences converge to the constant `0`.

## Main statements

* `MeasureTheory.TendstoInDistribution.delta_method`: the delta method for maps between real
  normed spaces.
* `MeasureTheory.TendstoInDistribution.delta_method_real`: the one-dimensional form with
  `HasDerivAt g g' θ`, limit `g' * Z`.

## Proof

With `S n := r n • (X n - θ)`:

1. `X n → θ` in probability: `X n - θ = (r n)⁻¹ • S n` once `r n ≠ 0`, Slutsky's scalar-multiple
   form gives `(r n)⁻¹ • S n →ᵈ 0 • Z = 0`, and convergence in distribution to a constant is
   convergence in probability to it.
2. The remainder `R n := g (X n) - g θ - L (X n - θ)` satisfies `r n • R n = ‖S n‖ • ψ (X n)` for
   `r n ≥ 0`, where `ψ x := ‖x - θ‖⁻¹ • (g x - g θ - L (x - θ))` is continuous at `θ` with value
   `0` (this is `HasFDerivAt`). So `ψ (X n) → 0` in probability, and Slutsky's theorem applied to
   the pair `(‖S n‖, ψ (X n)) →ᵈ (‖Z‖, 0)` gives `‖S n‖ • ψ (X n) →ᵈ 0`, hence `→ 0` in
   probability. The joint form of Slutsky handles the dependence between the two factors, so no
   separate tightness (stochastic boundedness) argument for `S n` is needed.
3. `r n • (g (X n) - g θ) = L (S n) + r n • R n`; the first term converges in distribution to
   `L Z` by the continuous mapping theorem, and the second tends to `0` in probability.

The scale is given as `Tendsto r l atTop`. Equivalently, `r n` is eventually positive and
`(r n)⁻¹ → 0`; only these two consequences are used.

If `Z` is Gaussian, so is `L Z`, with covariance transformed by `L`; this is Mathlib's Gaussian
map API and is not restated here.

## References

* A. W. van der Vaart, *Asymptotic Statistics* (1998), Theorem 3.1.
-/

@[expose] public section

open Filter Topology

namespace MeasureTheory

variable {ι Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {μ' : Measure Ω'} {l : Filter ι}

namespace DeltaMethod

/-- A deterministic sequence converging to `c` converges to `c` in probability. -/
private theorem tendstoInMeasure_const_seq {E : Type*} [SeminormedAddCommGroup E] {a : ι → E}
    {c : E} (ha : Tendsto a l (𝓝 c)) :
    TendstoInMeasure μ (fun n (_ : Ω) ↦ a n) l (fun _ ↦ c) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(tendsto_iff_norm_sub_tendsto_zero.1 ha).eventually (gt_mem_nhds hε)]
    with n hn
  simp [hn.not_ge]

end DeltaMethod

open DeltaMethod

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [l.IsCountablyGenerated]

/-- **The delta method.** Let `r n → ∞` and suppose `r n • (X n - θ)` converges in distribution
to `Z`. If `g` has Fréchet derivative `L` at `θ`, then `r n • (g (X n) - g θ)` converges in
distribution to `L Z`.

This is the first-order statement only. When `L = 0` the limit is the constant `0`, and no
second-order limit law is asserted.

The measurability hypotheses `hX` and `hgX` are needed because `g` is only assumed
differentiable at `θ` and `X n` cannot be recovered from `r n • (X n - θ)` when `r n = 0`;
both hold automatically for measurable `X n` and continuous `g`. -/
theorem TendstoInDistribution.delta_method {X : ι → Ω → E} {Z : Ω' → E} {θ : E} {r : ι → ℝ}
    {g : E → F} {L : E →L[ℝ] F}
    (hXZ : TendstoInDistribution (fun n ω ↦ r n • (X n ω - θ)) l Z (fun _ ↦ μ) μ')
    (hr : Tendsto r l atTop) (hg : HasFDerivAt g L θ)
    (hX : ∀ n, AEMeasurable (X n) μ) (hgX : ∀ n, AEMeasurable (fun ω ↦ g (X n ω)) μ) :
    TendstoInDistribution (fun n ω ↦ r n • (g (X n ω) - g θ)) l (fun ω ↦ L (Z ω))
      (fun _ ↦ μ) μ' := by
  have hr_pos : ∀ᶠ n in l, 0 < r n := hr.eventually_gt_atTop 0
  -- Step 1: `X n → θ` in probability.
  have h1 : TendstoInDistribution (fun n ω ↦ (r n)⁻¹ • (r n • (X n ω - θ))) l
      (fun _ ↦ (0 : E)) (fun _ ↦ μ) μ' :=
    (hXZ.smul_of_tendstoInMeasure_const
      (tendstoInMeasure_const_seq (tendsto_inv_atTop_zero.comp hr))
      (fun _ ↦ aemeasurable_const)).congr (fun _ ↦ ae_of_all _ fun _ ↦ rfl)
      (ae_of_all _ fun ω ↦ zero_smul ℝ (Z ω))
  have hXθ : TendstoInMeasure μ X l (fun _ ↦ θ) := by
    have h := (tendstoInMeasure_of_tendstoInDistribution_const h1).congr'
      (f' := fun n ω ↦ X n ω - θ) ?_ EventuallyEq.rfl
    · rw [tendstoInMeasure_iff_norm] at h ⊢
      simpa using h
    · filter_upwards [hr_pos] with n hn
      exact ae_of_all _ fun ω ↦ by simp [smul_smul, inv_mul_cancel₀ hn.ne']
  -- Step 2: the scaled remainder tends to `0` in probability.
  set ψ : E → F := fun x ↦ ‖x - θ‖⁻¹ • (g x - g θ - L (x - θ)) with hψ_def
  have hψθ : ψ θ = 0 := by simp [ψ]
  have hψ : ContinuousAt ψ θ := by
    rw [ContinuousAt, hψθ, tendsto_zero_iff_norm_tendsto_zero]
    simpa [ψ, norm_smul] using hasFDerivAt_iff_tendsto.1 hg
  have hη : TendstoInMeasure μ (fun n ω ↦ ψ (X n ω)) l (fun _ ↦ 0) := by
    have h := hXθ.comp_const_of_continuousAt hψ
    rwa [hψθ] at h
  have hη_meas : ∀ n, AEMeasurable (fun ω ↦ ψ (X n ω)) μ := fun n ↦
    ((hX n).sub_const θ).norm.inv.smul (((hgX n).sub_const _).sub
      (L.continuous.measurable.comp_aemeasurable ((hX n).sub_const θ)))
  have hnorm : TendstoInDistribution (fun n ω ↦ ‖r n • (X n ω - θ)‖) l (fun ω ↦ ‖Z ω‖)
      (fun _ ↦ μ) μ' := hXZ.continuous_comp continuous_norm
  have hprod : TendstoInDistribution (fun n ω ↦ ‖r n • (X n ω - θ)‖ • ψ (X n ω)) l
      (fun _ ↦ (0 : F)) (fun _ ↦ μ) μ' :=
    (hnorm.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : ℝ × F ↦ p.1 • p.2) (by fun_prop) hη hη_meas).congr
      (fun _ ↦ ae_of_all _ fun _ ↦ rfl) (ae_of_all _ fun _ ↦ smul_zero _)
  have hrem : TendstoInMeasure μ (fun n ω ↦ r n • (g (X n ω) - g θ - L (X n ω - θ))) l
      (fun _ ↦ 0) := by
    refine (tendstoInMeasure_of_tendstoInDistribution_const hprod).congr' ?_ EventuallyEq.rfl
    filter_upwards [hr_pos] with n hn
    refine ae_of_all _ fun ω ↦ ?_
    by_cases hv : X n ω - θ = 0
    · have hXn : X n ω = θ := sub_eq_zero.1 hv
      simp [ψ, hXn]
    · simp only [ψ, norm_smul, Real.norm_of_nonneg hn.le, smul_smul, mul_assoc,
        mul_inv_cancel₀ (norm_ne_zero_iff.2 hv), mul_one]
  -- Step 3: assemble.
  have hlin : TendstoInDistribution (fun n ω ↦ L (r n • (X n ω - θ))) l (fun ω ↦ L (Z ω))
      (fun _ ↦ μ) μ' := hXZ.continuous_comp L.continuous
  refine (hlin.add_of_tendstoInMeasure_const hrem fun n ↦ ?_).congr
    (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ add_zero _)
  · exact (((hgX n).sub_const _).sub
      (L.continuous.measurable.comp_aemeasurable ((hX n).sub_const θ))).const_smul _
  · simp only [Pi.add_apply, map_smul, ← smul_add]
    congr 1
    abel

/-- **The delta method, one-dimensional form.** Let `r n → ∞` and suppose `r n * (X n - θ)`
converges in distribution to `Z`. If `g : ℝ → ℝ` has derivative `g'` at `θ`, then
`r n * (g (X n) - g θ)` converges in distribution to `g' * Z`. First-order statement only. -/
theorem TendstoInDistribution.delta_method_real {X : ι → Ω → ℝ} {Z : Ω' → ℝ} {θ : ℝ}
    {r : ι → ℝ} {g : ℝ → ℝ} {g' : ℝ}
    (hXZ : TendstoInDistribution (fun n ω ↦ r n * (X n ω - θ)) l Z (fun _ ↦ μ) μ')
    (hr : Tendsto r l atTop) (hg : HasDerivAt g g' θ)
    (hX : ∀ n, AEMeasurable (X n) μ) (hgX : ∀ n, AEMeasurable (fun ω ↦ g (X n ω)) μ) :
    TendstoInDistribution (fun n ω ↦ r n * (g (X n ω) - g θ)) l (fun ω ↦ g' * Z ω)
      (fun _ ↦ μ) μ' :=
  (hXZ.delta_method hr hg.hasFDerivAt hX hgX).congr (fun _ ↦ ae_of_all _ fun _ ↦ rfl)
    (ae_of_all _ fun ω ↦ by simp [mul_comm])

end MeasureTheory
