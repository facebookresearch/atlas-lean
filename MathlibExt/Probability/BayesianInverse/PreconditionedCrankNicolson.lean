/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Kernel.Invariance
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Deterministic

/-!
# The preconditioned Crank–Nicolson proposal is reversible for its Gaussian prior

For a centred Gaussian prior `μ₀ = N(0, C)` and `β ∈ [-1, 1]`, the **preconditioned
Crank–Nicolson (pCN)** proposal moves from `u` to

`v = √(1 - β²) u + β ξ`, `ξ ~ μ₀` independent of `u`

(Cotter, Roberts, Stuart and White, *MCMC methods for functions: modifying old algorithms to make
them faster*, Statist. Sci. 28 (2013), arXiv:1202.0709, equation (4.8), which is their pCN
proposal (4.7) rewritten with `β² = 8δ/(2+δ)²` and `β ∈ [0, 1]`;
Dashti and Stuart, *The Bayesian Approach to Inverse Problems*, arXiv:1302.6989v4, Algorithm 5.10).
Dashti and Stuart, Example 5.3, show that this kernel is reversible with respect to `μ₀`: the
joint law of `(u, v)` with `u ~ μ₀` is symmetric. That is what makes the Metropolis–Hastings
acceptance probability `min{1, exp(Φ(u) - Φ(v))}` depend only on the potential (their
Theorem 5.8), and the algorithm well defined on function space.

## Main results

* `pcnProposal β (u, ξ) = √(1 - β²) • u + β • ξ`.
* `map_swap_pcn_eq`: for a centred Gaussian measure `μ₀` on a separable Banach space and
  `-1 ≤ β ≤ 1`, the law of `(u, v)` under `μ₀ ⊗ μ₀` is invariant under swapping the coordinates.
* `pcnKernel μ₀ β`: the pCN proposal as a Markov kernel, `u ↦ law of √(1 - β²) u + β ξ`.
* `isReversible_pcnKernel` (**prior reversibility of pCN**) and `invariant_pcnKernel`
  (the prior is invariant), in the sense of Mathlib's `ProbabilityTheory.Kernel.IsReversible`.

The proof is Mathlib's rotation invariance of `μ₀ ⊗ μ₀`
(`ProbabilityTheory.IsGaussian.map_rotation_eq_self`, the key step of Fernique's theorem) with
angle `θ = arcsin β`, combined with the reflection `(x, y) ↦ (x, -y)`. It holds on any separable
Banach space, so in particular in every finite dimension; Dashti and Stuart state it on a
separable Hilbert space.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.BayesianInverse

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **The pCN proposal map.** `pcnProposal β (u, ξ) = √(1 - β²) u + β ξ` (Dashti and Stuart,
arXiv:1302.6989v4, Algorithm 5.10, step 2). -/
noncomputable def pcnProposal (β : ℝ) (p : E × E) : E :=
  √(1 - β ^ 2) • p.1 + β • p.2

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Continuity of the pCN proposal map.** -/
theorem continuous_pcnProposal (β : ℝ) : Continuous (pcnProposal (E := E) β) := by
  unfold pcnProposal; fun_prop

variable [CompleteSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] in
/-- **Measurability of the pCN proposal map.** -/
theorem measurable_pcnProposal (β : ℝ) : Measurable (pcnProposal (E := E) β) :=
  (continuous_pcnProposal β).measurable

/-- A centred Gaussian measure is symmetric: `μ.map (-·) = μ`. Obtained from rotation
invariance of `μ ⊗ μ` with angle `π`. -/
private lemma map_neg_eq_self (μ : Measure E) [IsGaussian μ] (hμ : μ[id] = 0) :
    μ.map (fun x ↦ -x) = μ := by
  have hrot := IsGaussian.map_rotation_eq_self (μ := μ) hμ Real.pi
  have hfun : (ContinuousLinearMap.rotation Real.pi : E × E → E × E) = fun p ↦ (-p.1, -p.2) := by
    funext p; rw [ContinuousLinearMap.rotation_apply]; simp
  rw [hfun] at hrot
  have h1 := congrArg (fun ν : Measure (E × E) ↦ ν.map Prod.fst) hrot
  rw [Measure.map_map measurable_fst (by fun_prop), Measure.map_fst_prod] at h1
  rw [show (Prod.fst ∘ fun p : E × E ↦ (-p.1, -p.2)) = (fun x ↦ -x) ∘ Prod.fst from rfl,
    ← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod] at h1
  simpa using h1

/-- **The joint law of a pCN step is symmetric.** If `μ₀` is a centred Gaussian measure on a
separable Banach space and `-1 ≤ β ≤ 1`, then for `(u, ξ) ~ μ₀ ⊗ μ₀` the pair
`(u, √(1 - β²) u + β ξ)` has the same law as `(√(1 - β²) u + β ξ, u)`. This is the computation of
Dashti and Stuart (arXiv:1302.6989v4), Example 5.3, which they carry out on a separable Hilbert
space through the covariance identities (5.3). -/
theorem map_swap_pcn_eq (μ₀ : Measure E) [IsGaussian μ₀] (hμ₀ : μ₀[id] = 0) {β : ℝ}
    (hβ₁ : -1 ≤ β) (hβ₂ : β ≤ 1) :
    ((μ₀.prod μ₀).map fun p ↦ (p.1, pcnProposal β p)).map Prod.swap =
      (μ₀.prod μ₀).map fun p ↦ (p.1, pcnProposal β p) := by
  set ρ := √(1 - β ^ 2) with hρ
  have hρ2 : ρ ^ 2 = 1 - β ^ 2 := Real.sq_sqrt (by nlinarith)
  set θ := Real.arcsin β
  have hsin : Real.sin θ = β := Real.sin_arcsin hβ₁ hβ₂
  have hcos : Real.cos θ = ρ := Real.cos_arcsin β
  -- the reflection `T (x, y) = (ρ x + β y, β x - ρ y)` preserves `μ₀ ⊗ μ₀`
  set T : E × E → E × E := fun p ↦ (ρ • p.1 + β • p.2, β • p.1 - ρ • p.2)
  have hT : T = (fun p : E × E ↦ (p.1, -p.2)) ∘ ContinuousLinearMap.rotation θ := by
    funext p
    simp only [T, Function.comp_apply, ContinuousLinearMap.rotation_apply, hsin, hcos,
      neg_smul, Prod.mk.injEq, true_and, sub_eq_add_neg]
    abel
  have hTμ : (μ₀.prod μ₀).map T = μ₀.prod μ₀ := by
    rw [hT, ← Measure.map_map (g := fun p : E × E ↦ (p.1, -p.2))
      (measurable_fst.prodMk measurable_snd.neg)
      (ContinuousLinearMap.rotation (E := E) θ).continuous.measurable,
      IsGaussian.map_rotation_eq_self hμ₀ θ]
    rw [show (fun p : E × E ↦ (p.1, -p.2)) = Prod.map id (fun x ↦ -x) from rfl,
      ← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id,
      map_neg_eq_self μ₀ hμ₀]
  set π : E × E → E × E := fun p ↦ (p.1, pcnProposal β p)
  have hπ : Measurable π := measurable_fst.prodMk (measurable_pcnProposal β)
  have hcomm : Prod.swap ∘ π = π ∘ T := by
    funext p
    simp only [Function.comp_apply, Prod.swap_prod_mk, π, T, pcnProposal, Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    rw [← hρ]
    have : ρ • (ρ • p.1 + β • p.2) + β • (β • p.1 - ρ • p.2) = (ρ ^ 2 + β ^ 2) • p.1 := by
      simp only [smul_add, smul_sub, smul_smul, add_smul]
      rw [mul_comm β ρ, sq, sq]; abel
    rw [this, hρ2, sub_add_cancel, one_smul]
  calc ((μ₀.prod μ₀).map π).map Prod.swap = (μ₀.prod μ₀).map (Prod.swap ∘ π) :=
        Measure.map_map measurable_swap hπ
    _ = (μ₀.prod μ₀).map (π ∘ T) := by rw [hcomm]
    _ = ((μ₀.prod μ₀).map T).map π := (Measure.map_map hπ (by fun_prop)).symm
    _ = (μ₀.prod μ₀).map π := by rw [hTμ]

/-- **The pCN proposal kernel.** `pcnKernel μ₀ β u` is the law of `√(1 - β²) u + β ξ` with
`ξ ~ μ₀`; for `μ₀ = N(0, C)` this is `N(√(1 - β²) u, β² C)` (Dashti and Stuart,
arXiv:1302.6989v4, Example 5.3 and Algorithm 5.10). -/
noncomputable def pcnKernel (μ₀ : Measure E) [IsProbabilityMeasure μ₀] (β : ℝ) : Kernel E E :=
  (Kernel.deterministic id measurable_id ×ₖ Kernel.const E μ₀).map (pcnProposal β)

instance (μ₀ : Measure E) [IsProbabilityMeasure μ₀] (β : ℝ) :
    IsMarkovKernel (pcnKernel μ₀ β) :=
  Kernel.IsMarkovKernel.map _ (measurable_pcnProposal β)

omit [CompleteSpace E] in
/-- **Evaluation of the pCN kernel.** The pCN kernel at `u` is the image of `μ₀` under
`ξ ↦ √(1 - β²) u + β ξ`. -/
theorem pcnKernel_apply (μ₀ : Measure E) [IsProbabilityMeasure μ₀] (β : ℝ) (u : E) :
    pcnKernel μ₀ β u = μ₀.map fun ξ ↦ pcnProposal β (u, ξ) := by
  rw [pcnKernel, Kernel.map_apply _ (measurable_pcnProposal β), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (measurable_pcnProposal β) measurable_prodMk_left]
  rfl

omit [CompleteSpace E] in
/-- The flow `∫_A Q(u, B) μ₀(du)` of the pCN kernel is the mass of `A × B` under the joint law of
`(u, v)`. -/
private lemma setLIntegral_pcnKernel (μ₀ : Measure E) [IsProbabilityMeasure μ₀] (β : ℝ)
    {A B : Set E} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ x in A, pcnKernel μ₀ β x B ∂μ₀ =
      ((μ₀.prod μ₀).map fun p ↦ (p.1, pcnProposal β p)) (A ×ˢ B) := by
  have hπ : Measurable fun p : E × E ↦ (p.1, pcnProposal β p) :=
    measurable_fst.prodMk (measurable_pcnProposal β)
  rw [Measure.map_apply hπ (hA.prod hB), Measure.prod_apply (hπ (hA.prod hB)),
    ← lintegral_indicator hA]
  refine lintegral_congr fun x ↦ ?_
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, pcnKernel_apply,
      Measure.map_apply (f := fun ξ ↦ pcnProposal β (x, ξ))
        ((measurable_pcnProposal β).comp measurable_prodMk_left) hB]
    congr 1
    ext ξ; simp [hx]
  · rw [Set.indicator_of_notMem hx]
    symm
    convert measure_empty (μ := μ₀)
    ext ξ; simp [hx]

/-- **Prior reversibility of the pCN proposal.** For a centred Gaussian measure `μ₀` on a
separable Banach space and `-1 ≤ β ≤ 1`, the pCN kernel satisfies detailed balance with respect
to `μ₀`: `∫_A Q(u, B) μ₀(du) = ∫_B Q(u, A) μ₀(du)` for all measurable `A`, `B` (Dashti and Stuart,
arXiv:1302.6989v4, Example 5.3, there on a separable Hilbert space). -/
theorem isReversible_pcnKernel (μ₀ : Measure E) [IsGaussian μ₀] (hμ₀ : μ₀[id] = 0) {β : ℝ}
    (hβ₁ : -1 ≤ β) (hβ₂ : β ≤ 1) : Kernel.IsReversible (pcnKernel μ₀ β) μ₀ := by
  intro A B hA hB
  rw [setLIntegral_pcnKernel μ₀ β hA hB, setLIntegral_pcnKernel μ₀ β hB hA]
  conv_rhs => rw [← map_swap_pcn_eq μ₀ hμ₀ hβ₁ hβ₂]
  rw [Measure.map_apply measurable_swap (hB.prod hA), Set.preimage_swap_prod]

/-- **The pCN proposal preserves its Gaussian prior.** If `u ~ μ₀` then
`√(1 - β²) u + β ξ ~ μ₀` (Dashti and Stuart, arXiv:1302.6989v4, Example 5.3 with Lemma 5.2). -/
theorem invariant_pcnKernel (μ₀ : Measure E) [IsGaussian μ₀] (hμ₀ : μ₀[id] = 0) {β : ℝ}
    (hβ₁ : -1 ≤ β) (hβ₂ : β ≤ 1) : Kernel.Invariant (pcnKernel μ₀ β) μ₀ :=
  (isReversible_pcnKernel μ₀ hμ₀ hβ₁ hβ₂).invariant

end MathlibExt.Probability.BayesianInverse
