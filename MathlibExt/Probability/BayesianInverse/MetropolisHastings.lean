/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BayesianInverse.WellPosedness
public import MathlibExt.Probability.BayesianInverse.PreconditionedCrankNicolson
public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Metropolis–Hastings with proposals that are reversible for the prior

For a posterior `dμ/dμ₀ ∝ exp(-Φ)` and a proposal kernel `Q` that is reversible with respect to
the prior `μ₀`, the Metropolis–Hastings kernel with acceptance probability
`a(u, v) = min{1, exp(Φ(u) - Φ(v))}`,

`P(u, dv) = a(u, v) Q(u, dv) + (∫ (1 - a(u, w)) Q(u, dw)) δ_u(dv)`,

is reversible with respect to the posterior (Dashti and Stuart, *The Bayesian Approach to
Inverse Problems*, arXiv:1302.6989v4, Theorem 5.8, with the kernel (5.5)). The acceptance
probability involves only differences of the potential, never densities with respect to a
reference measure, so the algorithm makes sense on a general state space. With the
preconditioned Crank–Nicolson proposal this is the pCN method (their Algorithm 5.10;
Cotter, Roberts, Stuart and White, Statist. Sci. 28 (2013), arXiv:1202.0709).

## Main results

* `map_swap_compProd_eq_of_isReversible`: a kernel reversible for a finite measure `μ₀` makes the
  joint law `μ₀ ⊗ Q` symmetric.
* `mhKernel Q Φ hΦ`, for a Markov proposal and a measurable potential, a Markov kernel
  (`isMarkovKernel_mhKernel`).
* `isReversible_mhKernel` (**Dashti-Stuart Theorem 5.8**) and `invariant_mhKernel`.
* `isReversible_pcn_mhKernel`: the pCN method is reversible for the posterior of a centred
  Gaussian prior on a separable Banach space.

The finite-state analogue, with acceptance ratio `min(1, π(y)Q(y,x)/(π(x)Q(x,y)))`, is
`Cslib.MachineLearning.Sampling.isReversible_mhKernel`.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.BayesianInverse

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {U : Type*} [MeasurableSpace U]

/-- **Detailed balance makes the joint law symmetric.** If `Q` is reversible with respect to a
finite measure `μ₀`, then `μ₀ ⊗ Q` is invariant under `(u, v) ↦ (v, u)`. -/
theorem map_swap_compProd_eq_of_isReversible (μ₀ : Measure U) [IsFiniteMeasure μ₀]
    (Q : Kernel U U) [IsMarkovKernel Q] (hQ : Q.IsReversible μ₀) :
    (μ₀ ⊗ₘ Q).map Prod.swap = μ₀ ⊗ₘ Q := by
  have hrect : ∀ s ∈ Set.image2 (· ×ˢ ·) {s : Set U | MeasurableSet s}
      {t : Set U | MeasurableSet t}, ((μ₀ ⊗ₘ Q).map Prod.swap) s = (μ₀ ⊗ₘ Q) s := by
    rintro _ ⟨A, hA, B, hB, rfl⟩
    rw [Measure.map_apply measurable_swap (hA.prod hB), Set.preimage_swap_prod,
      Measure.compProd_apply_prod hB hA, Measure.compProd_apply_prod hA hB]
    exact (hQ hA hB).symm
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod hrect ?_
  simpa using hrect _ ⟨Set.univ, MeasurableSet.univ, Set.univ, MeasurableSet.univ, rfl⟩

/-- Symmetric double integrals: for a kernel `Q` reversible with respect to a finite measure
`μ₀` and a measurable symmetric `m`, swapping the roles of `A` and `B` leaves
`∫_A ∫_B m(u, v) Q(u, dv) μ₀(du)` unchanged. -/
private lemma setLIntegral_setLIntegral_symm (μ₀ : Measure U) [IsFiniteMeasure μ₀]
    (Q : Kernel U U) [IsMarkovKernel Q] (hQ : Q.IsReversible μ₀) {m : U → U → ℝ≥0∞}
    (hm : Measurable (Function.uncurry m)) (hsymm : ∀ u v, m u v = m v u)
    {A B : Set U} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ x in A, ∫⁻ v in B, m x v ∂Q x ∂μ₀ = ∫⁻ x in B, ∫⁻ v in A, m x v ∂Q x ∂μ₀ := by
  have key : ∀ {A B : Set U}, MeasurableSet A → MeasurableSet B →
      ∫⁻ p, (A ×ˢ B).indicator (Function.uncurry m) p ∂(μ₀ ⊗ₘ Q) =
        ∫⁻ x in A, ∫⁻ v in B, m x v ∂Q x ∂μ₀ := by
    intro A B hA hB
    rw [Measure.lintegral_compProd (hm.indicator (hA.prod hB)), ← lintegral_indicator hA]
    refine lintegral_congr fun x ↦ ?_
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, ← lintegral_indicator hB]
      refine lintegral_congr fun v ↦ ?_
      by_cases hv : v ∈ B <;> simp [Set.indicator, hx, hv]
    · simp [Set.indicator, hx]
  rw [← key hA hB, ← key hB hA]
  conv_lhs => rw [← map_swap_compProd_eq_of_isReversible μ₀ Q hQ]
  rw [lintegral_map (hm.indicator (hA.prod hB)) measurable_swap]
  refine lintegral_congr fun p ↦ ?_
  by_cases h1 : p.2 ∈ A <;> by_cases h2 : p.1 ∈ B <;>
    simp [Set.indicator, h1, h2, Function.uncurry, hsymm p.1 p.2]

/-- **Metropolis–Hastings acceptance probability for a prior-reversible proposal.**
`a(u, v) = min{1, exp(Φ(u) - Φ(v))}` (Dashti and Stuart, arXiv:1302.6989v4, Theorem 5.8). -/
noncomputable def mhAcceptPotential (Φ : U → ℝ) (u v : U) : ℝ≥0∞ :=
  ENNReal.ofReal (min 1 (Real.exp (Φ u - Φ v)))

/-- **Measurability of the acceptance probability.** `(u, v) ↦ min{1, exp(Φ(u) - Φ(v))}` is
jointly measurable when `Φ` is measurable. -/
theorem measurable_mhAcceptPotential {Φ : U → ℝ} (hΦ : Measurable Φ) :
    Measurable (Function.uncurry (mhAcceptPotential Φ)) :=
  (measurable_const.min ((hΦ.comp measurable_fst).sub (hΦ.comp measurable_snd)).exp).ennreal_ofReal

omit [MeasurableSpace U] in
/-- **The acceptance probability is at most one.** -/
theorem mhAcceptPotential_le_one (Φ : U → ℝ) (u v : U) : mhAcceptPotential Φ u v ≤ 1 :=
  ENNReal.ofReal_le_one.2 (min_le_left _ _)

/-- **Metropolis–Hastings kernel for a prior-reversible proposal.** From `u`, propose
`v ~ Q(u, ·)` and accept it with probability `a(u, v) = min{1, exp(Φ(u) - Φ(v))}`; otherwise stay
at `u`. As a kernel, `P(u, dv) = a(u, v) Q(u, dv) + r(u) δ_u(dv)` with rejection probability
`r(u) = ∫ (1 - a(u, w)) Q(u, dw)` (Dashti and Stuart, arXiv:1302.6989v4, equation (5.5) and
Algorithm 5.6). The proposal must be a Markov kernel and the potential measurable, so that
acceptance and rejection add up to one (`isMarkovKernel_mhKernel`): for the zero proposal every
event would have probability `0`, for a proposal of mass `2` the "rejection probability" could
exceed one, and for a non-measurable `Φ` the acceptance density is not measurable, so
`Kernel.withDensity` would return the zero kernel and the transition law could lose all its
mass. -/
noncomputable def mhKernel (Q : Kernel U U) [IsMarkovKernel Q] (Φ : U → ℝ)
    (_hΦ : Measurable Φ) : Kernel U U :=
  Q.withDensity (mhAcceptPotential Φ) +
    (Kernel.deterministic id measurable_id).withDensity
      fun u _ ↦ ∫⁻ w, (1 - mhAcceptPotential Φ u w) ∂Q u

private lemma measurable_rejection (Q : Kernel U U) [IsSFiniteKernel Q] {Φ : U → ℝ}
    (hΦ : Measurable Φ) : Measurable fun u ↦ ∫⁻ w, (1 - mhAcceptPotential Φ u w) ∂Q u :=
  (measurable_const.sub (measurable_mhAcceptPotential hΦ)).lintegral_kernel_prod_right'

/-- **Evaluation of the Metropolis–Hastings kernel.** On a measurable set `B`, the kernel is
the accepted moves into `B` plus the
rejection probability if `u ∈ B`. -/
theorem mhKernel_apply (Q : Kernel U U) [IsMarkovKernel Q] {Φ : U → ℝ} (hΦ : Measurable Φ)
    (u : U) {B : Set U} (hB : MeasurableSet B) :
    mhKernel Q Φ hΦ u B = ∫⁻ v in B, mhAcceptPotential Φ u v ∂Q u +
      B.indicator (fun u ↦ ∫⁻ w, (1 - mhAcceptPotential Φ u w) ∂Q u) u := by
  rw [mhKernel, add_apply, Measure.add_apply,
    Kernel.withDensity_apply _ (measurable_mhAcceptPotential hΦ),
    Kernel.withDensity_apply _ (show Measurable (Function.uncurry
      fun u (_ : U) ↦ ∫⁻ w, (1 - mhAcceptPotential Φ u w) ∂Q u) from
        (measurable_rejection Q hΦ).comp measurable_fst),
    withDensity_apply _ hB, withDensity_apply _ hB, Kernel.deterministic_apply]
  congr 1
  by_cases hu : u ∈ B
  · simp [Measure.dirac_apply' _ hB, hu]
  · simp [Measure.dirac_apply' _ hB, hu]

/-- **The Metropolis–Hastings kernel is a Markov kernel**: accepted and rejected mass add to
one because `a ≤ 1`. -/
theorem isMarkovKernel_mhKernel (Q : Kernel U U) [IsMarkovKernel Q] {Φ : U → ℝ}
    (hΦ : Measurable Φ) : IsMarkovKernel (mhKernel Q Φ hΦ) := by
  refine ⟨fun u ↦ ⟨?_⟩⟩
  rw [mhKernel_apply Q hΦ u MeasurableSet.univ, Measure.restrict_univ,
    Set.indicator_of_mem (Set.mem_univ u), ← lintegral_add_left]
  · simp_rw [add_tsub_cancel_of_le (mhAcceptPotential_le_one Φ u _)]
    simp
  · exact (measurable_mhAcceptPotential hΦ).comp measurable_prodMk_left

/-- **Metropolis–Hastings with a prior-reversible proposal is reversible for the posterior.**
If `Q` is reversible with respect to the prior probability measure `μ₀` and `Φ` is measurable,
then `mhKernel Q Φ` satisfies detailed balance with respect to `posterior μ₀ Φ`, the measure
with density `exp(-Φ)/Z` against `μ₀` (Dashti and Stuart, arXiv:1302.6989v4, Theorem 5.8). The
proof is theirs: `exp(-Φ(u)) a(u, v) = min{exp(-Φ(u)), exp(-Φ(v))}` is symmetric. -/
theorem isReversible_mhKernel (μ₀ : Measure U) [IsProbabilityMeasure μ₀] (Q : Kernel U U)
    [IsMarkovKernel Q] (hQ : Q.IsReversible μ₀) {Φ : U → ℝ} (hΦ : Measurable Φ) :
    (mhKernel Q Φ hΦ).IsReversible (posterior μ₀ Φ) := by
  set Z := normalizer μ₀ Φ
  set g : U → ℝ≥0∞ := fun u ↦ ENNReal.ofReal (Real.exp (-Φ u) / Z)
  have hg : Measurable g := by fun_prop
  set r : U → ℝ≥0∞ := fun u ↦ ∫⁻ w, (1 - mhAcceptPotential Φ u w) ∂Q u
  have hr : Measurable r := measurable_rejection Q hΦ
  set m : U → U → ℝ≥0∞ := fun u v ↦
    ENNReal.ofReal (min (Real.exp (-Φ u)) (Real.exp (-Φ v)) / Z)
  have hm : Measurable (Function.uncurry m) := by
    refine Measurable.ennreal_ofReal (Measurable.div_const ?_ _)
    exact (hΦ.comp measurable_fst).neg.exp.min (hΦ.comp measurable_snd).neg.exp
  have hgm : ∀ u v, g u * mhAcceptPotential Φ u v = m u v := by
    intro u v
    simp only [g, m, mhAcceptPotential]
    rw [← ENNReal.ofReal_mul' (le_min zero_le_one (Real.exp_pos _).le)]
    congr 1
    rw [div_mul_eq_mul_div, mul_min_of_nonneg _ _ (Real.exp_pos _).le, mul_one,
      ← Real.exp_add, show -Φ u + (Φ u - Φ v) = -Φ v by ring]
  have hflow : ∀ {A B : Set U}, MeasurableSet A → MeasurableSet B →
      ∫⁻ x in A, mhKernel Q Φ hΦ x B ∂posterior μ₀ Φ =
        ∫⁻ x in A, ∫⁻ v in B, m x v ∂Q x ∂μ₀ + ∫⁻ x in B ∩ A, g x * r x ∂μ₀ := by
    intro A B hA hB
    rw [posterior, setLIntegral_withDensity_eq_setLIntegral_mul μ₀ hg
      (Kernel.measurable_coe _ hB) hA]
    rw [← Measure.restrict_restrict hB, ← lintegral_indicator hB, ← lintegral_add_left']
    · refine lintegral_congr fun x ↦ ?_
      rw [Pi.mul_apply, mhKernel_apply Q hΦ x hB, mul_add,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      · exact lintegral_congr fun v ↦ hgm x v
      · by_cases hx : x ∈ B <;> simp [Set.indicator, hx, g, r]
    · exact (Measurable.setLIntegral_kernel_prod_right hm hB).aemeasurable
  intro A B hA hB
  rw [hflow hA hB, hflow hB hA, Set.inter_comm,
    setLIntegral_setLIntegral_symm μ₀ Q hQ hm (fun u v ↦ by simp only [m, min_comm]) hA hB]

/-- **The posterior is invariant for Metropolis–Hastings with a prior-reversible proposal**
(Dashti and Stuart, arXiv:1302.6989v4, Theorem 5.8 with Lemma 5.2). -/
theorem invariant_mhKernel (μ₀ : Measure U) [IsProbabilityMeasure μ₀] (Q : Kernel U U)
    [IsMarkovKernel Q] (hQ : Q.IsReversible μ₀) {Φ : U → ℝ} (hΦ : Measurable Φ) :
    (mhKernel Q Φ hΦ).Invariant (posterior μ₀ Φ) :=
  haveI := isMarkovKernel_mhKernel Q hΦ
  (isReversible_mhKernel μ₀ Q hQ hΦ).invariant

/-- **The pCN method is reversible for the posterior.** For a centred Gaussian prior `μ₀` on a
separable Banach space, `-1 ≤ β ≤ 1` and a measurable potential `Φ`, Metropolis–Hastings with
the pCN proposal and acceptance probability `min{1, exp(Φ(u) - Φ(v))}` satisfies detailed
balance with respect to the posterior `dμ/dμ₀ ∝ exp(-Φ)` (Dashti and Stuart,
arXiv:1302.6989v4, Algorithm 5.10, from Example 5.3 and Theorem 5.8). -/
theorem isReversible_pcn_mhKernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [SecondCountableTopology E]
    (μ₀ : Measure E) [IsGaussian μ₀] (hμ₀ : μ₀[id] = 0) {β : ℝ} (hβ₁ : -1 ≤ β) (hβ₂ : β ≤ 1)
    {Φ : E → ℝ} (hΦ : Measurable Φ) :
    (mhKernel (pcnKernel μ₀ β) Φ hΦ).IsReversible (posterior μ₀ Φ) :=
  isReversible_mhKernel μ₀ _ (isReversible_pcnKernel μ₀ hμ₀ hβ₁ hβ₂) hΦ

end MathlibExt.Probability.BayesianInverse
