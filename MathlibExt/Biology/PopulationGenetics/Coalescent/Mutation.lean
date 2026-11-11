/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.Tajima
public import MathlibExt.Probability.Distributions.PoissonKernel
public import Mathlib.Probability.HasCondDistrib
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.CDF

/-!
# Poisson mutation marking on a Kingman genealogy

Infinite-sites mutation on a genealogy: given the genealogy, each branch receives an independent
Poisson number of mutation events with mean `rate × branch length`, and every event creates a new
segregating site. The number of segregating sites `S` is the total number of events.

The existing Watterson and Tajima results (`KingmanTimes.watterson_unbiased`,
`KingmanTimes.variance_segSites`, `integral_tajimaVarEstimator`) take the conditional moments
`E[S | genealogy] = (θ/2) L` and `Var[S | genealogy] = (θ/2) L` as hypotheses. This file derives
them from the mutation model, with the repository's convention (`Kingman.lean`): time in units of
`2N` generations, `θ = 4Nu`, mutations at rate `θ / 2` per lineage.

* **Conditionally Poisson counts.** If `N` has conditional law `Po(ρ(X))` given `X`
  (`HasCondDistrib N X (poissonMeasureKernel.comap ρ _) μ`), then `E[N | X] = ρ(X)` and
  `Var[N | X] = ρ(X)` (`condExp_natCast_of_hasCondDistrib_poisson`,
  `condVar_natCast_of_hasCondDistrib_poisson`).
* **Per-branch marking.** If the vector of branch counts has conditional law
  `∏_b Po(r ℓ_b(X))` (`branchMutationKernel`), the total has conditional law `Po(r ∑_b ℓ_b(X))`
  (`hasCondDistrib_sum_of_branchMutation`, by finite Poisson additivity).
* **Kingman genealogy.** The Kingman genealogy has `k` branches of length `T k` during the epoch
  with `k` lineages (`KingmanBranch`, `kingmanBranchLength`); their lengths sum to the total
  branch length `L` (`sum_kingmanBranchLength`). With mutation rate `θ / 2` per lineage
  (`kingmanMutationKernel`), `E[S | genealogy] = Var[S | genealogy] = (θ/2) L` a.e.
  (`KingmanTimes.condExp_segSites_of_mutation`, `KingmanTimes.condVar_segSites_of_mutation`),
  hence Watterson's estimator is unbiased, `Var S = θ a₁ + θ² a₂`, and Tajima's variance
  estimator is unbiased, with no moment hypotheses left
  (`KingmanTimes.watterson_unbiased_of_mutation`, `KingmanTimes.variance_segSites_of_mutation`,
  `KingmanTimes.integral_tajimaVarEstimator_of_mutation`).
* **A concrete model.** `kingmanMutationMeasure n θ` (holding times from `piMeasure n`, then
  per-branch Poisson counts) satisfies all of the above (`hasCondDistrib_kingmanMutationMeasure`,
  `watterson_unbiased_kingmanMutationMeasure`), so the hypotheses are not vacuous.

Only the segregating-site count `S` is treated. The mean pairwise difference `π` depends on which
sample copies descend from each branch (the tree topology), which `KingmanTimes` does not record,
so the pairwise hypotheses of `integral_meanPairDiff` are not discharged here.

## References

* G. A. Watterson, *On the number of segregating sites in genetical models without
  recombination*, Theor. Popul. Biol. 7 (1975), 256–276.
* F. Tajima, *Statistical method for testing the neutral mutation hypothesis by DNA
  polymorphism*, Genetics 123 (1989), 585–595.
* J. Wakeley, *Coalescent Theory: An Introduction* (2009), ch. 3–4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent

/-! ### Conditionally Poisson counts -/

section CondPoisson

variable {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {X : Ω → 𝓧} {N : Ω → ℕ} {ρ : 𝓧 → ℝ≥0} {hρ : Measurable ρ}

/-- A function of a conditionally Poisson count is integrable when its conditional absolute
moment `G (ρ (X ω))` is. -/
private lemma integrable_comp_of_hasCondDistrib_poisson
    (h : HasCondDistrib N X (poissonMeasureKernel.comap ρ hρ) μ) {f : ℕ → ℝ} {G : ℝ≥0 → ℝ}
    (hf : ∀ r, Integrable f (poissonMeasure r)) (hfG : ∀ r, ∫ n, ‖f n‖ ∂poissonMeasure r = G r)
    (hG : Measurable G) (hGi : Integrable (fun ω => G (ρ (X ω))) μ) :
    Integrable (fun ω => f (N ω)) μ := by
  have hfm : Measurable f := measurable_of_countable f
  have hjoint : Integrable (fun p : 𝓧 × ℕ => f p.2)
      (μ.map X ⊗ₘ poissonMeasureKernel.comap ρ hρ) := by
    refine (Measure.integrable_compProd_iff (f := fun p : 𝓧 × ℕ => f p.2)
      (hfm.comp measurable_snd).aestronglyMeasurable).2 ⟨ae_of_all _ fun x => hf (ρ x), ?_⟩
    simp only [Kernel.comap_apply, poissonMeasureKernel_apply, hfG]
    exact (integrable_map_measure (hG.comp hρ).aestronglyMeasurable
      h.aemeasurable_fst).2 hGi
  rw [← h.map_eq] at hjoint
  exact (integrable_map_measure (hfm.comp measurable_snd).aestronglyMeasurable
    h.aemeasurable).1 hjoint

/-- The conditional expectation of a function of a conditionally Poisson count is its Poisson
expectation at the conditional mean. -/
private lemma condExp_comp_of_hasCondDistrib_poisson (hX : Measurable X)
    (h : HasCondDistrib N X (poissonMeasureKernel.comap ρ hρ) μ) {f : ℕ → ℝ}
    (hfi : Integrable (fun ω => f (N ω)) μ) :
    μ[fun ω => f (N ω) | m𝓧.comap X] =ᵐ[μ] fun ω => ∫ n, f n ∂poissonMeasure (ρ (X ω)) := by
  have h1 := condExp_ae_eq_integral_condDistrib hX h.aemeasurable_snd
    (measurable_of_countable f).stronglyMeasurable hfi
  have h2 := ae_of_ae_map hX.aemeasurable
    (condDistrib_ae_eq_of_measure_eq_compProd hX.aemeasurable h.aemeasurable_snd h.map_eq)
  filter_upwards [h1, h2] with ω h1 h2
  rw [h1, h2, Kernel.comap_apply, poissonMeasureKernel_apply]

/-- A conditionally Poisson count with integrable conditional mean is integrable. -/
theorem integrable_natCast_of_hasCondDistrib_poisson
    (h : HasCondDistrib N X (poissonMeasureKernel.comap ρ hρ) μ)
    (hρi : Integrable (fun ω => (ρ (X ω) : ℝ)) μ) :
    Integrable (fun ω => (N ω : ℝ)) μ :=
  integrable_comp_of_hasCondDistrib_poisson h (G := fun r => (r : ℝ))
    integrable_natCast_poissonMeasure
    (fun r => by simpa using integral_natCast_poissonMeasure r) (by fun_prop) hρi

/-- **Conditional mean of a conditionally Poisson count**: if `N ~ Po(ρ(X))` given `X`, then
`E[N | X] = ρ(X)` a.e. -/
theorem condExp_natCast_of_hasCondDistrib_poisson (hX : Measurable X)
    (h : HasCondDistrib N X (poissonMeasureKernel.comap ρ hρ) μ)
    (hρi : Integrable (fun ω => (ρ (X ω) : ℝ)) μ) :
    μ[fun ω => (N ω : ℝ) | m𝓧.comap X] =ᵐ[μ] fun ω => (ρ (X ω) : ℝ) := by
  filter_upwards [condExp_comp_of_hasCondDistrib_poisson hX h
    (integrable_natCast_of_hasCondDistrib_poisson h hρi)] with ω hω
  rw [hω, integral_natCast_poissonMeasure]

/-- A conditionally Poisson count whose conditional mean is square integrable is square
integrable. -/
theorem memLp_two_natCast_of_hasCondDistrib_poisson
    (h : HasCondDistrib N X (poissonMeasureKernel.comap ρ hρ) μ)
    (hρ2 : MemLp (fun ω => (ρ (X ω) : ℝ)) 2 μ) :
    MemLp (fun ω => (N ω : ℝ)) 2 μ := by
  have hm : AEStronglyMeasurable (fun ω => (N ω : ℝ)) μ :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).aestronglyMeasurable.comp_aemeasurable
      h.aemeasurable_snd
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  exact integrable_comp_of_hasCondDistrib_poisson h (f := fun n : ℕ => (n : ℝ) ^ 2)
    (G := fun r => (r : ℝ) + (r : ℝ) ^ 2) integrable_natCast_sq_poissonMeasure
    (fun r => by simpa using integral_natCast_sq_poissonMeasure r) (by fun_prop)
    ((hρ2.integrable one_le_two).add hρ2.integrable_sq)

/-- **Conditional variance of a conditionally Poisson count**: if `N ~ Po(ρ(X))` given `X`, then
`Var[N | X] = ρ(X)` a.e. -/
theorem condVar_natCast_of_hasCondDistrib_poisson (hX : Measurable X)
    (h : HasCondDistrib N X (poissonMeasureKernel.comap ρ hρ) μ)
    (hρ2 : MemLp (fun ω => (ρ (X ω) : ℝ)) 2 μ) :
    Var[fun ω => (N ω : ℝ); μ | m𝓧.comap X] =ᵐ[μ] fun ω => (ρ (X ω) : ℝ) := by
  have hN2 := memLp_two_natCast_of_hasCondDistrib_poisson h hρ2
  have hsq := condExp_comp_of_hasCondDistrib_poisson hX h (f := fun n : ℕ => (n : ℝ) ^ 2)
    hN2.integrable_sq
  filter_upwards [condVar_ae_eq_condExp_sq_sub_sq_condExp hX.comap_le hN2, hsq,
    condExp_natCast_of_hasCondDistrib_poisson hX h (hρ2.integrable one_le_two)]
    with ω hvar hsq hmean
  rw [hvar, Pi.sub_apply, Pi.pow_apply, hmean]
  change μ[fun ω => (N ω : ℝ) ^ 2 | m𝓧.comap X] ω - _ = _
  rw [hsq, integral_natCast_sq_poissonMeasure]
  ring

end CondPoisson

/-! ### Per-branch Poisson marking -/

section Branch

variable {Ω 𝓧 ι : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} [Fintype ι]
  {μ : Measure Ω}

/-- **Infinite-sites mutation on a finite genealogy**: given the genealogy `x`, branch `b` of
length `ℓ x b` carries an independent `Po(r * ℓ x b)` number of mutation events, where `r` is the
mutation rate per lineage per unit time. -/
def branchMutationKernel (r : ℝ≥0) (ℓ : 𝓧 → ι → ℝ≥0) (hℓ : Measurable ℓ) : Kernel 𝓧 (ι → ℕ) :=
  (piPoissonKernel ι).comap (fun x b => r * ℓ x b) (by fun_prop)

instance (r : ℝ≥0) (ℓ : 𝓧 → ι → ℝ≥0) (hℓ : Measurable ℓ) :
    IsMarkovKernel (branchMutationKernel r ℓ hℓ) := by
  unfold branchMutationKernel
  infer_instance

/-- The number of segregating sites under infinite-sites mutation: every mutation event falls at
a new site, so `S` is the total number of events over all branches. -/
def segSites (N : Ω → ι → ℕ) (ω : Ω) : ℝ := ((∑ b, N ω b : ℕ) : ℝ)

/-- **Conditional law of the number of segregating sites**: if the branch counts are independent
Poisson with means `r ℓ_b(X)` given `X`, then their total is `Po(r ∑_b ℓ_b(X))` given `X`. -/
theorem hasCondDistrib_sum_of_branchMutation {X : Ω → 𝓧} {N : Ω → ι → ℕ} {r : ℝ≥0}
    {ℓ : 𝓧 → ι → ℝ≥0} {hℓ : Measurable ℓ} [SFinite μ]
    (h : HasCondDistrib N X (branchMutationKernel r ℓ hℓ) μ) :
    HasCondDistrib (fun ω => ∑ b, N ω b) X
      (poissonMeasureKernel.comap (fun x => r * ∑ b, ℓ x b)
        (measurable_const.mul (Finset.measurable_sum _ fun _ _ => hℓ.eval))) μ := by
  have hk : (branchMutationKernel r ℓ hℓ).map (fun N : ι → ℕ => ∑ b, N b) =
      poissonMeasureKernel.comap (fun x => r * ∑ b, ℓ x b)
        (measurable_const.mul (Finset.measurable_sum _ fun _ _ => hℓ.eval)) := by
    ext1 x
    rw [Kernel.map_apply _ (by fun_prop), branchMutationKernel, Kernel.comap_apply,
      piPoissonKernel_apply, map_sum_pi_poissonMeasure, Kernel.comap_apply,
      poissonMeasureKernel_apply, Finset.mul_sum]
  have h' := h.comp_left (f := fun N : ι → ℕ => ∑ b, N b) (by fun_prop)
  rw [hk] at h'
  exact h'

end Branch

/-! ### The Kingman genealogy -/

/-- The branches of a Kingman genealogy of `n` gene copies, epoch by epoch: during the epoch with
`k` lineages (`2 ≤ k ≤ n`) there are `k` branches. -/
abbrev KingmanBranch (n : ℕ) : Type := Σ k : Icc 2 n, Fin k

/-- The branch lengths of a Kingman genealogy with epoch lengths `t`: each of the `k` branches of
epoch `k` has length `t k` (truncated at `0`, which is a.s. irrelevant for exponential holding
times). -/
def kingmanBranchLength (n : ℕ) (t : Icc 2 n → ℝ) (b : KingmanBranch n) : ℝ≥0 :=
  (t b.1).toNNReal

/-- The branch lengths depend measurably on the epoch lengths. -/
theorem measurable_kingmanBranchLength (n : ℕ) : Measurable (kingmanBranchLength n) := by
  unfold kingmanBranchLength
  fun_prop

/-- The branch lengths of epoch `k` sum to `k * t k`. -/
theorem sum_kingmanBranchLength (n : ℕ) (t : Icc 2 n → ℝ) :
    ∑ b, kingmanBranchLength n t b = ∑ k : Icc 2 n, ((k : ℕ) : ℝ≥0) * (t k).toNNReal := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [kingmanBranchLength]

/-- Infinite-sites mutation on the Kingman genealogy at rate `θ / 2` per lineage per unit time
(`θ = 4Nu`, time in units of `2N` generations). -/
def kingmanMutationKernel (n : ℕ) (θ : ℝ≥0) : Kernel (Icc 2 n → ℝ) (KingmanBranch n → ℕ) :=
  branchMutationKernel (θ / 2) (kingmanBranchLength n) (measurable_kingmanBranchLength n)

instance (n : ℕ) (θ : ℝ≥0) : IsMarkovKernel (kingmanMutationKernel n θ) := by
  unfold kingmanMutationKernel
  infer_instance

/-- An exponentially distributed random variable is a.s. nonnegative. -/
private lemma ae_nonneg_of_hasLaw_expMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {Y : Ω → ℝ} {r : ℝ} (hr : 0 < r) (hY : HasLaw Y (expMeasure r) μ) :
    ∀ᵐ ω ∂μ, 0 ≤ Y ω := by
  have := isProbabilityMeasure_expMeasure hr
  have h : ∀ᵐ x ∂expMeasure r, 0 ≤ x := by
    rw [ae_iff]
    refine measure_mono_null (fun x (hx : ¬0 ≤ x) => Set.mem_Iic.2 (not_le.1 hx).le) ?_
    rw [← ofReal_cdf, cdf_expMeasure_eq hr]
    simp
  rw [← hY.map_eq] at h
  exact ae_of_ae_map hY.aemeasurable h

namespace KingmanTimes

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : ℕ} (K : KingmanTimes μ n)

/-- The vector of epoch lengths `(T 2, …, T n)` of a Kingman genealogy. -/
def epochs (ω : Ω) (k : Icc 2 n) : ℝ := K.T k ω

/-- The total branch length in terms of the branch lengths: `∑_b ℓ_b = L` a.s. -/
theorem sum_kingmanBranchLength_epochs :
    ∀ᵐ ω ∂μ, ((∑ b, kingmanBranchLength n (K.epochs ω) b : ℝ≥0) : ℝ) = K.totalLength ω := by
  have hnn : ∀ᵐ ω ∂μ, ∀ k : Icc 2 n, 0 ≤ K.T k ω :=
    ae_all_iff.2 fun k => ae_nonneg_of_hasLaw_expMeasure (choose_two_pos k.2) (K.hasLaw k k.2)
  filter_upwards [hnn] with ω hω
  rw [sum_kingmanBranchLength, totalLength, ← Finset.sum_coe_sort (Icc 2 n)]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [epochs, Real.coe_toNNReal _ (hω k)]

/-- The epoch lengths are square integrable, hence so is the total branch length. -/
private theorem memLp_totalLength : MemLp K.totalLength 2 μ := by
  have hT : ∀ k ∈ Icc 2 n, MemLp (fun ω => (k : ℝ) * K.T k ω) 2 μ := fun k hk =>
    ((K.hasLaw k hk).memLp_comp (f := id)
      ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
        (by simpa using integrable_pow_expMeasure (choose_two_pos hk) 2))).const_mul _
  have hL : K.totalLength = ∑ k ∈ Icc 2 n, fun ω => (k : ℝ) * K.T k ω := by
    funext ω
    simp [totalLength, Finset.sum_apply]
  rw [hL]
  exact memLp_finsetSum' _ hT

variable {θ : ℝ≥0} {N : Ω → KingmanBranch n → ℕ}

/-- **The number of segregating sites is conditionally Poisson**: under infinite-sites mutation
at rate `θ / 2` per lineage, `S ~ Po((θ/2) ∑_b ℓ_b)` given the genealogy. -/
theorem hasCondDistrib_segSites_of_mutation [SFinite μ]
    (hN : HasCondDistrib N K.epochs (kingmanMutationKernel n θ) μ) :
    HasCondDistrib (fun ω => ∑ b, N ω b) K.epochs
      (poissonMeasureKernel.comap (fun t => θ / 2 * ∑ b, kingmanBranchLength n t b)
        (measurable_const.mul (Finset.measurable_sum _ fun _ _ =>
          (measurable_kingmanBranchLength n).eval))) μ :=
  hasCondDistrib_sum_of_branchMutation hN

/-- The conditional Poisson mean `(θ/2) ∑_b ℓ_b` is `(θ/2) L` a.s. -/
private theorem mean_ae_eq (θ : ℝ≥0) :
    (fun ω => ((θ / 2 * ∑ b, kingmanBranchLength n (K.epochs ω) b : ℝ≥0) : ℝ)) =ᵐ[μ]
      fun ω => (θ : ℝ) / 2 * K.totalLength ω := by
  filter_upwards [K.sum_kingmanBranchLength_epochs] with ω h
  rw [NNReal.coe_mul, h, NNReal.coe_div, NNReal.coe_two]

/-- **Conditional mean of the number of segregating sites**: `E[S | genealogy] = (θ/2) L` a.s.
This discharges the hypothesis `hS` of `watterson_unbiased`. -/
theorem condExp_segSites_of_mutation [IsProbabilityMeasure μ] (hK : Measurable K.epochs)
    (hN : HasCondDistrib N K.epochs (kingmanMutationKernel n θ) μ) :
    μ[segSites N | MeasurableSpace.comap K.epochs inferInstance] =ᵐ[μ]
      fun ω => (θ : ℝ) / 2 * K.totalLength ω := by
  have hint := (K.integrable_totalLength.const_mul ((θ : ℝ) / 2)).congr (K.mean_ae_eq θ).symm
  filter_upwards [condExp_natCast_of_hasCondDistrib_poisson hK
    (K.hasCondDistrib_segSites_of_mutation hN) hint, K.mean_ae_eq θ] with ω h1 h2
  rw [show segSites N = fun ω => ((∑ b, N ω b : ℕ) : ℝ) from rfl, h1, h2]

/-- Under Poisson mutation marking, the number of segregating sites is square integrable. -/
theorem memLp_segSites_of_mutation [IsProbabilityMeasure μ]
    (hN : HasCondDistrib N K.epochs (kingmanMutationKernel n θ) μ) :
    MemLp (segSites N) 2 μ :=
  memLp_two_natCast_of_hasCondDistrib_poisson (K.hasCondDistrib_segSites_of_mutation hN)
    ((K.memLp_totalLength.const_mul ((θ : ℝ) / 2)).ae_eq (K.mean_ae_eq θ).symm)

/-- **Conditional variance of the number of segregating sites**:
`Var[S | genealogy] = (θ/2) L` a.s. -/
theorem condVar_segSites_of_mutation [IsProbabilityMeasure μ] (hK : Measurable K.epochs)
    (hN : HasCondDistrib N K.epochs (kingmanMutationKernel n θ) μ) :
    Var[segSites N; μ | MeasurableSpace.comap K.epochs inferInstance] =ᵐ[μ]
      fun ω => (θ : ℝ) / 2 * K.totalLength ω := by
  have h2 := (K.memLp_totalLength.const_mul ((θ : ℝ) / 2)).ae_eq (K.mean_ae_eq θ).symm
  filter_upwards [condVar_natCast_of_hasCondDistrib_poisson hK
    (K.hasCondDistrib_segSites_of_mutation hN) h2, K.mean_ae_eq θ] with ω h1 h2
  rw [show segSites N = fun ω => ((∑ b, N ω b : ℕ) : ℝ) from rfl, h1, h2]

/-- **Watterson's estimator is unbiased under Poisson mutation marking** (Watterson 1975):
`E[S / H_{n-1}] = θ` for `n ≥ 2`, with `S` the number of infinite-sites mutation events on the
Kingman genealogy at rate `θ / 2` per lineage. -/
theorem watterson_unbiased_of_mutation [IsProbabilityMeasure μ] (hK : Measurable K.epochs)
    (hN : HasCondDistrib N K.epochs (kingmanMutationKernel n θ) μ) (hn : 2 ≤ n) :
    μ[fun ω => segSites N ω / (harmonic (n - 1) : ℝ)] = (θ : ℝ) :=
  K.watterson_unbiased hK.comap_le ((K.memLp_segSites_of_mutation hN).integrable one_le_two)
    (K.condExp_segSites_of_mutation hK hN) hn

/-- **Variance of the number of segregating sites under Poisson mutation marking** (Watterson
1975): `Var S = θ a₁ + θ² a₂`. -/
theorem variance_segSites_of_mutation [IsProbabilityMeasure μ] (hK : Measurable K.epochs)
    (hN : HasCondDistrib N K.epochs (kingmanMutationKernel n θ) μ) :
    Var[segSites N; μ] = (θ : ℝ) * tajimaA1 n + (θ : ℝ) ^ 2 * tajimaA2 n :=
  K.variance_segSites hK.comap_le (K.memLp_segSites_of_mutation hN)
    (K.condExp_segSites_of_mutation hK hN) (K.condVar_segSites_of_mutation hK hN)

/-- **Tajima's variance estimator is unbiased under Poisson mutation marking** (Tajima 1989):
`E[e₁ S + e₂ S (S - 1)] = c₁ θ + c₂ θ²` for `n ≥ 2`. -/
theorem integral_tajimaVarEstimator_of_mutation [IsProbabilityMeasure μ]
    (hK : Measurable K.epochs) (hN : HasCondDistrib N K.epochs (kingmanMutationKernel n θ) μ)
    (hn : 2 ≤ n) :
    μ[fun ω => tajimaE1 n * segSites N ω + tajimaE2 n * (segSites N ω * (segSites N ω - 1))] =
      tajimaC1 n * (θ : ℝ) + tajimaC2 n * (θ : ℝ) ^ 2 :=
  integral_tajimaVarEstimator K hK.comap_le hn (K.memLp_segSites_of_mutation hN)
    (K.condExp_segSites_of_mutation hK hN) (K.condVar_segSites_of_mutation hK hN)

end KingmanTimes

/-! ### A concrete marked Kingman model -/

/-- Independence is preserved by precomposition with a measure-preserving map. -/
theorem iIndepFun_comp_of_measurePreserving {ι Ω Ω' : Type*} [Finite ι]
    {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {β : ι → Type*}
    {mβ : ∀ i, MeasurableSpace (β i)} {μ : Measure Ω} {P : Measure Ω'} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] {g : Ω' → Ω} (hg : MeasurePreserving g P μ) {f : ∀ i, Ω → β i}
    (hf : ∀ i, Measurable (f i)) (h : iIndepFun f μ) :
    iIndepFun (fun i => f i ∘ g) P := by
  have := Fintype.ofFinite ι
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (hf i).aemeasurable)] at h
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => ((hf i).comp hg.measurable).aemeasurable)]
  have h1 : P.map (fun ω' i => (f i ∘ g) ω') = μ.map (fun ω i => f i ω) := by
    rw [← hg.map_eq, Measure.map_map (measurable_pi_iff.2 hf) hg.measurable]
    rfl
  have h2 : ∀ i, P.map (f i ∘ g) = μ.map (f i) := fun i => by
    rw [← hg.map_eq, Measure.map_map (hf i) hg.measurable]
  simp only [h1, h2, h]

/-- The first marginal of `μ ⊗ₘ κ` is `μ` for a Markov kernel `κ`. -/
theorem measurePreserving_fst_compProd {α β : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsMarkovKernel κ] :
    MeasurePreserving Prod.fst (μ ⊗ₘ κ) μ :=
  ⟨measurable_fst, Measure.fst_compProd μ κ⟩

/-- The marked Kingman model for a sample of size `n`: independent exponential holding times
(`piMeasure n`), then, given them, independent `Po((θ/2) ℓ_b)` mutation counts on the branches. -/
def kingmanMutationMeasure (n : ℕ) (θ : ℝ≥0) :
    Measure ((Icc 2 n → ℝ) × (KingmanBranch n → ℕ)) :=
  piMeasure n ⊗ₘ kingmanMutationKernel n θ

instance (n : ℕ) (θ : ℝ≥0) : IsProbabilityMeasure (kingmanMutationMeasure n θ) := by
  unfold kingmanMutationMeasure
  infer_instance

/-- The holding times of the marked Kingman model form a Kingman coalescent. -/
def KingmanTimes.ofMutationModel (n : ℕ) (θ : ℝ≥0) :
    KingmanTimes (kingmanMutationMeasure n θ) n where
  T k p := (KingmanTimes.ofPi n).T k p.1
  hasLaw k hk := ((KingmanTimes.ofPi n).hasLaw k hk).comp
    (measurePreserving_fst_compProd _ _).hasLaw
  indep := iIndepFun_comp_of_measurePreserving (measurePreserving_fst_compProd _ _)
    (fun k => by
      simp only [KingmanTimes.ofPi, k.2, ↓reduceDIte]
      exact measurable_pi_apply _)
    (KingmanTimes.ofPi n).indep

/-- In the marked Kingman model the genealogy is the first coordinate. -/
theorem KingmanTimes.epochs_ofMutationModel (n : ℕ) (θ : ℝ≥0) :
    (KingmanTimes.ofMutationModel n θ).epochs = Prod.fst := by
  funext p k
  simp only [KingmanTimes.epochs, KingmanTimes.ofMutationModel, KingmanTimes.ofPi, k.2, ↓reduceDIte]

/-- In the marked Kingman model, the branch counts have conditional law
`kingmanMutationKernel n θ` given the genealogy. -/
theorem hasCondDistrib_kingmanMutationMeasure (n : ℕ) (θ : ℝ≥0) :
    HasCondDistrib Prod.snd (KingmanTimes.ofMutationModel n θ).epochs
      (kingmanMutationKernel n θ) (kingmanMutationMeasure n θ) := by
  rw [KingmanTimes.epochs_ofMutationModel]
  refine ⟨by fun_prop, ?_⟩
  rw [kingmanMutationMeasure, (measurePreserving_fst_compProd _ _).map_eq]
  simp only [Prod.mk.eta]
  exact Measure.map_id

/-- **Watterson's estimator is unbiased in the marked Kingman model**: `E[S / H_{n-1}] = θ` for
`n ≥ 2`, with no remaining hypotheses. -/
theorem watterson_unbiased_kingmanMutationMeasure {n : ℕ} (θ : ℝ≥0) (hn : 2 ≤ n) :
    ∫ p, segSites Prod.snd p / (harmonic (n - 1) : ℝ) ∂kingmanMutationMeasure n θ = θ :=
  (KingmanTimes.ofMutationModel n θ).watterson_unbiased_of_mutation
    (by rw [KingmanTimes.epochs_ofMutationModel]; exact measurable_fst)
    (hasCondDistrib_kingmanMutationMeasure n θ) hn

/-- **Variance of the number of segregating sites in the marked Kingman model**:
`Var S = θ a₁ + θ² a₂`, with no remaining hypotheses. -/
theorem variance_segSites_kingmanMutationMeasure (n : ℕ) (θ : ℝ≥0) :
    Var[segSites Prod.snd; kingmanMutationMeasure n θ] =
      (θ : ℝ) * tajimaA1 n + (θ : ℝ) ^ 2 * tajimaA2 n :=
  (KingmanTimes.ofMutationModel n θ).variance_segSites_of_mutation
    (by rw [KingmanTimes.epochs_ofMutationModel]; exact measurable_fst)
    (hasCondDistrib_kingmanMutationMeasure n θ)

end MathlibExt.Biology.PopulationGenetics.Coalescent
