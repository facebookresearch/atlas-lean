/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Variance

/-!
# BOLT-LMM: mean-field variational Bayes for the mixture prior on SNP effects

BOLT-LMM (Loh et al. 2015) fits the Bayesian linear model

  `y = X β + e`,  `e ~ N(0, σ_e² I)`,  `β_j` i.i.d. `~ π`,

on `n` individuals and `m` SNPs (`X : Matrix (Fin n) (Fin m) ℝ`), where the prior `π` is the
mixture `p N(0, σ₁²) + (1 - p) N(0, σ₂²)` (`mixturePrior`; `σ₂² = 0` is the spike-and-slab
prior), by mean-field variational Bayes: the posterior is approximated by a product
`q = ∏ⱼ qⱼ` of factors on `ℝ` chosen to maximize the evidence lower bound

  `ELBO(q) = 𝔼_q[log N(y; X β, σ_e² I)] - ∑ⱼ KL(qⱼ ‖ π)`.

Here a factor is *admissible* (`IsAdmissible`) if it is a probability measure with a finite
second moment and finite KL divergence from the prior. The expected log-likelihood of a product
of such factors depends on them only through their means `μⱼ` and variances `vⱼ`
(`integral_rss_pi`):

  `𝔼_q ‖y - X β‖² = ‖y - X μ‖² + ∑ⱼ ‖xⱼ‖² vⱼ`,

which is how `elbo` is defined; the KL term is the sum of the factor divergences (equal to the
divergence of the product `∏ⱼ qⱼ` from the product prior by additivity of the KL divergence over
products, which is not formalized here).

**Coordinate ascent (CAVI).** As a function of one factor `qⱼ` (the others fixed), the ELBO is
`∫ fⱼ dqⱼ - KL(qⱼ ‖ π) + C` (`exists_elbo_update_eq`) for the potential
`fⱼ(b) = (b xⱼᵀ rⱼ - ‖xⱼ‖² b² / 2) / σ_e²`, where `rⱼ = y - ∑_{k ≠ j} xₖ μₖ` is the partial
residual of the other SNPs' posterior means (`potential`, `partialResidual`). So `fⱼ` is the part
of the expected log-likelihood `𝔼_{q_{-j}}[log p(y | β)]` that depends on `βⱼ`, and the CAVI
update is the tilted prior `qⱼ ∝ π · exp fⱼ`, i.e. `qⱼ ∝ exp 𝔼_{q_{-j}}[log p(y, β)]`
(`caviUpdate`). We prove:

* the update is admissible (`isAdmissible_caviUpdate`) and maximizes the ELBO over the factor,
  with the exact gap `ELBO(q) = ELBO(update) - KL(qⱼ ‖ update)` (`elbo_update_eq_sub`);
* coordinate ascent is monotone: `ELBO(q) ≤ ELBO(caviStep q j)` (`elbo_le_elbo_caviStep`), and
  along any update schedule the ELBO is nondecreasing (`monotone_elbo_caviRun`);
* stationary points: `q` cannot be improved by changing its `j`-th factor iff `qⱼ` is the
  expected-log-joint update (`isCoordMax_iff`).

These are statements about the variational objective only: we do not claim that the
variational posterior equals the true posterior (in general it does not), nor that the
iteration converges.

## Main results

* `mixturePrior`, `isProbabilityMeasure_mixturePrior`, `integrable_sq_mixturePrior`.
* `integral_rss_pi`: the expected residual sum of squares of a product of factors.
* `exists_elbo_update_eq`, `isAdmissible_caviUpdate`, `elbo_update_eq_sub`,
  `elbo_le_elbo_caviStep`, `monotone_elbo_caviRun`, `isCoordMax_iff`.

## References

* P.-R. Loh, G. Tucker, B. K. Bulik-Sullivan, B. J. Vilhjálmsson, H. K. Finucane, R. M. Salem,
  D. I. Chasman, P. M. Ridker, B. M. Neale, B. Berger, N. Patterson, A. L. Price, *Efficient
  Bayesian mixed-model analysis increases association power in large cohorts*, Nat. Genet. 47
  (2015), 284–290 (Supplementary Note: the variational Bayes iteration).
* D. M. Blei, A. Kucukelbir, J. D. McAuliffe, *Variational inference: a review for
  statisticians*, J. Amer. Statist. Assoc. 112 (2017), 859–877 (CAVI, Section 2.4).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace MathlibExt.Biology.StatisticalGenetics.BOLTLMMVariational

/-- The BOLT-LMM prior on a SNP effect: the mixture `p N(0, v₁) + (1 - p) N(0, v₂)` of two
centered Gaussians with variances `v₁, v₂` (`v₂ = 0` gives the spike-and-slab prior with a point
mass at `0`). -/
noncomputable def mixturePrior (p v₁ v₂ : ℝ≥0) : Measure ℝ :=
  (p : ℝ≥0∞) • gaussianReal 0 v₁ + ((1 - p : ℝ≥0) : ℝ≥0∞) • gaussianReal 0 v₂

/-- The mixture prior is a probability measure for a mixing weight `p ≤ 1`. -/
theorem isProbabilityMeasure_mixturePrior {p : ℝ≥0} (hp : p ≤ 1) (v₁ v₂ : ℝ≥0) :
    IsProbabilityMeasure (mixturePrior p v₁ v₂) := by
  constructor
  simp only [mixturePrior, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.coe_add, add_tsub_cancel_of_le hp, ENNReal.coe_one]

/-- The mixture prior has a finite second moment. -/
theorem integrable_sq_mixturePrior (p v₁ v₂ : ℝ≥0) :
    Integrable (fun b : ℝ => b ^ 2) (mixturePrior p v₁ v₂) := by
  have h : ∀ v : ℝ≥0, Integrable (fun b : ℝ => b ^ 2) (gaussianReal 0 v) := fun v =>
    (memLp_id_gaussianReal 2).integrable_sq
  exact ((h v₁).smul_measure ENNReal.coe_ne_top).add_measure
    ((h v₂).smul_measure ENNReal.coe_ne_top)

/-- An admissible variational factor for the prior `π`: a probability measure with a finite
second moment and finite KL divergence from `π` (`q ≪ π` with integrable log-likelihood
ratio). -/
structure IsAdmissible (π q : Measure ℝ) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure q
  integrable_sq : Integrable (fun b : ℝ => b ^ 2) q
  absolutelyContinuous : q ≪ π
  integrable_llr : Integrable (llr q π) q

/-- The mean `∫ b dq` of a factor. -/
noncomputable def mean (q : Measure ℝ) : ℝ := ∫ b, b ∂q

/-- The squared norm `‖xⱼ‖² = ∑ᵢ X i j ²` of the genotype column of SNP `j`. -/
def colNormSq {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) : ℝ := ∑ i, X i j ^ 2

/-- The expected residual sum of squares `‖y - X μ‖² + ∑ⱼ ‖xⱼ‖² vⱼ` of the product of the
factors `q`, with means `μⱼ` and variances `vⱼ` (`integral_rss_pi`). -/
noncomputable def expectedRSS {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ)
    (q : Fin m → Measure ℝ) : ℝ :=
  ∑ i, (y i - ∑ j, X i j * mean (q j)) ^ 2 + ∑ j, colNormSq X j * variance id (q j)

/-- **The expected residual sum of squares of a product of factors**: for probability factors
with finite second moments, `𝔼_{∏ qⱼ} ‖y - X β‖² = ‖y - X μ‖² + ∑ⱼ ‖xⱼ‖² vⱼ`. -/
theorem integral_rss_pi {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ)
    (q : Fin m → Measure ℝ) [∀ j, IsProbabilityMeasure (q j)]
    (h2 : ∀ j, Integrable (fun b : ℝ => b ^ 2) (q j)) :
    ∫ β, ∑ i, (y i - ∑ j, X i j * β j) ^ 2 ∂(Measure.pi q) = expectedRSS X y q := by
  have hmem : ∀ j, MemLp (fun b : ℝ => b) 2 (q j) := fun j =>
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr (h2 j)
  have hterm : ∀ i j, MemLp (fun β : Fin m → ℝ => X i j * β j) 2 (Measure.pi q) := fun i j =>
    ((hmem j).comp_measurePreserving (measurePreserving_eval q j)).const_mul (X i j)
  have hS : ∀ i, MemLp (fun β : Fin m → ℝ => ∑ j, X i j * β j) 2 (Measure.pi q) := fun i =>
    memLp_finsetSum _ fun j _ => hterm i j
  have hmean : ∀ i, ∫ β, ∑ j, X i j * β j ∂(Measure.pi q) = ∑ j, X i j * mean (q j) := fun i => by
    rw [integral_finsetSum _ fun j _ => (hterm i j).integrable one_le_two]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul,
      integral_comp_eval (X := fun _ => ℝ) (μ := q) (i := j) (f := fun b : ℝ => b)
        aestronglyMeasurable_id]
    rfl
  have hvar : ∀ i, variance (fun β : Fin m → ℝ => ∑ j, X i j * β j) (Measure.pi q) =
      ∑ j, X i j ^ 2 * variance id (q j) := fun i => by
    have h := variance_sum_pi (μ := q) (X := fun j b => X i j * b)
      (fun j => (hmem j).const_mul (X i j))
    have hfun : (∑ j, fun ω : Fin m → ℝ => X i j * ω j) = fun β => ∑ j, X i j * β j := by
      ext β; simp [Finset.sum_apply]
    rw [hfun] at h
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [variance_const_mul]
    rfl
  have hi : ∀ i, ∫ β, (y i - ∑ j, X i j * β j) ^ 2 ∂(Measure.pi q) =
      (y i - ∑ j, X i j * mean (q j)) ^ 2 + ∑ j, X i j ^ 2 * variance id (q j) := fun i => by
    have hint := (hS i).integrable one_le_two
    have hint2 := (hS i).integrable_sq
    have e : (fun β : Fin m → ℝ => (y i - ∑ j, X i j * β j) ^ 2) =
        fun β => (y i ^ 2 - 2 * y i * ∑ j, X i j * β j) + (∑ j, X i j * β j) ^ 2 := by
      ext β; ring
    have hA : Integrable (fun β : Fin m → ℝ => y i ^ 2 - 2 * y i * ∑ j, X i j * β j)
        (Measure.pi q) := (integrable_const _).sub (hint.const_mul _)
    have hB : Integrable (fun β : Fin m → ℝ => 2 * y i * ∑ j, X i j * β j) (Measure.pi q) :=
      hint.const_mul _
    rw [e, integral_add hA hint2, integral_sub (integrable_const _) hB, integral_const,
      integral_const_mul,
      ← hvar i, variance_eq_sub (hS i), hmean i]
    simp only [probReal_univ, smul_eq_mul, one_mul, Pi.pow_apply]
    ring
  rw [integral_finsetSum _ fun i _ => ?_]
  · unfold expectedRSS
    rw [Finset.sum_congr rfl fun i _ => hi i, Finset.sum_add_distrib, Finset.sum_comm]
    simp only [colNormSq, Finset.sum_mul]
  · have e : (fun β : Fin m → ℝ => (y i - ∑ j, X i j * β j) ^ 2) =
        fun β => (y i ^ 2 - 2 * y i * ∑ j, X i j * β j) + (∑ j, X i j * β j) ^ 2 := by
      ext β; ring
    rw [e]
    have hA : Integrable (fun β : Fin m → ℝ => y i ^ 2 - 2 * y i * ∑ j, X i j * β j)
        (Measure.pi q) := (integrable_const _).sub (((hS i).integrable one_le_two).const_mul _)
    exact hA.add (hS i).integrable_sq

/-- The mean-field evidence lower bound
`-(n/2) log (2π σ_e²) - 𝔼_q ‖y - X β‖² / (2 σ_e²) - ∑ⱼ KL(qⱼ ‖ π)`, meaningful for `σ_e² > 0`.
It is the ELBO for admissible factors (finite KL); for an inadmissible factor `toReal` would turn
an infinite divergence into `0`, so all results assume admissibility. -/
noncomputable def elbo {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ) (σe2 : ℝ)
    (π : Measure ℝ) (q : Fin m → Measure ℝ) : ℝ :=
  -(n * Real.log (2 * Real.pi * σe2)) / 2 - expectedRSS X y q / (2 * σe2) -
    ∑ j, (klDiv (q j) π).toReal

/-- The partial residual `rⱼ = y - ∑_{k ≠ j} xₖ μₖ` of the other SNPs' posterior means. -/
noncomputable def partialResidual {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ)
    (q : Fin m → Measure ℝ) (j : Fin m) (i : Fin n) : ℝ :=
  y i - ∑ k ∈ Finset.univ.erase j, X i k * mean (q k)

/-- The CAVI potential `fⱼ(b) = (b xⱼᵀ rⱼ - ‖xⱼ‖² b² / 2) / σ_e²`: the part of the expected
log-likelihood `𝔼_{q_{-j}}[log p(y | β)]` that depends on `βⱼ = b`
(`exists_elbo_update_eq`). -/
noncomputable def potential {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ) (σe2 : ℝ)
    (q : Fin m → Measure ℝ) (j : Fin m) (b : ℝ) : ℝ :=
  (b * ∑ i, X i j * partialResidual X y q j i - colNormSq X j * b ^ 2 / 2) / σe2

/-- The CAVI update of factor `j`: the prior tilted by the potential,
`qⱼ ∝ π · exp fⱼ = exp 𝔼_{q_{-j}}[log p(y, β)]`. -/
noncomputable def caviUpdate {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ) (σe2 : ℝ)
    (π : Measure ℝ) (q : Fin m → Measure ℝ) (j : Fin m) : Measure ℝ :=
  π.tilted (potential X y σe2 q j)

/-- One coordinate-ascent step: replace factor `j` by its CAVI update. -/
noncomputable def caviStep {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ) (σe2 : ℝ)
    (π : Measure ℝ) (q : Fin m → Measure ℝ) (j : Fin m) : Fin m → Measure ℝ :=
  Function.update q j (caviUpdate X y σe2 π q j)

/-- Coordinate ascent along the update schedule `s`: at time `t` factor `s t` is updated. -/
noncomputable def caviRun {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ) (σe2 : ℝ)
    (π : Measure ℝ) (q : Fin m → Measure ℝ) (s : ℕ → Fin m) : ℕ → Fin m → Measure ℝ
  | 0 => q
  | t + 1 => caviStep X y σe2 π (caviRun X y σe2 π q s t) (s t)

/-! ### Proof-only lemmas -/

private lemma integrable_id_of_sq {ν : Measure ℝ} [IsFiniteMeasure ν]
    (h : Integrable (fun b : ℝ => b ^ 2) ν) : Integrable (fun b : ℝ => b) ν :=
  ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr h).integrable one_le_two

private lemma continuous_potential {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ)
    (σe2 : ℝ) (q : Fin m → Measure ℝ) (j : Fin m) : Continuous (potential X y σe2 q j) := by
  unfold potential
  fun_prop

private lemma integrable_potential {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ)
    (σe2 : ℝ) (q : Fin m → Measure ℝ) (j : Fin m) {ν : Measure ℝ} [IsFiniteMeasure ν]
    (h : Integrable (fun b : ℝ => b ^ 2) ν) : Integrable (potential X y σe2 q j) ν :=
  (((integrable_id_of_sq h).mul_const _).sub ((h.const_mul _).div_const 2)).div_const _

private lemma potential_le {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ) {σe2 : ℝ}
    (hσ : 0 < σe2) (q : Fin m → Measure ℝ) (j : Fin m) :
    ∃ C, ∀ b, potential X y σe2 q j b ≤ C := by
  set r := ∑ i, X i j * partialResidual X y q j i
  by_cases h0 : colNormSq X j = 0
  · have hX : ∀ i, X i j = 0 := fun i => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (X i j))).mp h0 i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp this
    refine ⟨0, fun b => ?_⟩
    simp [potential, h0, hX]
  · have hc : 0 < colNormSq X j :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg (X i j)) (Ne.symm h0)
    refine ⟨r ^ 2 / (2 * colNormSq X j) / σe2, fun b => div_le_div_of_nonneg_right ?_ hσ.le⟩
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (colNormSq X j * b - r)]

private lemma integrable_exp_potential {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ)
    (y : Fin n → ℝ) {σe2 : ℝ} (hσ : 0 < σe2) (q : Fin m → Measure ℝ) (j : Fin m)
    {ν : Measure ℝ} [IsFiniteMeasure ν] {g : ℝ → ℝ} (hg : Integrable g ν) :
    Integrable (fun b => Real.exp (potential X y σe2 q j b) * g b) ν := by
  obtain ⟨C, hC⟩ := potential_le X y hσ q j
  refine Integrable.mono' (hg.norm.const_mul (Real.exp C))
    (((continuous_potential X y σe2 q j).rexp.aestronglyMeasurable).mul hg.1)
    (Filter.Eventually.of_forall fun b => ?_)
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hC b)) (norm_nonneg _)

private lemma integrable_exp_potential' {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ)
    (y : Fin n → ℝ) {σe2 : ℝ} (hσ : 0 < σe2) (q : Fin m → Measure ℝ) (j : Fin m)
    {ν : Measure ℝ} [IsFiniteMeasure ν] :
    Integrable (fun b => Real.exp (potential X y σe2 q j b)) ν := by
  simpa using integrable_exp_potential X y hσ q j (integrable_const (1 : ℝ) : Integrable _ ν)

/-- **The ELBO as a function of one factor**: with the other factors fixed, the ELBO of
`q` with factor `j` replaced by an admissible `q'` is `∫ fⱼ dq' - KL(q' ‖ π) + C`. -/
theorem exists_elbo_update_eq {n m : ℕ} {X : Matrix (Fin n) (Fin m) ℝ} {y : Fin n → ℝ}
    {σe2 : ℝ} {π : Measure ℝ}
    (q : Fin m → Measure ℝ) (j : Fin m) :
    ∃ C : ℝ, ∀ q', IsAdmissible π q' →
      elbo X y σe2 π (Function.update q j q') =
        ∫ b, potential X y σe2 q j b ∂q' - (klDiv q' π).toReal + C := by
  set r := partialResidual X y q j
  set c := colNormSq X j
  refine ⟨-(n * Real.log (2 * Real.pi * σe2)) / 2 -
      (∑ i, r i ^ 2 + ∑ k ∈ Finset.univ.erase j, colNormSq X k * variance id (q k)) /
        (2 * σe2) - ∑ k ∈ Finset.univ.erase j, (klDiv (q k) π).toReal, fun q' hq' => ?_⟩
  have := hq'.isProbabilityMeasure
  have h1 := integrable_id_of_sq hq'.integrable_sq
  have hvar : variance id q' = ∫ b, b ^ 2 ∂q' - mean q' ^ 2 := by
    rw [variance_eq_sub ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr
      hq'.integrable_sq)]
    rfl
  have hint : ∫ b, potential X y σe2 q j b ∂q' =
      (mean q' * ∑ i, X i j * r i - c * (∫ b, b ^ 2 ∂q') / 2) / σe2 := by
    unfold potential
    rw [integral_div, integral_sub (h1.mul_const _) ((hq'.integrable_sq.const_mul _).div_const 2),
      integral_mul_const, integral_div, integral_const_mul]
    rfl
  have hsplit : ∀ (f : Fin m → ℝ), ∑ k, f k = f j + ∑ k ∈ Finset.univ.erase j, f k :=
    fun f => (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  have hupd : ∀ (g : Fin m → Measure ℝ → ℝ),
      ∑ k ∈ Finset.univ.erase j, g k (Function.update q j q' k) =
        ∑ k ∈ Finset.univ.erase j, g k (q k) := fun g =>
    Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  have hres : ∀ i, y i - ∑ k, X i k * mean (Function.update q j q' k) = r i - X i j * mean q' :=
    fun i => by
      rw [hsplit, Function.update_self,
        hupd (fun k μ => X i k * mean μ)]
      simp only [r, partialResidual]
      ring
  have hsq : ∑ i, (r i - X i j * mean q') ^ 2 =
      ∑ i, r i ^ 2 - 2 * mean q' * ∑ i, X i j * r i + mean q' ^ 2 * c := by
    simp only [c, colNormSq, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold elbo expectedRSS
  simp only [hres]
  rw [hsplit (fun k => colNormSq X k * variance id (Function.update q j q' k)),
    hsplit (fun k => (klDiv (Function.update q j q' k) π).toReal), Function.update_self,
    hupd (fun k μ => colNormSq X k * variance id μ), hupd (fun _ μ => (klDiv μ π).toReal), hsq,
    hint, hvar]
  ring

/-- The CAVI update is an admissible factor, for a probability prior with a finite second
moment. -/
theorem isAdmissible_caviUpdate {n m : ℕ} {X : Matrix (Fin n) (Fin m) ℝ} {y : Fin n → ℝ}
    {σe2 : ℝ} {π : Measure ℝ}
    [IsProbabilityMeasure π]
    (hπ : Integrable (fun b : ℝ => b ^ 2) π) (hσ : 0 < σe2) (q : Fin m → Measure ℝ)
    (j : Fin m) : IsAdmissible π (caviUpdate X y σe2 π q j) := by
  have hexp := integrable_exp_potential' X y hσ q j (ν := π)
  have hf := integrable_potential X y σe2 q j hπ
  have hllr : Integrable (llr (π.tilted (potential X y σe2 q j)) π) π := by
    refine integrable_llr_tilted_left Measure.AbsolutelyContinuous.rfl hf ?_ hexp
      (continuous_potential X y σe2 q j).aemeasurable
    exact (integrable_zero ℝ ℝ π).congr (llr_self π).symm
  refine ⟨isProbabilityMeasure_tilted hexp, ?_, tilted_absolutelyContinuous π _, ?_⟩
  · exact (integrable_tilted_iff hexp _).mpr (integrable_exp_potential X y hσ q j hπ)
  · exact (integrable_tilted_iff hexp _).mpr (integrable_exp_potential X y hσ q j hllr)

/-- **The CAVI update maximizes the ELBO over its factor, with exact gap**: replacing factor
`j` by an admissible `q'` gives `ELBO(caviStep q j) - KL(q' ‖ caviUpdate q j)`. -/
theorem elbo_update_eq_sub {n m : ℕ} {X : Matrix (Fin n) (Fin m) ℝ} {y : Fin n → ℝ}
    {σe2 : ℝ} {π : Measure ℝ}
    [IsProbabilityMeasure π] (hπ : Integrable (fun b : ℝ => b ^ 2) π)
    (hσ : 0 < σe2) (q : Fin m → Measure ℝ) (j : Fin m) {q' : Measure ℝ}
    (hq' : IsAdmissible π q') :
    elbo X y σe2 π (Function.update q j q') =
      elbo X y σe2 π (caviStep X y σe2 π q j) - (klDiv q' (caviUpdate X y σe2 π q j)).toReal := by
  obtain ⟨C, hC⟩ := exists_elbo_update_eq (X := X) (y := y) (σe2 := σe2) (π := π) q j
  have hexp := integrable_exp_potential' X y hσ q j (ν := π)
  have hadm := isAdmissible_caviUpdate (X := X) (y := y) hπ hσ q j
  have := hadm.isProbabilityMeasure
  have gibbs : ∀ μ, IsAdmissible π μ → ∫ b, potential X y σe2 q j b ∂μ - (klDiv μ π).toReal =
      Real.log (∫ b, Real.exp (potential X y σe2 q j b) ∂π) -
        (klDiv μ (caviUpdate X y σe2 π q j)).toReal := by
    intro μ hμ
    have := hμ.isProbabilityMeasure
    have hfμ := integrable_potential X y σe2 q j hμ.integrable_sq
    have hac : μ ≪ caviUpdate X y σe2 π q j :=
      hμ.absolutelyContinuous.trans (absolutelyContinuous_tilted hexp)
    rw [toReal_klDiv_of_measure_eq hac (by simp),
      toReal_klDiv_of_measure_eq hμ.absolutelyContinuous (by simp), caviUpdate,
      integral_llr_tilted_right hμ.absolutelyContinuous hfμ hexp hμ.integrable_llr]
    ring
  have g1 := gibbs q' hq'
  have g2 := gibbs _ hadm
  rw [klDiv_self, ENNReal.toReal_zero] at g2
  rw [caviStep, hC _ hq', hC _ hadm]
  linarith

/-- **Coordinate ascent does not decrease the ELBO.** -/
theorem elbo_le_elbo_caviStep {n m : ℕ} {X : Matrix (Fin n) (Fin m) ℝ} {y : Fin n → ℝ}
    {σe2 : ℝ} {π : Measure ℝ}
    {q : Fin m → Measure ℝ} [IsProbabilityMeasure π]
    (hπ : Integrable (fun b : ℝ => b ^ 2) π) (hσ : 0 < σe2)
    {j : Fin m} (hqj : IsAdmissible π (q j)) :
    elbo X y σe2 π q ≤ elbo X y σe2 π (caviStep X y σe2 π q j) := by
  have h := elbo_update_eq_sub (X := X) (y := y) hπ hσ q j hqj
  rw [Function.update_eq_self] at h
  rw [h]
  linarith [ENNReal.toReal_nonneg (a := klDiv (q j) (caviUpdate X y σe2 π q j))]

/-- **The ELBO is nondecreasing along coordinate ascent**, for any update schedule. -/
theorem monotone_elbo_caviRun {n m : ℕ} {X : Matrix (Fin n) (Fin m) ℝ} {y : Fin n → ℝ}
    {σe2 : ℝ} {π : Measure ℝ}
    {q : Fin m → Measure ℝ} [IsProbabilityMeasure π]
    (hπ : Integrable (fun b : ℝ => b ^ 2) π) (hσ : 0 < σe2)
    (hq : ∀ k, IsAdmissible π (q k)) (s : ℕ → Fin m) :
    Monotone fun t => elbo X y σe2 π (caviRun X y σe2 π q s t) := by
  have hadm : ∀ t k, IsAdmissible π (caviRun X y σe2 π q s t k) := by
    intro t
    induction t with
    | zero => exact hq
    | succ t ih =>
      intro k
      simp only [caviRun, caviStep]
      by_cases hk : k = s t
      · subst hk
        rw [Function.update_self]
        exact isAdmissible_caviUpdate hπ hσ _ _
      · rw [Function.update_of_ne hk]
        exact ih k
  exact monotone_nat_of_le_succ fun t => elbo_le_elbo_caviStep hπ hσ (hadm t (s t))

/-- **Stationary points of coordinate ascent**: no admissible change of factor `j` increases
the ELBO iff `qⱼ` is the expected-log-joint update `π · exp fⱼ / Z`. -/
theorem isCoordMax_iff {n m : ℕ} {X : Matrix (Fin n) (Fin m) ℝ} {y : Fin n → ℝ}
    {σe2 : ℝ} {π : Measure ℝ}
    {q : Fin m → Measure ℝ} [IsProbabilityMeasure π]
    (hπ : Integrable (fun b : ℝ => b ^ 2) π) (hσ : 0 < σe2)
    {j : Fin m} (hqj : IsAdmissible π (q j)) :
    (∀ q', IsAdmissible π q' → elbo X y σe2 π (Function.update q j q') ≤ elbo X y σe2 π q) ↔
      q j = caviUpdate X y σe2 π q j := by
  have hexp := integrable_exp_potential' X y hσ q j (ν := π)
  have hadm := isAdmissible_caviUpdate (X := X) (y := y) hπ hσ q j
  have := hadm.isProbabilityMeasure
  have := hqj.isProbabilityMeasure
  constructor
  · intro hmax
    have h1 := hmax _ hadm
    have h2 := elbo_update_eq_sub (X := X) (y := y) hπ hσ q j hqj
    rw [Function.update_eq_self] at h2
    have h0 : (klDiv (q j) (caviUpdate X y σe2 π q j)).toReal = 0 := by
      have := ENNReal.toReal_nonneg (a := klDiv (q j) (caviUpdate X y σe2 π q j))
      change elbo X y σe2 π (caviStep X y σe2 π q j) ≤ _ at h1
      linarith
    have hne : klDiv (q j) (caviUpdate X y σe2 π q j) ≠ ∞ :=
      klDiv_ne_top (hqj.absolutelyContinuous.trans (absolutelyContinuous_tilted hexp))
        (integrable_llr_tilted_right hqj.absolutelyContinuous
          (integrable_potential X y σe2 q j hqj.integrable_sq) hqj.integrable_llr hexp)
    exact klDiv_eq_zero_iff.mp (((ENNReal.toReal_eq_zero_iff _).mp h0).resolve_right hne)
  · intro heq q' hq'
    have h := elbo_update_eq_sub (X := X) (y := y) hπ hσ q j hq'
    have hstep : caviStep X y σe2 π q j = q := by
      rw [caviStep, ← heq, Function.update_eq_self]
    rw [h, hstep]
    linarith [ENNReal.toReal_nonneg (a := klDiv q' (caviUpdate X y σe2 π q j))]

end MathlibExt.Biology.StatisticalGenetics.BOLTLMMVariational
