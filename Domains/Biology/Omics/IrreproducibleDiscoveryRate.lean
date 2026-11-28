/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.GaussianDensity
public import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# The copula mixture model and the irreproducible discovery rate

Two replicate experiments score the same candidate findings (peaks, binding sites, chromatin
interactions). The copula mixture model of Li, Brown, Huang and Bickel (2011) explains the
dependence between the two replicates' scores by a latent label: a finding is *reproducible*
(`K = 1`) with probability `π₁` and *irreproducible* (`K = 0`) with probability `π₀ = 1 - π₁`, and,
given its label, its latent pair `z = (z₁, z₂)` has the law

* `K = 1`: `N((μ, μ), σ² [[1, ρ], [ρ, 1]])`, with `μ > 0` and `0 < ρ ≤ 1`;
* `K = 0`: `N((0, 0), I₂)`.

The observed scores are monotone transforms `x_r = F_r⁻¹(G(z_r))` of the latent ones, where
`G(t) = π₀ Φ(t) + π₁ Φ((t - μ) / σ)` is the marginal distribution of each latent coordinate and
`F_r` the unknown marginal distribution of replicate `r`; so only the ranks of the scores carry
information, and the parameters `(π₁, μ, σ, ρ)` are estimated from them by an
expectation–maximization pseudo-likelihood. Here they are inputs.

Writing `h₀`, `h₁` for the densities of the two components, the *local irreproducible discovery
rate* of a finding with latent pair `z` is the posterior probability that it is irreproducible,

  `idr(z) = π₀ h₀(z) / (π₀ h₀(z) + π₁ h₁(z))`,

and the *irreproducible discovery rate* of a selected set `S` of findings is the average
`IDR(S) = (1 / |S|) ∑ i ∈ S, idr(z i)`, the expected fraction of irreproducible findings in `S`
given the latent pairs. Selecting findings so that `IDR(S) ≤ α` thus keeps the expected fraction
of irreproducible findings in the selected set at most `α`.

## Conventions

* A latent pair is a point of `EuclideanSpace ℝ (Fin 2)`, whose coordinates `z 0` and `z 1` are
  the latent scores of replicates `1` and `2`. The components are Mathlib's
  `multivariateGaussian 0 1` and
  `multivariateGaussian !₂[μ, μ] !![σ ^ 2, ρ * σ ^ 2; ρ * σ ^ 2, σ ^ 2]`, and `h₀`, `h₁` are
  `multivariateGaussianPDFReal` of the same means and covariance matrices.
* With `ρ = 1`, which the model allows, the reproducible component lies on the diagonal
  `z 0 = z 1` and has no density with respect to Lebesgue measure. A version of the posterior
  probability of `K = 0` is then `0` on the diagonal and `1` off it, and `idr` takes these values
  when `ρ = 1`. For `0 < π₁ < 1` and `σ ≠ 0` they are also the limits of the formula above as `ρ`
  increases to `1`.
* The parameters are real inputs. Each theorem assumes only what it uses: `π₁ ∈ [0, 1]` for the
  bounds and the probabilistic theorems, `σ ≠ 0` and `ρ ∈ (-1, 1]` for the posterior and the
  expected fraction, and `σ > 0` and `|ρ| ≤ 1` for the latent marginal. The source's `μ > 0` and
  `ρ > 0`, which make the reproducible findings the high and positively correlated ones, are
  needed by none of them.
* The findings form a type `ι`, finding `i` has latent pair `z i`, and a selected set is a
  `Finset ι`. The irreproducible discovery rate of the empty set is `0`.
* The local rate of finding `i` is the irreproducible discovery rate of the set consisting of it
  alone, `irreproducibleDiscoveryRate π₁ μ σ ρ z {i}`, and that of a latent pair `x` is
  `irreproducibleDiscoveryRate π₁ μ σ ρ id {x}`.
* In the probabilistic theorems the label and the latent pair of a finding have the joint law
  `π₀ δ₀ ⊗ N((0, 0), I₂) + π₁ δ₁ ⊗ N((μ, μ), σ² [[1, ρ], [ρ, 1]])` on `Fin 2 × ℝ²`, and the
  findings of a finite type `ι` are independent, with the product law.

## Main definition

* `irreproducibleDiscoveryRate π₁ μ σ ρ z S`: the irreproducible discovery rate `IDR(S)` of the
  set `S` of findings with latent pairs `z`, under the copula mixture model with parameters
  `(π₁, μ, σ, ρ)`.

## Main results

* `irreproducibleDiscoveryRate_eq_sum_div`: `IDR(S)` is the average of the local rates of the
  findings of `S`.
* `irreproducibleDiscoveryRate_singleton_of_ne_one`,
  `irreproducibleDiscoveryRate_singleton_of_eq_one`: the local rate
  `π₀ h₀(z) / (π₀ h₀(z) + π₁ h₁(z))` with the two bivariate normal densities written out, and its
  values when `ρ = 1`.
* `irreproducibleDiscoveryRate_nonneg`, `irreproducibleDiscoveryRate_le_one`: for `π₁ ∈ [0, 1]`
  the rates lie in `[0, 1]`.
* `withDensity_irreproducibleDiscoveryRate`, `irreproducibleDiscoveryRate_posterior`: the local
  rate is the posterior probability that a finding is irreproducible given its latent pair, a
  version of the conditional probability of `K = 0` given `z` (Bayes' rule).
* `cdf_latent_coordinate`: each latent coordinate has distribution function
  `G(t) = π₀ Φ(t) + π₁ Φ((t - μ) / σ)`.
* `irreproducibleDiscoveryRate_le_of_subset`: adding findings whose local rates are at least those
  of the selected ones does not decrease the irreproducible discovery rate, so the rate of the
  `k` findings with the smallest local rates is nondecreasing in `k`.
* `lintegral_fraction_irreproducible`: for independent findings, `IDR(S)` is the conditional
  expectation of the fraction of irreproducible findings in `S` given all the latent pairs.
* `lintegral_fraction_irreproducible_le`: a selection rule that always selects a set with
  `IDR(S) ≤ α` keeps the expected fraction of irreproducible findings in the selected set at most
  `α`.

## References

* Q. Li, J. B. Brown, H. Huang and P. J. Bickel, "Measuring reproducibility of high-throughput
  experiments", Ann. Appl. Stat. 5 (2011), 1752–1779, <https://doi.org/10.1214/11-AOAS466>:
  Section 2.2.2 (the copula mixture model, (2.5a)–(2.5c) and (2.8)) and Section 2.3 (the local
  idr (2.9), the IDR (2.10) and the selection procedure).
* K. Krismer, Y. Guo and D. K. Gifford, "IDR2D identifies reproducible genomic interactions",
  Nucleic Acids Res. 48 (2020), e31, <https://doi.org/10.1093/nar/gkaa030>: introduction (IDR as a
  copula mixture with one reproducible and one irreproducible component).
-/

@[expose] public section

namespace Domains.Biology.Omics.IrreproducibleDiscoveryRate

open MeasureTheory ProbabilityTheory MetaMathlibExt Matrix

variable {ι : Type*}

/-- The **irreproducible discovery rate** `IDR(S)` of a set `S` of findings under the **copula
mixture model** of two replicate experiments (Li, Brown, Huang and Bickel 2011).

Two replicate experiments score the same findings, larger scores meaning stronger evidence.
Under the model, finding `i` is reproducible (`K i = 1`) with probability `π₁` and irreproducible
(`K i = 0`) with probability `π₀ = 1 - π₁`, and given its label its latent pair
`z i = (z i 0, z i 1)` is drawn from `N((μ, μ), σ² [[1, ρ], [ρ, 1]])` when `K i = 1` and from
`N((0, 0), I₂)` when `K i = 0`, with `μ > 0` and `0 < ρ ≤ 1`. The observed scores are the
monotone transforms `x i r = F_r⁻¹(G(z i r))`, where `G(t) = π₀ Φ(t) + π₁ Φ((t - μ) / σ)` is the
marginal distribution of each latent coordinate (`cdf_latent_coordinate`) and `F_r` the unknown
marginal distribution of replicate `r`, so that the dependence between the replicates is a
mixture of a Gaussian copula and the independence copula, and only the ranks of the scores
matter. The parameters `(π₁, μ, σ, ρ)`, estimated from the ranks in practice, are inputs here.

With `h₀ = multivariateGaussianPDFReal 0 1` and
`h₁ = multivariateGaussianPDFReal !₂[μ, μ] !![σ ^ 2, ρ * σ ^ 2; ρ * σ ^ 2, σ ^ 2]` the densities of
the two components, the *local irreproducible discovery rate* of a finding with latent pair `x`
is

  `idr(x) = π₀ h₀(x) / (π₀ h₀(x) + π₁ h₁(x))`,

the posterior probability that the finding is irreproducible
(`irreproducibleDiscoveryRate_posterior`). When `ρ = 1` the reproducible component lies on the
diagonal `x 0 = x 1` and has no density; `idr(x)` is then `0` on the diagonal and `1` off it,
again a version of the posterior probability. The irreproducible discovery rate of `S`, with `z i`
the latent pair of finding `i`, is

  `IDR(S) = (1 / |S|) ∑ i ∈ S, idr(z i)`,

the average of the local rates of the findings of `S`, and `0` for the empty set; the local rate
of finding `i` is `IDR({i})` (`irreproducibleDiscoveryRate_eq_sum_div`). For independent findings
`IDR(S)` is the expected fraction of irreproducible findings in `S` given the latent pairs
(`lintegral_fraction_irreproducible`), so selecting the findings with the smallest local rates
for as long as `IDR(S) ≤ α` keeps the expected fraction of irreproducible findings in the selected
set at most `α` (`irreproducibleDiscoveryRate_le_of_subset`,
`lintegral_fraction_irreproducible_le`), as the local false discovery rate does for the false
discovery rate in a two-group model.

For genomic interactions, which have two anchors, the findings are the pairs of a one-to-one
correspondence between the interactions of the two replicates (Krismer, Guo and Gifford 2020;
`Domains.Biology.Omics.InteractionCorrespondence.IsResolvedCorrespondence`): an interaction of
replicate 1 whose anchors overlap, or lie within a maximal gap of, those of some interaction of
replicate 2 is paired with such an interaction of minimal ambiguity-resolution value, unless one of
its partners of minimal value is paired with another interaction of replicate 1. The scores of
these pairs enter the same model. -/
noncomputable def irreproducibleDiscoveryRate (π₁ μ σ ρ : ℝ) (z : ι → EuclideanSpace ℝ (Fin 2))
    (S : Finset ι) : ℝ :=
  let h₀ := multivariateGaussianPDFReal (0 : EuclideanSpace ℝ (Fin 2)) 1
  let h₁ := multivariateGaussianPDFReal !₂[μ, μ] !![σ ^ 2, ρ * σ ^ 2; ρ * σ ^ 2, σ ^ 2]
  let idr : EuclideanSpace ℝ (Fin 2) → ℝ := fun x =>
    if ρ = 1 then (if x 0 = x 1 then 0 else 1)
    else (1 - π₁) * h₀ x / ((1 - π₁) * h₀ x + π₁ * h₁ x)
  (∑ i ∈ S, idr (z i)) / S.card

section LocalRate

variable {π₁ μ σ ρ : ℝ} {z : ι → EuclideanSpace ℝ (Fin 2)}

/-- The irreproducible discovery rate of a set of findings is the average of the local rates of
its findings, the rate of each finding alone. -/
theorem irreproducibleDiscoveryRate_eq_sum_div (S : Finset ι) :
    irreproducibleDiscoveryRate π₁ μ σ ρ z S =
      (∑ i ∈ S, irreproducibleDiscoveryRate π₁ μ σ ρ z {i}) / S.card := by
  simp [irreproducibleDiscoveryRate]

/-- The local rate of a finding depends only on its latent pair. -/
theorem irreproducibleDiscoveryRate_singleton_eq_id (i : ι) :
    irreproducibleDiscoveryRate π₁ μ σ ρ z {i} = irreproducibleDiscoveryRate π₁ μ σ ρ id {z i} := by
  simp [irreproducibleDiscoveryRate]

private theorem multivariateGaussianPDFReal_zero_one_apply (x : EuclideanSpace ℝ (Fin 2)) :
    multivariateGaussianPDFReal (0 : EuclideanSpace ℝ (Fin 2)) 1 x =
      Real.exp (-(x 0 ^ 2 + x 1 ^ 2) / 2) / (2 * Real.pi) := by
  have hq : WithLp.ofLp (x - 0) ⬝ᵥ (1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *ᵥ WithLp.ofLp (x - 0) =
      x 0 ^ 2 + x 1 ^ 2 := by
    rw [inv_one, one_mulVec, sub_zero, dotProduct, Fin.sum_univ_two]; ring
  rw [multivariateGaussianPDFReal, hq, det_one, Real.sqrt_one, inv_one, mul_one, Fintype.card_fin,
    Real.sq_sqrt (by positivity)]
  ring_nf

private theorem multivariateGaussianPDFReal_reproducible_apply (μ σ ρ : ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    multivariateGaussianPDFReal !₂[μ, μ] !![σ ^ 2, ρ * σ ^ 2; ρ * σ ^ 2, σ ^ 2] x =
      Real.exp (-((x 0 - μ) ^ 2 - 2 * ρ * (x 0 - μ) * (x 1 - μ) + (x 1 - μ) ^ 2) /
          (2 * σ ^ 2 * (1 - ρ ^ 2))) / (2 * Real.pi * σ ^ 2 * √(1 - ρ ^ 2)) := by
  have hdet : (!![σ ^ 2, ρ * σ ^ 2; ρ * σ ^ 2, σ ^ 2] : Matrix (Fin 2) (Fin 2) ℝ).det =
      σ ^ 4 * (1 - ρ ^ 2) := by
    rw [det_fin_two_of]; ring
  have hsqrt : √(σ ^ 4 * (1 - ρ ^ 2)) = σ ^ 2 * √(1 - ρ ^ 2) := by
    rw [Real.sqrt_mul (by positivity), show σ ^ 4 = (σ ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [multivariateGaussianPDFReal, hdet, hsqrt, Fintype.card_fin, Real.sq_sqrt (by positivity)]
  by_cases h0 : σ ^ 2 * √(1 - ρ ^ 2) = 0
  · rw [h0, _root_.inv_zero, mul_zero, zero_mul,
      show 2 * Real.pi * σ ^ 2 * √(1 - ρ ^ 2) = 2 * Real.pi * (σ ^ 2 * √(1 - ρ ^ 2)) by ring, h0,
      mul_zero, div_zero]
  · have hσ : σ ≠ 0 := by rintro rfl; simp at h0
    have hρ : 0 < 1 - ρ ^ 2 := by
      by_contra hle
      exact h0 (by rw [Real.sqrt_eq_zero'.2 (not_lt.1 hle), mul_zero])
    have hd : σ ^ 4 * (1 - ρ ^ 2) ≠ 0 := by positivity
    have hq : WithLp.ofLp (x - !₂[μ, μ]) ⬝ᵥ
        (!![σ ^ 2, ρ * σ ^ 2; ρ * σ ^ 2, σ ^ 2] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *ᵥ
          WithLp.ofLp (x - !₂[μ, μ]) =
        ((x 0 - μ) ^ 2 - 2 * ρ * (x 0 - μ) * (x 1 - μ) + (x 1 - μ) ^ 2) /
          (σ ^ 2 * (1 - ρ ^ 2)) := by
      rw [inv_def, hdet, adjugate_fin_two_of, Ring.inverse_eq_inv', smul_mulVec, dotProduct_smul]
      simp only [dotProduct, Fin.sum_univ_two, mulVec, Fin.isValue, WithLp.ofLp_sub,
        Pi.sub_apply, smul_eq_mul, of_apply, cons_val', cons_val_zero, cons_val_one,
        empty_val', cons_val_fin_one]
      field_simp
      ring
    rw [hq, div_eq_mul_inv (Real.exp _), mul_comm (Real.exp _)]
    congr 1
    · field_simp
    · congr 1
      field_simp

/-- **The local irreproducible discovery rate.** For `ρ ≠ 1`, the local rate of finding `i`, with
latent pair `(u, v) = (z i 0, z i 1)`, is

  `π₀ h₀(u, v) / (π₀ h₀(u, v) + π₁ h₁(u, v))`,

where `π₀ = 1 - π₁`, `h₀(u, v) = exp(-(u² + v²) / 2) / (2π)` is the standard bivariate normal
density and

  `h₁(u, v) = exp(-((u - μ)² - 2ρ(u - μ)(v - μ) + (v - μ)²) / (2σ²(1 - ρ²))) / (2πσ²√(1 - ρ²))`

the bivariate normal density with means `μ`, variances `σ²` and correlation `ρ`. (When `σ = 0` or
`|ρ| ≥ 1` the second expression is `0`, by the conventions `√t = 0` for `t < 0` and `t / 0 = 0`.) -/
theorem irreproducibleDiscoveryRate_singleton_of_ne_one (hρ : ρ ≠ 1) (i : ι) :
    irreproducibleDiscoveryRate π₁ μ σ ρ z {i} =
      (1 - π₁) * (Real.exp (-(z i 0 ^ 2 + z i 1 ^ 2) / 2) / (2 * Real.pi)) /
        ((1 - π₁) * (Real.exp (-(z i 0 ^ 2 + z i 1 ^ 2) / 2) / (2 * Real.pi)) +
          π₁ * (Real.exp (-((z i 0 - μ) ^ 2 - 2 * ρ * (z i 0 - μ) * (z i 1 - μ) +
              (z i 1 - μ) ^ 2) / (2 * σ ^ 2 * (1 - ρ ^ 2))) /
            (2 * Real.pi * σ ^ 2 * √(1 - ρ ^ 2)))) := by
  simp only [irreproducibleDiscoveryRate, Finset.sum_singleton, Finset.card_singleton,
    Nat.cast_one, div_one, hρ, ↓reduceIte, multivariateGaussianPDFReal_zero_one_apply,
    multivariateGaussianPDFReal_reproducible_apply]

/-- When `ρ = 1`, the local rate of a finding is `0` if its two latent scores are equal, where
all the reproducible findings lie, and `1` otherwise. -/
theorem irreproducibleDiscoveryRate_singleton_of_eq_one (i : ι) :
    irreproducibleDiscoveryRate π₁ μ σ 1 z {i} = if z i 0 = z i 1 then 0 else 1 := by
  simp [irreproducibleDiscoveryRate]

private theorem localRate_mem_Icc (hπ₁ : π₁ ∈ Set.Icc 0 1) (x : EuclideanSpace ℝ (Fin 2)) :
    irreproducibleDiscoveryRate π₁ μ σ ρ id {x} ∈ Set.Icc 0 1 := by
  simp only [irreproducibleDiscoveryRate, Finset.sum_singleton, Finset.card_singleton,
    Nat.cast_one, div_one, id]
  split_ifs
  · simp
  · simp
  · have h₀ : 0 ≤ multivariateGaussianPDFReal (0 : EuclideanSpace ℝ (Fin 2)) 1 x := by
      rw [multivariateGaussianPDFReal_zero_one_apply]; positivity
    have h₁ : 0 ≤ multivariateGaussianPDFReal !₂[μ, μ]
        !![σ ^ 2, ρ * σ ^ 2; ρ * σ ^ 2, σ ^ 2] x := by
      rw [multivariateGaussianPDFReal_reproducible_apply]; positivity
    have ha : 0 ≤ (1 - π₁) * multivariateGaussianPDFReal 0 1 x :=
      mul_nonneg (sub_nonneg.2 hπ₁.2) h₀
    have hb : 0 ≤ π₁ * multivariateGaussianPDFReal !₂[μ, μ]
        !![σ ^ 2, ρ * σ ^ 2; ρ * σ ^ 2, σ ^ 2] x := mul_nonneg hπ₁.1 h₁
    exact ⟨div_nonneg ha (add_nonneg ha hb), div_le_one_of_le₀ (le_add_of_nonneg_right hb)
      (add_nonneg ha hb)⟩

/-- For `π₁ ∈ [0, 1]` the irreproducible discovery rate is nonnegative. -/
theorem irreproducibleDiscoveryRate_nonneg (hπ₁ : π₁ ∈ Set.Icc 0 1) (S : Finset ι) :
    0 ≤ irreproducibleDiscoveryRate π₁ μ σ ρ z S := by
  rw [irreproducibleDiscoveryRate_eq_sum_div]
  refine div_nonneg (Finset.sum_nonneg fun i _ => ?_) (Nat.cast_nonneg _)
  rw [irreproducibleDiscoveryRate_singleton_eq_id]
  exact (localRate_mem_Icc hπ₁ _).1

/-- For `π₁ ∈ [0, 1]` the irreproducible discovery rate is at most `1`. -/
theorem irreproducibleDiscoveryRate_le_one (hπ₁ : π₁ ∈ Set.Icc 0 1) (S : Finset ι) :
    irreproducibleDiscoveryRate π₁ μ σ ρ z S ≤ 1 := by
  rw [irreproducibleDiscoveryRate_eq_sum_div]
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  rw [div_le_one (by exact_mod_cast hS.card_pos)]
  calc ∑ i ∈ S, irreproducibleDiscoveryRate π₁ μ σ ρ z {i} ≤ ∑ _i ∈ S, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => by
          rw [irreproducibleDiscoveryRate_singleton_eq_id]; exact (localRate_mem_Icc hπ₁ _).2
    _ = S.card := by simp

end LocalRate

section Posterior

variable {π₁ μ σ ρ : ℝ}

private theorem posDef_reproducibleCov (hσ : σ ≠ 0) (hρ : |ρ| < 1) :
    (!![σ ^ 2, ρ * σ ^ 2; ρ * σ ^ 2, σ ^ 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h; push Not at h
      exact hx (by ext i; fin_cases i <;> simp [h.1, h.2])
    have h1 : -1 < ρ := (abs_lt.1 hρ).1
    have h2 : ρ < 1 := (abs_lt.1 hρ).2
    have hs : 0 < σ ^ 2 := by positivity
    simp only [star_trivial, dotProduct, Fin.sum_univ_two, mulVec, of_apply, cons_val',
      cons_val_zero, cons_val_one, empty_val', cons_val_fin_one, Fin.isValue]
    have key : 0 < x 0 ^ 2 + 2 * ρ * x 0 * x 1 + x 1 ^ 2 := by
      rcases hx' with h | h
      · have : 0 < x 0 ^ 2 := by positivity
        nlinarith [sq_nonneg (x 1 + ρ * x 0), mul_pos (sub_pos.2 h2) (sub_pos.2 h1)]
      · have : 0 < x 1 ^ 2 := by positivity
        nlinarith [sq_nonneg (x 0 + ρ * x 1), mul_pos (sub_pos.2 h2) (sub_pos.2 h1)]
    nlinarith [mul_pos hs key]

private theorem posSemidef_reproducibleCov (hρ : |ρ| ≤ 1) :
    (!![σ ^ 2, ρ * σ ^ 2; ρ * σ ^ 2, σ ^ 2] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · have h1 : -1 ≤ ρ := (abs_le.1 hρ).1
    have h2 : ρ ≤ 1 := (abs_le.1 hρ).2
    simp only [star_trivial, dotProduct, Fin.sum_univ_two, mulVec, of_apply, cons_val',
      cons_val_zero, cons_val_one, empty_val', cons_val_fin_one, Fin.isValue]
    have key : 0 ≤ x 0 ^ 2 + 2 * ρ * x 0 * x 1 + x 1 ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 h2) (sq_nonneg (x 0 - x 1)),
        mul_nonneg (sub_nonneg.2 h1) (sq_nonneg (x 0 + x 1))]
    nlinarith [mul_nonneg (sq_nonneg σ) key]

/-- The diagonal `z 0 = z 1` is null for the irreproducible component. -/
private theorem multivariateGaussian_zero_one_diagonal :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) 1 {x | x 0 = x 1} = 0 := by
  rw [multivariateGaussian_eq_withDensity _ PosDef.one]
  refine withDensity_absolutelyContinuous _ _ ?_
  let L : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ :=
    (EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).toLinearMap -
      (EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).toLinearMap
  have hs : {x : EuclideanSpace ℝ (Fin 2) | x 0 = x 1} = (LinearMap.ker L : Set _) := by
    ext x; simp [L, sub_eq_zero]
  rw [hs]
  refine Measure.addHaar_submodule _ _ fun h => ?_
  have : (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
  simp [L] at this

/-- With `ρ = 1` the reproducible component lies on the diagonal `z 0 = z 1`. -/
private theorem ae_diagonal_reproducible_one (μ σ : ℝ) :
    ∀ᵐ x ∂multivariateGaussian !₂[μ, μ] !![σ ^ 2, 1 * σ ^ 2; 1 * σ ^ 2, σ ^ 2], x 0 = x 1 := by
  set N := multivariateGaussian !₂[μ, μ] (!![σ ^ 2, 1 * σ ^ 2; 1 * σ ^ 2, σ ^ 2] :
    Matrix (Fin 2) (Fin 2) ℝ)
  have hS := posSemidef_reproducibleCov (σ := σ) (ρ := 1) (by norm_num)
  let v : EuclideanSpace ℝ (Fin 2) := !₂[1, -1]
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin 2)) := innerSL ℝ v
  have hL : ∀ x : EuclideanSpace ℝ (Fin 2), L x = x 0 - x 1 := by
    intro x
    simp [L, v, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have hvar : Var[L; N] = 0 := by
    have : Var[L; N] = covarianceBilin N v v := by
      rw [covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id, covariance_self]
      · rfl
      · exact L.measurable.aemeasurable
    rw [this, covarianceBilin_multivariateGaussian hS]
    simp [v, dotProduct, mulVec, Fin.sum_univ_two]
  have hmean : ∫ x, L x ∂N = 0 := by
    rw [L.integral_comp_id_comm IsGaussian.integrable_id, integral_id_multivariateGaussian, hL]
    simp
  have hmap : N.map L = Measure.dirac 0 := by
    rw [IsGaussian.map_eq_gaussianReal, hvar, hmean]
    simp [gaussianReal_zero_var]
  have : N (L ⁻¹' {0})ᶜ = 0 := by
    have h : N.map L ({0}ᶜ : Set ℝ) = Measure.dirac 0 ({0}ᶜ : Set ℝ) := by rw [hmap]
    rw [Measure.map_apply L.measurable (measurableSet_singleton 0).compl] at h
    simpa using h
  refine measure_mono_null (fun x hx => ?_) this
  simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, hL]
  exact fun h => hx (sub_eq_zero.1 h)

private theorem measurable_multivariateGaussianPDFReal_zero_one :
    Measurable (multivariateGaussianPDFReal (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  have : multivariateGaussianPDFReal (0 : EuclideanSpace ℝ (Fin 2)) 1 =
      fun x => Real.exp (-(x 0 ^ 2 + x 1 ^ 2) / 2) / (2 * Real.pi) :=
    funext multivariateGaussianPDFReal_zero_one_apply
  rw [this]; fun_prop

private theorem measurable_multivariateGaussianPDFReal_reproducible :
    Measurable (multivariateGaussianPDFReal !₂[μ, μ] !![σ ^ 2, ρ * σ ^ 2; ρ * σ ^ 2, σ ^ 2]) := by
  have : multivariateGaussianPDFReal !₂[μ, μ] !![σ ^ 2, ρ * σ ^ 2; ρ * σ ^ 2, σ ^ 2] =
      fun x : EuclideanSpace ℝ (Fin 2) =>
        Real.exp (-((x 0 - μ) ^ 2 - 2 * ρ * (x 0 - μ) * (x 1 - μ) + (x 1 - μ) ^ 2) /
          (2 * σ ^ 2 * (1 - ρ ^ 2))) / (2 * Real.pi * σ ^ 2 * √(1 - ρ ^ 2)) :=
    funext (multivariateGaussianPDFReal_reproducible_apply μ σ ρ)
  rw [this]; fun_prop

/-- **Bayes' rule for the copula mixture model.** For `π₁ ∈ [0, 1]`, `σ ≠ 0` and `ρ ∈ (-1, 1]`,
the irreproducible part `π₀ N((0, 0), I₂)` of the latent mixture
`π₀ N((0, 0), I₂) + π₁ N((μ, μ), σ² [[1, ρ], [ρ, 1]])` has density `idr` with respect to the
mixture, where `idr x = irreproducibleDiscoveryRate π₁ μ σ ρ id {x}` is the local rate of a finding
with latent pair `x`. -/
theorem withDensity_irreproducibleDiscoveryRate (hπ₁ : π₁ ∈ Set.Icc 0 1) (hσ : σ ≠ 0)
    (hρ : ρ ∈ Set.Ioc (-1) 1) :
    (ENNReal.ofReal (1 - π₁) • multivariateGaussian 0 1 +
        ENNReal.ofReal π₁ • multivariateGaussian !₂[μ, μ] !![σ ^ 2, ρ * σ ^ 2; ρ * σ ^ 2, σ ^ 2]
      ).withDensity (fun x => ENNReal.ofReal (irreproducibleDiscoveryRate π₁ μ σ ρ id {x})) =
      ENNReal.ofReal (1 - π₁) • multivariateGaussian 0 1 := by
  by_cases hρ1 : ρ = 1
  · subst hρ1
    rw [withDensity_add_measure, withDensity_smul_measure, withDensity_smul_measure]
    have h₀ : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) 1).withDensity
        (fun x => ENNReal.ofReal (irreproducibleDiscoveryRate π₁ μ σ 1 id {x})) =
        multivariateGaussian 0 1 := by
      conv_rhs =>
        rw [← withDensity_one (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) 1)]
      refine withDensity_congr_ae ?_
      have hoff : ∀ᵐ x ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) 1, x 0 ≠ x 1 :=
        ae_iff.2 (by simpa using multivariateGaussian_zero_one_diagonal)
      filter_upwards [hoff] with x hx
      simp [irreproducibleDiscoveryRate_singleton_of_eq_one, hx]
    have h₁ : (multivariateGaussian !₂[μ, μ] !![σ ^ 2, 1 * σ ^ 2; 1 * σ ^ 2, σ ^ 2]).withDensity
        (fun x => ENNReal.ofReal (irreproducibleDiscoveryRate π₁ μ σ 1 id {x})) = 0 := by
      rw [← withDensity_zero]
      refine withDensity_congr_ae ?_
      filter_upwards [ae_diagonal_reproducible_one μ σ] with x hx
      simp [irreproducibleDiscoveryRate_singleton_of_eq_one, hx]
    rw [h₀, h₁, smul_zero, add_zero]
  · have hρ' : |ρ| < 1 := abs_lt.2 ⟨hρ.1, lt_of_le_of_ne hρ.2 hρ1⟩
    rw [multivariateGaussian_eq_withDensity _ PosDef.one,
      multivariateGaussian_eq_withDensity _ (posDef_reproducibleCov hσ hρ')]
    set h₀ := multivariateGaussianPDFReal (0 : EuclideanSpace ℝ (Fin 2)) 1
    set h₁ := multivariateGaussianPDFReal !₂[μ, μ] !![σ ^ 2, ρ * σ ^ 2; ρ * σ ^ 2, σ ^ 2]
    have hh₀ : ∀ x, 0 ≤ h₀ x := fun x => by
      simp only [h₀, multivariateGaussianPDFReal_zero_one_apply]; positivity
    have hh₁ : ∀ x, 0 ≤ h₁ x := fun x => by
      simp only [h₁, multivariateGaussianPDFReal_reproducible_apply]; positivity
    have hm₀ : Measurable fun x => ENNReal.ofReal (h₀ x) :=
      ENNReal.measurable_ofReal.comp measurable_multivariateGaussianPDFReal_zero_one
    have hm₁ : Measurable fun x => ENNReal.ofReal (h₁ x) :=
      ENNReal.measurable_ofReal.comp measurable_multivariateGaussianPDFReal_reproducible
    have hidr : ∀ x, irreproducibleDiscoveryRate π₁ μ σ ρ id {x} =
        (1 - π₁) * h₀ x / ((1 - π₁) * h₀ x + π₁ * h₁ x) := fun x => by
      simp [irreproducibleDiscoveryRate, hρ1, h₀, h₁]
    have hmidr :
        Measurable fun x => ENNReal.ofReal (irreproducibleDiscoveryRate π₁ μ σ ρ id {x}) := by
      simp_rw [hidr]
      exact ENNReal.measurable_ofReal.comp
        ((measurable_const.mul measurable_multivariateGaussianPDFReal_zero_one).div
          ((measurable_const.mul measurable_multivariateGaussianPDFReal_zero_one).add
            (measurable_const.mul measurable_multivariateGaussianPDFReal_reproducible)))
    rw [← withDensity_smul _ hm₀, ← withDensity_smul _ hm₁,
      ← withDensity_add_left (hm₀.const_smul _), ← withDensity_mul _
        ((hm₀.const_smul _).add (hm₁.const_smul _)) hmidr]
    congr 1; funext x
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hidr]
    have ha : 0 ≤ (1 - π₁) * h₀ x := mul_nonneg (sub_nonneg.2 hπ₁.2) (hh₀ x)
    have hb : 0 ≤ π₁ * h₁ x := mul_nonneg hπ₁.1 (hh₁ x)
    rw [← ENNReal.ofReal_mul (sub_nonneg.2 hπ₁.2), ← ENNReal.ofReal_mul hπ₁.1,
      ← ENNReal.ofReal_add ha hb, ← ENNReal.ofReal_mul (add_nonneg ha hb)]
    congr 1
    rcases (add_nonneg ha hb).eq_or_lt with hD | hD
    · rw [← hD, div_zero, mul_zero]
      linarith
    · field_simp

/-- **The local rate is the posterior probability of irreproducibility.** Let `π₁ ∈ [0, 1]`,
`σ ≠ 0` and `ρ ∈ (-1, 1]`, and let `P` be the joint law of the label `K` and the latent pair `z`
of a finding under the copula mixture model: `K = 0` with probability `π₀ = 1 - π₁` and then
`z ~ N((0, 0), I₂)`, and `K = 1` with probability `π₁` and then
`z ~ N((μ, μ), σ² [[1, ρ], [ρ, 1]])`. Then for every measurable set `B` of latent pairs,

  `P(K = 0, z ∈ B) = ∫_B idr dP_z`,

where `P_z` is the law of `z` and `idr x = irreproducibleDiscoveryRate π₁ μ σ ρ id {x}`: the local
rate is a version of the conditional probability that `K = 0` given `z`. -/
theorem irreproducibleDiscoveryRate_posterior (hπ₁ : π₁ ∈ Set.Icc 0 1) (hσ : σ ≠ 0)
    (hρ : ρ ∈ Set.Ioc (-1) 1) {B : Set (EuclideanSpace ℝ (Fin 2))} (hB : MeasurableSet B) :
    let P : Measure (Fin 2 × EuclideanSpace ℝ (Fin 2)) :=
      ENNReal.ofReal (1 - π₁) • (Measure.dirac 0).prod (multivariateGaussian 0 1) +
        ENNReal.ofReal π₁ • (Measure.dirac 1).prod
          (multivariateGaussian !₂[μ, μ] !![σ ^ 2, ρ * σ ^ 2; ρ * σ ^ 2, σ ^ 2])
    P ({0} ×ˢ B) = ∫⁻ x in B, ENNReal.ofReal (irreproducibleDiscoveryRate π₁ μ σ ρ id {x})
      ∂(P.map Prod.snd) := by
  intro P
  have hsnd : P.map Prod.snd = ENNReal.ofReal (1 - π₁) • multivariateGaussian 0 1 +
      ENNReal.ofReal π₁ • multivariateGaussian !₂[μ, μ] !![σ ^ 2, ρ * σ ^ 2; ρ * σ ^ 2, σ ^ 2] := by
    simp only [P]
    rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul,
      Measure.map_snd_prod, Measure.map_snd_prod]
    · simp
    all_goals exact measurable_snd.aemeasurable
  rw [hsnd, ← withDensity_apply _ hB, withDensity_irreproducibleDiscoveryRate hπ₁ hσ hρ]
  simp [P, Measure.prod_prod]

/-- **The latent marginal distribution.** For `π₁ ∈ [0, 1]`, `σ > 0` and `|ρ| ≤ 1`, each latent
coordinate `z r` of the mixture `π₀ N((0, 0), I₂) + π₁ N((μ, μ), σ² [[1, ρ], [ρ, 1]])` has
distribution function

  `G(t) = π₀ Φ(t) + π₁ Φ((t - μ) / σ)`,

where `π₀ = 1 - π₁` and `Φ` is the standard normal distribution function. -/
theorem cdf_latent_coordinate (hπ₁ : π₁ ∈ Set.Icc 0 1) (hσ : 0 < σ) (hρ : |ρ| ≤ 1) (r : Fin 2)
    (t : ℝ) :
    cdf ((ENNReal.ofReal (1 - π₁) • multivariateGaussian 0 1 +
        ENNReal.ofReal π₁ • multivariateGaussian !₂[μ, μ] !![σ ^ 2, ρ * σ ^ 2; ρ * σ ^ 2, σ ^ 2]
        ).map fun x : EuclideanSpace ℝ (Fin 2) => x r) t =
      (1 - π₁) * cdf (gaussianReal 0 1) t + π₁ * cdf (gaussianReal 0 1) ((t - μ) / σ) := by
  have hmap : (ENNReal.ofReal (1 - π₁) • multivariateGaussian 0 1 +
      ENNReal.ofReal π₁ • multivariateGaussian !₂[μ, μ] !![σ ^ 2, ρ * σ ^ 2; ρ * σ ^ 2, σ ^ 2]
        ).map (fun x : EuclideanSpace ℝ (Fin 2) => x r) =
      ENNReal.ofReal (1 - π₁) • gaussianReal 0 1 +
        ENNReal.ofReal π₁ • gaussianReal μ (σ ^ 2).toNNReal := by
    rw [Measure.map_add _ _ (by fun_prop), Measure.map_smul, Measure.map_smul,
      (measurePreserving_eval_multivariateGaussian PosDef.one.posSemidef).map_eq,
      (measurePreserving_eval_multivariateGaussian (posSemidef_reproducibleCov hρ)).map_eq]
    · fin_cases r <;> simp
    all_goals exact (by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin 2) => x r).aemeasurable
  have hG : gaussianReal μ (σ ^ 2).toNNReal =
      (gaussianReal 0 1).map fun x => μ + σ * x := by
    rw [show (fun x : ℝ => μ + σ * x) = (fun x => μ + x) ∘ (fun x => σ * x) from rfl,
      ← Measure.map_map (measurable_const_add μ) (measurable_const_mul σ),
      gaussianReal_map_const_mul, gaussianReal_map_const_add]
    congr 1
    · ring
    · ext; simp [sq_nonneg]
  have hIic : (fun x => μ + σ * x) ⁻¹' Set.Iic t = Set.Iic ((t - μ) / σ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic]
    rw [le_div_iff₀ hσ]
    constructor <;> intro h <;> linarith
  have hprob : IsProbabilityMeasure (ENNReal.ofReal (1 - π₁) • gaussianReal 0 1 +
      ENNReal.ofReal π₁ • gaussianReal μ (σ ^ 2).toNNReal) := by
    constructor
    simp only [_root_.add_apply, _root_.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (sub_nonneg.2 hπ₁.2) hπ₁.1]
    simp
  rw [hmap, cdf_eq_real, cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def,
    measureReal_def]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [hG, Measure.map_apply (by fun_prop) measurableSet_Iic, hIic,
    ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.2 hπ₁.2), ENNReal.toReal_ofReal hπ₁.1]

end Posterior

section Selection

variable {π₁ μ σ ρ : ℝ} {z : ι → EuclideanSpace ℝ (Fin 2)}

/-- **Selecting by the local rate.** Enlarging a nonempty selected set `S` to `T ⊇ S` by findings
whose local rates are at least those of the findings of `S` does not decrease the irreproducible
discovery rate. So, for findings ranked by increasing local rate, the rate of the first `k` is
nondecreasing in `k`, and selecting findings in that order for as long as the rate stays at most
`α` selects the largest set of first findings whose rate is at most `α`. -/
theorem irreproducibleDiscoveryRate_le_of_subset {S T : Finset ι} (hST : S ⊆ T) (hS : S.Nonempty)
    (h : ∀ i ∈ S, ∀ j ∈ T, j ∉ S → irreproducibleDiscoveryRate π₁ μ σ ρ z {i} ≤
      irreproducibleDiscoveryRate π₁ μ σ ρ z {j}) :
    irreproducibleDiscoveryRate π₁ μ σ ρ z S ≤ irreproducibleDiscoveryRate π₁ μ σ ρ z T := by
  classical
  rw [irreproducibleDiscoveryRate_eq_sum_div S, irreproducibleDiscoveryRate_eq_sum_div T]
  have hs : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hcard : (T.card : ℝ) = S.card + (T \ S).card := by
    rw [← Finset.card_sdiff_add_card_eq_card hST]; push_cast; ring
  rw [← Finset.sum_sdiff hST, hcard]
  have hkey : ∀ j ∈ T \ S, ∑ i ∈ S, irreproducibleDiscoveryRate π₁ μ σ ρ z {i} ≤
      S.card * irreproducibleDiscoveryRate π₁ μ σ ρ z {j} := fun j hj => by
    calc ∑ i ∈ S, irreproducibleDiscoveryRate π₁ μ σ ρ z {i}
        ≤ ∑ _i ∈ S, irreproducibleDiscoveryRate π₁ μ σ ρ z {j} :=
          Finset.sum_le_sum fun i hi => h i hi j (Finset.mem_sdiff.1 hj).1 (Finset.mem_sdiff.1 hj).2
      _ = S.card * irreproducibleDiscoveryRate π₁ μ σ ρ z {j} := by simp
  have hB : ((T \ S).card : ℝ) * ∑ i ∈ S, irreproducibleDiscoveryRate π₁ μ σ ρ z {i} ≤
      S.card * ∑ j ∈ T \ S, irreproducibleDiscoveryRate π₁ μ σ ρ z {j} := by
    calc ((T \ S).card : ℝ) * ∑ i ∈ S, irreproducibleDiscoveryRate π₁ μ σ ρ z {i}
        = ∑ _j ∈ T \ S, ∑ i ∈ S, irreproducibleDiscoveryRate π₁ μ σ ρ z {i} := by simp
      _ ≤ ∑ j ∈ T \ S, S.card * irreproducibleDiscoveryRate π₁ μ σ ρ z {j} :=
          Finset.sum_le_sum hkey
      _ = S.card * ∑ j ∈ T \ S, irreproducibleDiscoveryRate π₁ μ σ ρ z {j} := by
          rw [Finset.mul_sum]
  rw [div_le_div_iff₀ hs (by positivity)]
  nlinarith [hB]

end Selection

section ExpectedFraction

/-! ### The expected fraction of irreproducible findings -/

variable {π₁ μ σ ρ : ℝ}

/-- The joint law of the label and the latent pair of one finding. -/
private noncomputable def labelledLaw (π₁ μ σ ρ : ℝ) : Measure (Fin 2 × EuclideanSpace ℝ (Fin 2)) :=
  ENNReal.ofReal (1 - π₁) • (Measure.dirac 0).prod (multivariateGaussian 0 1) +
    ENNReal.ofReal π₁ • (Measure.dirac 1).prod
      (multivariateGaussian !₂[μ, μ] !![σ ^ 2, ρ * σ ^ 2; ρ * σ ^ 2, σ ^ 2])

private instance : IsFiniteMeasure (labelledLaw π₁ μ σ ρ) := by
  refine ⟨?_⟩
  simp only [labelledLaw, _root_.add_apply, _root_.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩

private theorem isProbabilityMeasure_labelledLaw (hπ₁ : π₁ ∈ Set.Icc 0 1) :
    IsProbabilityMeasure (labelledLaw π₁ μ σ ρ) := by
  constructor
  simp only [labelledLaw, _root_.add_apply, _root_.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.2 hπ₁.2) hπ₁.1]
  simp

private theorem measurable_localRate :
    Measurable fun x : EuclideanSpace ℝ (Fin 2) => irreproducibleDiscoveryRate π₁ μ σ ρ id {x} := by
  by_cases hρ1 : ρ = 1
  · subst hρ1
    simp only [irreproducibleDiscoveryRate_singleton_of_eq_one, id]
    exact Measurable.ite (measurableSet_eq_fun (by fun_prop) (by fun_prop)) measurable_const
      measurable_const
  · simp only [irreproducibleDiscoveryRate, Finset.sum_singleton, Finset.card_singleton,
      Nat.cast_one, div_one, hρ1, ↓reduceIte, id]
    exact (measurable_const.mul measurable_multivariateGaussianPDFReal_zero_one).div
      ((measurable_const.mul measurable_multivariateGaussianPDFReal_zero_one).add
        (measurable_const.mul measurable_multivariateGaussianPDFReal_reproducible))

/-- The irreproducible discovery rate of a set of findings is a measurable function of their
latent pairs. -/
theorem measurable_irreproducibleDiscoveryRate (S : Finset ι) :
    Measurable fun z : ι → EuclideanSpace ℝ (Fin 2) =>
      irreproducibleDiscoveryRate π₁ μ σ ρ z S := by
  have : (fun z : ι → EuclideanSpace ℝ (Fin 2) => irreproducibleDiscoveryRate π₁ μ σ ρ z S) =
      fun z => (∑ i ∈ S, irreproducibleDiscoveryRate π₁ μ σ ρ id {z i}) / S.card := by
    funext z
    rw [irreproducibleDiscoveryRate_eq_sum_div]
    simp_rw [irreproducibleDiscoveryRate_singleton_eq_id (z := z)]
  rw [this]
  exact (Finset.measurable_sum _ fun i _ =>
    measurable_localRate.comp (measurable_pi_apply i)).div_const _

/-- Bayes' rule against a function of the latent pair. -/
private theorem lintegral_ite_label (hπ₁ : π₁ ∈ Set.Icc 0 1) (hσ : σ ≠ 0)
    (hρ : ρ ∈ Set.Ioc (-1) 1) {φ : EuclideanSpace ℝ (Fin 2) → ENNReal} (hφ : Measurable φ) :
    ∫⁻ y, (if y.1 = 0 then φ y.2 else 0) ∂labelledLaw π₁ μ σ ρ =
      ∫⁻ y, ENNReal.ofReal (irreproducibleDiscoveryRate π₁ μ σ ρ id {y.2}) * φ y.2
        ∂labelledLaw π₁ μ σ ρ := by
  have hF : Measurable fun y : Fin 2 × EuclideanSpace ℝ (Fin 2) => if y.1 = 0 then φ y.2 else 0 :=
    Measurable.ite (measurable_fst (measurableSet_singleton 0)) (hφ.comp measurable_snd)
      measurable_const
  have hf : Measurable fun x : EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal (irreproducibleDiscoveryRate π₁ μ σ ρ id {x}) :=
    ENNReal.measurable_ofReal.comp measurable_localRate
  have hG : Measurable fun y : Fin 2 × EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal (irreproducibleDiscoveryRate π₁ μ σ ρ id {y.2}) * φ y.2 :=
    (hf.comp measurable_snd).mul (hφ.comp measurable_snd)
  have key := congrArg (fun m => ∫⁻ x, φ x ∂m) (withDensity_irreproducibleDiscoveryRate (μ := μ)
    hπ₁ hσ hρ)
  simp only [lintegral_withDensity_eq_lintegral_mul _ hf hφ, lintegral_add_measure,
    lintegral_smul_measure, Pi.mul_apply] at key
  simp only [labelledLaw, lintegral_add_measure, lintegral_smul_measure, Measure.dirac_prod,
    lintegral_map hF measurable_prodMk_left, lintegral_map hG measurable_prodMk_left]
  simpa using key.symm

/-- Bayes' rule for one of several independent findings, given all their latent pairs. -/
private theorem lintegral_pi_ite_label [Fintype ι] (hπ₁ : π₁ ∈ Set.Icc 0 1) (hσ : σ ≠ 0)
    (hρ : ρ ∈ Set.Ioc (-1) 1) (i : ι) {g : (ι → EuclideanSpace ℝ (Fin 2)) → ENNReal}
    (hg : Measurable g) :
    ∫⁻ ω, (if (ω i).1 = 0 then g (fun j => (ω j).2) else 0)
        ∂Measure.pi (fun _ : ι => labelledLaw π₁ μ σ ρ) =
      ∫⁻ ω, ENNReal.ofReal (irreproducibleDiscoveryRate π₁ μ σ ρ id {(ω i).2}) *
          g (fun j => (ω j).2) ∂Measure.pi (fun _ : ι => labelledLaw π₁ μ σ ρ) := by
  classical
  have hZ : Measurable fun ω : ι → Fin 2 × EuclideanSpace ℝ (Fin 2) => fun j => (ω j).2 := by
    fun_prop
  refine lintegral_eq_of_lmarginal_eq {i} ?_ ?_ ?_
  · exact Measurable.ite ((measurable_pi_apply i).fst (measurableSet_singleton 0)) (hg.comp hZ)
      measurable_const
  · exact (ENNReal.measurable_ofReal.comp (measurable_localRate.comp
      (measurable_pi_apply i).snd)).mul (hg.comp hZ)
  rw [lmarginal_singleton, lmarginal_singleton]
  funext x
  have hupd : ∀ y : Fin 2 × EuclideanSpace ℝ (Fin 2),
      (fun j => (Function.update x i y j).2) = Function.update (fun j => (x j).2) i y.2 := by
    intro y; funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  simp only [Function.update_self, hupd]
  exact lintegral_ite_label hπ₁ hσ hρ (hg.comp (measurable_update _))

/-- **The irreproducible discovery rate is the expected fraction of irreproducible findings.**
Let `π₁ ∈ [0, 1]`, `σ ≠ 0` and `ρ ∈ (-1, 1]`, and let the findings `i : ι` be independent, each
with the joint law `P` of its label `K i` and its latent pair `z i` under the copula mixture model
(as in `irreproducibleDiscoveryRate_posterior`). Then for every set `S` of findings, the
conditional expectation, given all the latent pairs `z`, of the fraction of irreproducible findings
in `S`, `#{i ∈ S | K i = 0} / #S`, is `IDR(S) = irreproducibleDiscoveryRate π₁ μ σ ρ z S`: for every
measurable weight `h` of the latent pairs,

  `E[#{i ∈ S | K i = 0} / #S * h(z)] = E[IDR(S) * h(z)]`. -/
theorem lintegral_fraction_irreproducible [Fintype ι] (hπ₁ : π₁ ∈ Set.Icc 0 1) (hσ : σ ≠ 0)
    (hρ : ρ ∈ Set.Ioc (-1) 1) (S : Finset ι)
    {h : (ι → EuclideanSpace ℝ (Fin 2)) → ENNReal} (hh : Measurable h) :
    let P : Measure (Fin 2 × EuclideanSpace ℝ (Fin 2)) :=
      ENNReal.ofReal (1 - π₁) • (Measure.dirac 0).prod (multivariateGaussian 0 1) +
        ENNReal.ofReal π₁ • (Measure.dirac 1).prod
          (multivariateGaussian !₂[μ, μ] !![σ ^ 2, ρ * σ ^ 2; ρ * σ ^ 2, σ ^ 2])
    ∫⁻ ω, ENNReal.ofReal (((S.filter fun i => (ω i).1 = 0).card : ℝ) / S.card) *
        h (fun j => (ω j).2) ∂Measure.pi (fun _ : ι => P) =
      ∫⁻ ω, ENNReal.ofReal (irreproducibleDiscoveryRate π₁ μ σ ρ (fun j => (ω j).2) S) *
        h (fun j => (ω j).2) ∂Measure.pi (fun _ : ι => P) := by
  intro P
  change ∫⁻ ω, _ ∂Measure.pi (fun _ : ι => labelledLaw π₁ μ σ ρ) =
    ∫⁻ ω, _ ∂Measure.pi (fun _ : ι => labelledLaw π₁ μ σ ρ)
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [irreproducibleDiscoveryRate]
  set c : ENNReal := ENNReal.ofReal ((S.card : ℝ)⁻¹)
  have hZ : Measurable fun ω : ι → Fin 2 × EuclideanSpace ℝ (Fin 2) => fun j => (ω j).2 := by
    fun_prop
  have hL : ∀ ω : ι → Fin 2 × EuclideanSpace ℝ (Fin 2),
      ENNReal.ofReal (((S.filter fun i => (ω i).1 = 0).card : ℝ) / S.card) *
        h (fun j => (ω j).2) =
      ∑ i ∈ S, (if (ω i).1 = 0 then c * h (fun j => (ω j).2) else 0) := by
    intro ω
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_div,
      ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp [c, div_eq_mul_inv]
  have hR : ∀ ω : ι → Fin 2 × EuclideanSpace ℝ (Fin 2),
      ENNReal.ofReal (irreproducibleDiscoveryRate π₁ μ σ ρ (fun j => (ω j).2) S) *
        h (fun j => (ω j).2) =
      ∑ i ∈ S, ENNReal.ofReal (irreproducibleDiscoveryRate π₁ μ σ ρ id {(ω i).2}) *
        (c * h (fun j => (ω j).2)) := by
    intro ω
    rw [irreproducibleDiscoveryRate_eq_sum_div, Finset.sum_div,
      ENNReal.ofReal_sum_of_nonneg fun i _ =>
        div_nonneg (irreproducibleDiscoveryRate_nonneg hπ₁ _) (Nat.cast_nonneg _), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [irreproducibleDiscoveryRate_singleton_eq_id, div_eq_mul_inv,
      ENNReal.ofReal_mul (irreproducibleDiscoveryRate_nonneg hπ₁ _), mul_assoc]
  simp_rw [hL, hR]
  rw [lintegral_finsetSum, lintegral_finsetSum]
  · exact Finset.sum_congr rfl fun i _ =>
      lintegral_pi_ite_label hπ₁ hσ hρ i (measurable_const.mul hh)
  · exact fun i _ => (ENNReal.measurable_ofReal.comp
      (measurable_localRate.comp (measurable_pi_apply i).snd)).mul
        (measurable_const.mul (hh.comp hZ))
  · exact fun i _ => Measurable.ite ((measurable_pi_apply i).fst (measurableSet_singleton 0))
      (measurable_const.mul (hh.comp hZ)) measurable_const

/-- **Selecting findings controls the expected fraction of irreproducible ones.** Let
`π₁ ∈ [0, 1]`, `σ ≠ 0` and `ρ ∈ (-1, 1]`, and let the findings `i : ι` be independent, each with
the joint law `P` of its label `K i` and its latent pair `z i` under the copula mixture model. If a
selection rule `sel`, which chooses a set of findings from their latent pairs (measurably), always
selects a set whose irreproducible discovery rate is at most `α`, then the expected fraction of
irreproducible findings in the selected set is at most `α`:

  `E[#{i ∈ sel z | K i = 0} / #(sel z)] ≤ α`. -/
theorem lintegral_fraction_irreproducible_le [Fintype ι] (hπ₁ : π₁ ∈ Set.Icc 0 1) (hσ : σ ≠ 0)
    (hρ : ρ ∈ Set.Ioc (-1) 1) {α : ℝ} (sel : (ι → EuclideanSpace ℝ (Fin 2)) → Finset ι)
    (hsel : ∀ s, MeasurableSet {z | sel z = s})
    (hα : ∀ z, irreproducibleDiscoveryRate π₁ μ σ ρ z (sel z) ≤ α) :
    let P : Measure (Fin 2 × EuclideanSpace ℝ (Fin 2)) :=
      ENNReal.ofReal (1 - π₁) • (Measure.dirac 0).prod (multivariateGaussian 0 1) +
        ENNReal.ofReal π₁ • (Measure.dirac 1).prod
          (multivariateGaussian !₂[μ, μ] !![σ ^ 2, ρ * σ ^ 2; ρ * σ ^ 2, σ ^ 2])
    ∫⁻ ω, ENNReal.ofReal
        ((((sel fun j => (ω j).2).filter fun i => (ω i).1 = 0).card : ℝ) /
          (sel fun j => (ω j).2).card) ∂Measure.pi (fun _ : ι => P) ≤ ENNReal.ofReal α := by
  intro P
  change ∫⁻ ω, _ ∂Measure.pi (fun _ : ι => labelledLaw π₁ μ σ ρ) ≤ _
  classical
  have := isProbabilityMeasure_labelledLaw (μ := μ) (σ := σ) (ρ := ρ) hπ₁
  have hZ : Measurable fun ω : ι → Fin 2 × EuclideanSpace ℝ (Fin 2) => fun j => (ω j).2 := by
    fun_prop
  have hind : ∀ s, Measurable fun z : ι → EuclideanSpace ℝ (Fin 2) =>
      if sel z = s then (1 : ENNReal) else 0 := fun s =>
    Measurable.ite (hsel s) measurable_const measurable_const
  have hfrac : ∀ ω : ι → Fin 2 × EuclideanSpace ℝ (Fin 2),
      ENNReal.ofReal ((((sel fun j => (ω j).2).filter fun i => (ω i).1 = 0).card : ℝ) /
        (sel fun j => (ω j).2).card) =
      ∑ s, ENNReal.ofReal (((s.filter fun i => (ω i).1 = 0).card : ℝ) / s.card) *
        (if sel (fun j => (ω j).2) = s then 1 else 0) := by
    intro ω
    simp
  have hidr : ∀ ω : ι → Fin 2 × EuclideanSpace ℝ (Fin 2),
      ENNReal.ofReal (irreproducibleDiscoveryRate π₁ μ σ ρ (fun j => (ω j).2)
        (sel fun j => (ω j).2)) =
      ∑ s, ENNReal.ofReal (irreproducibleDiscoveryRate π₁ μ σ ρ (fun j => (ω j).2) s) *
        (if sel (fun j => (ω j).2) = s then 1 else 0) := by
    intro ω
    simp
  have hmfrac : ∀ s : Finset ι, Measurable fun ω : ι → Fin 2 × EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal (((s.filter fun i => (ω i).1 = 0).card : ℝ) / s.card) := fun s => by
    simp_rw [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    refine ENNReal.measurable_ofReal.comp ((Finset.measurable_sum _ fun i _ => ?_).div_const _)
    exact Measurable.ite
      ((by fun_prop : Measurable fun ω : ι → Fin 2 × EuclideanSpace ℝ (Fin 2) => (ω i).1)
        (measurableSet_singleton 0)) measurable_const measurable_const
  have hmidr : ∀ s : Finset ι, Measurable fun ω : ι → Fin 2 × EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal (irreproducibleDiscoveryRate π₁ μ σ ρ (fun j => (ω j).2) s) := fun s =>
    ENNReal.measurable_ofReal.comp ((measurable_irreproducibleDiscoveryRate s).comp hZ)
  calc ∫⁻ ω, ENNReal.ofReal ((((sel fun j => (ω j).2).filter fun i => (ω i).1 = 0).card : ℝ) /
          (sel fun j => (ω j).2).card) ∂Measure.pi (fun _ : ι => labelledLaw π₁ μ σ ρ)
      = ∑ s, ∫⁻ ω, ENNReal.ofReal (((s.filter fun i => (ω i).1 = 0).card : ℝ) / s.card) *
          (if sel (fun j => (ω j).2) = s then 1 else 0)
            ∂Measure.pi (fun _ : ι => labelledLaw π₁ μ σ ρ) := by
        simp_rw [hfrac]
        exact lintegral_finsetSum _ fun s _ => (hmfrac s).mul ((hind s).comp hZ)
    _ = ∑ s, ∫⁻ ω, ENNReal.ofReal (irreproducibleDiscoveryRate π₁ μ σ ρ (fun j => (ω j).2) s) *
          (if sel (fun j => (ω j).2) = s then 1 else 0)
            ∂Measure.pi (fun _ : ι => labelledLaw π₁ μ σ ρ) :=
        Finset.sum_congr rfl fun s _ => lintegral_fraction_irreproducible hπ₁ hσ hρ s (hind s)
    _ = ∫⁻ ω, ENNReal.ofReal (irreproducibleDiscoveryRate π₁ μ σ ρ (fun j => (ω j).2)
          (sel fun j => (ω j).2)) ∂Measure.pi (fun _ : ι => labelledLaw π₁ μ σ ρ) := by
        simp_rw [hidr]
        exact (lintegral_finsetSum _ fun s _ => (hmidr s).mul ((hind s).comp hZ)).symm
    _ ≤ ∫⁻ _ω, ENNReal.ofReal α ∂Measure.pi (fun _ : ι => labelledLaw π₁ μ σ ρ) :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hα _)
    _ = ENNReal.ofReal α := by simp

end ExpectedFraction

end Domains.Biology.Omics.IrreproducibleDiscoveryRate
