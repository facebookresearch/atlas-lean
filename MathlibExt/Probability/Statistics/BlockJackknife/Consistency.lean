/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.BlockJackknife.Identity
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.StrongLaw

/-!
# Consistency of the scaled block-jackknife covariance

For iid block vectors with finite second moments, the scaled block-jackknife covariance
`B · V_jack` of the first `B` blocks converges almost surely to the covariance matrix of a
single block, entrywise and therefore in the matrix (product) topology, which every norm
on the finite-dimensional space `Matrix n n ℝ` induces. No consistency is claimed for
dependent blocks.

## Main results

* `BlockJackknife.card_smul_jackCov_apply`: for `B ≥ 2` blocks, `B · V_jack` is the
  unbiased sample covariance of the block vectors.
* `BlockJackknife.ae_tendsto_card_smul_jackCov_apply`: entrywise almost-sure consistency.
* `BlockJackknife.ae_tendsto_card_smul_jackCov`: consistency in the matrix topology.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), ch. 23.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Matrix Filter
open scoped Topology

namespace MathlibExt.Probability.Statistics.BlockJackknife

variable {n : Type*}

/-- Entry formula for `B ≥ 2` blocks: `(B · V_jack)_{ij} = B / (B - 1) · (B⁻¹ ∑_b z_{b,i} z_{b,j} - z̄_i z̄_j)`,
the unbiased sample covariance of the block vectors. -/
theorem card_smul_jackCov_apply {B : ℕ} (hB : 2 ≤ B) (z : Fin B → n → ℝ) (i j : n) :
    ((B : ℝ) • jackCov z) i j =
      (B : ℝ) / ((B : ℝ) - 1) *
        ((B : ℝ)⁻¹ * ∑ b, z b i * z b j - mean z i * mean z j) := by
  have hc : Fintype.card (Fin B) = B := Fintype.card_fin B
  have hB' : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have h0 : (B : ℝ) ≠ 0 := by linarith
  have h1 : (B : ℝ) - 1 ≠ 0 := by linarith
  rw [jackCov_eq (by rw [hc]; exact hB), hc]
  have hm : ∀ k, ∑ b, z b k = B * mean z k := by
    intro k
    simp only [mean, hc, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    field_simp
  simp only [Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply, Pi.sub_apply, smul_eq_mul]
  have hexp : ∑ b : Fin B, (z b i - mean z i) * (z b j - mean z j) =
      ∑ b, z b i * z b j - B * mean z i * mean z j := by
    have : ∀ b : Fin B, (z b i - mean z i) * (z b j - mean z j) =
        z b i * z b j - mean z j * z b i - mean z i * z b j + mean z i * mean z j := fun b => by ring
    simp only [this, sum_add_distrib, sum_sub_distrib, ← mul_sum, hm, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hexp]
  field_simp

variable [Finite n] {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Consistency of the scaled block-jackknife covariance, entrywise.** For iid block vectors
`Z 0, Z 1, …` (`iIndepFun` and identically distributed) with finite second moments in every
coordinate, almost surely `B · V_jack(Z 0, …, Z (B-1)) → Cov(Z 0)` entrywise as `B → ∞`. -/
theorem ae_tendsto_card_smul_jackCov_apply {Z : ℕ → Ω → n → ℝ} (hindep : iIndepFun Z μ)
    (hident : ∀ b, IdentDistrib (Z b) (Z 0) μ μ) (hL2 : ∀ i, MemLp (fun ω => Z 0 ω i) 2 μ) :
    ∀ᵐ ω ∂μ, ∀ i j, Tendsto (fun B : ℕ => ((B : ℝ) • jackCov (fun b : Fin B => Z b ω)) i j)
      atTop (𝓝 (cov[fun ω => Z 0 ω i, fun ω => Z 0 ω j; μ])) := by
  -- strong law for products and for coordinates
  have hP : ∀ i j, ∀ᵐ ω ∂μ, Tendsto (fun B : ℕ => (B : ℝ)⁻¹ • ∑ b ∈ range B, Z b ω i * Z b ω j)
      atTop (𝓝 (μ[fun ω => Z 0 ω i * Z 0 ω j])) := by
    intro i j
    have hg : Measurable fun v : n → ℝ => v i * v j := by fun_prop
    exact strong_law_ae (fun b ω => Z b ω i * Z b ω j) ((hL2 i).integrable_mul (hL2 j))
      (fun a b hab => (hindep.comp (fun _ v => v i * v j) fun _ => hg).indepFun hab)
      (fun b => (hident b).comp hg)
  have hM : ∀ i, ∀ᵐ ω ∂μ, Tendsto (fun B : ℕ => (B : ℝ)⁻¹ • ∑ b ∈ range B, Z b ω i)
      atTop (𝓝 (μ[fun ω => Z 0 ω i])) := by
    intro i
    have hg : Measurable fun v : n → ℝ => v i := by fun_prop
    exact strong_law_ae (fun b ω => Z b ω i) ((hL2 i).integrable one_le_two)
      (fun a b hab => (hindep.comp (fun _ v => v i) fun _ => hg).indepFun hab)
      (fun b => (hident b).comp hg)
  filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j => hP i j, ae_all_iff.2 hM]
    with ω h1 h2 i j
  have hlim : Tendsto (fun B : ℕ => (B : ℝ) / ((B : ℝ) - 1) *
      ((B : ℝ)⁻¹ • ∑ b ∈ range B, Z b ω i * Z b ω j -
        ((B : ℝ)⁻¹ • ∑ b ∈ range B, Z b ω i) * ((B : ℝ)⁻¹ • ∑ b ∈ range B, Z b ω j)))
      atTop (𝓝 (1 * (μ[fun ω => Z 0 ω i * Z 0 ω j] -
        μ[fun ω => Z 0 ω i] * μ[fun ω => Z 0 ω j]))) := by
    have hr : Tendsto (fun B : ℕ => (B : ℝ) / ((B : ℝ) - 1)) atTop (𝓝 1) := by
      simpa only [sub_eq_add_neg] using tendsto_natCast_div_add_atTop (-1 : ℝ)
    exact hr.mul ((h1 i j).sub ((h2 i).mul (h2 j)))
  have hcov : cov[fun ω => Z 0 ω i, fun ω => Z 0 ω j; μ] = 1 * (μ[fun ω => Z 0 ω i * Z 0 ω j] -
      μ[fun ω => Z 0 ω i] * μ[fun ω => Z 0 ω j]) := by
    rw [one_mul, covariance_eq_sub (hL2 i) (hL2 j)]; rfl
  rw [hcov]
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with B hB
  rw [card_smul_jackCov_apply hB]
  simp only [mean, Fintype.card_fin, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun b => Z b ω i * Z b ω j) B,
    Fin.sum_univ_eq_sum_range (fun b => Z b ω i) B, Fin.sum_univ_eq_sum_range (fun b => Z b ω j) B]

/-- **Consistency in the matrix topology**: almost surely `B · V_jack → Cov(Z 0)` as matrices. -/
theorem ae_tendsto_card_smul_jackCov {Z : ℕ → Ω → n → ℝ} (hindep : iIndepFun Z μ)
    (hident : ∀ b, IdentDistrib (Z b) (Z 0) μ μ) (hL2 : ∀ i, MemLp (fun ω => Z 0 ω i) 2 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun B : ℕ => (B : ℝ) • jackCov (fun b : Fin B => Z b ω)) atTop
      (𝓝 (Matrix.of fun i j => cov[fun ω => Z 0 ω i, fun ω => Z 0 ω j; μ])) := by
  filter_upwards [ae_tendsto_card_smul_jackCov_apply hindep hident hL2] with ω h
  exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => h i j

end MathlibExt.Probability.Statistics.BlockJackknife
