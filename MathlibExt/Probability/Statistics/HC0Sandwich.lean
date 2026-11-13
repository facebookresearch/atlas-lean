/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Topology.Instances.Matrix

/-!
# HC0 (Eicker-Huber-White) sandwich estimator consistency

The HC0 meat `Ω̂_n = n⁻¹ ∑_{i<n} û_i² * (x_i x_iᵀ)` with OLS residuals
`û_i = u_i - x_i ⬝ᵥ (β̂_n - β)`, and the sandwich `Q̂_n⁻¹ Ω̂_n Q̂_n⁻ᵀ`. The right factor is
the transpose of the bread inverse, as in a covariance sandwich; for a symmetric bread such
as the OLS Gram matrix it is the inverse itself.

CONDITIONAL RESULT: this file assumes a.s. consistency of the OLS estimator
(`β̂_n → β`, hypothesis `hβ`) and bread-inverse convergence (`hQinv`). It does not
prove them. An unconditional result requires
ST05.T01 (OLS consistency); discharge glue (ST05.T01 plus exogeneity
identifying the projection coefficient with `β`) can be added after
ST05.T01 merges.

Relation to the general GEE sandwich on main
(`MathlibExt/Probability/Statistics/Longitudinal/GEE/Sandwich.lean`,
`tendstoInMeasure_empirical_sandwichCovariance`): that result is convergence
in measure for a general estimating-equation sandwich in
continuous-linear-map form. It does not give the OLS HC0 matrix form, a.s.
convergence, or the residual cross-term bound proved here.

Limits of the meat are entrywise real-valued integrals: a matrix-valued Bochner integral
would need a normed group structure on `Matrix ι ι ℝ`, which Mathlib provides only as scoped
instances. Convergence needs no norm: `Matrix ι ι ℝ` is a function type with the product
topology, so the meat and the sandwich also converge as matrices (`tendsto_pi_nhds`); the
entrywise forms remain available.

## Main results

- `hc0Meat_entrywise_sub_le`: deterministic entrywise residual bound.
- `hc0Meat_matrix_tendsto_ae`: a.s. consistency of the HC0 meat as a matrix
  (entrywise form `hc0Meat_tendsto_ae`).
- `hc0Sandwich_matrix_tendsto_ae`: a.s. consistency of the HC0 sandwich as a matrix
  (entrywise form `hc0Sandwich_tendsto_ae`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace MathlibExt.Probability.Statistics.HC0Sandwich

/-- The HC0 meat `n⁻¹ ∑_{i<n} û_i² * (x_i x_iᵀ)` for a sample of `n`
regressor rows `x` and residuals `uhat`, with the outer product
`x_i x_iᵀ = Matrix.vecMulVec (x i) (x i)`. -/
noncomputable def hc0Meat {ι : Type*} [Fintype ι] (x : ℕ → ι → ℝ) (uhat : ℕ → ℝ)
    (n : ℕ) : Matrix ι ι ℝ :=
  (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, (uhat i ^ 2) • Matrix.vecMulVec (x i) (x i)

/-- Entrywise formula for the HC0 meat. -/
private lemma hc0Meat_entry {ι : Type*} [Fintype ι] (x : ℕ → ι → ℝ) (uhat : ℕ → ℝ)
    (n : ℕ) (a b : ι) :
    (hc0Meat x uhat n) a b
      = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (uhat i ^ 2) * ((x i) a * (x i) b) := by
  simp only [hc0Meat, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
    smul_eq_mul]

/-- Pointwise coordinate bound for the sup norm on `ι → ℝ`. -/
private lemma abs_apply_le_norm_pi {ι : Type*} [Fintype ι] (v : ι → ℝ) (a : ι) :
    |v a| ≤ ‖v‖ := by
  rw [← Real.norm_eq_abs]
  exact norm_le_pi_norm v a

/-- Crude sup-norm bound for the dot product. -/
private lemma abs_dotProduct_le_card {ι : Type*} [Fintype ι] (v w : ι → ℝ) :
    |v ⬝ᵥ w| ≤ (Fintype.card ι : ℝ) * ‖v‖ * ‖w‖ := by
  show |∑ c, v c * w c| ≤ _
  calc |∑ c, v c * w c| ≤ ∑ c, |v c * w c| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c : ι, (‖v‖ * ‖w‖) := Finset.sum_le_sum (fun c _ => by
        rw [abs_mul]
        exact mul_le_mul (abs_apply_le_norm_pi v c) (abs_apply_le_norm_pi w c)
          (abs_nonneg _) (norm_nonneg _))
    _ = (Fintype.card ι : ℝ) * ‖v‖ * ‖w‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Deterministic entrywise residual bound: replacing oracle errors `u` by
residuals `u - x ⬝ᵥ δ` moves entry `(a, b)` of the HC0 meat by at most
`2 * card * ‖δ‖ * (n⁻¹ ∑ ‖x_i‖³ |u_i|) + card² * ‖δ‖² * (n⁻¹ ∑ ‖x_i‖⁴)`. -/
theorem hc0Meat_entrywise_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {x : ℕ → ι → ℝ} {u : ℕ → ℝ} {δ : ι → ℝ} {n : ℕ} (hn : 0 < n) (a b : ι) :
    |(hc0Meat x (fun i => u i - (x i) ⬝ᵥ δ) n) a b -
        (hc0Meat x u n) a b| ≤
      2 * (Fintype.card ι : ℝ) * ‖δ‖ *
          ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ‖x i‖ ^ 3 * |u i|) +
        (Fintype.card ι : ℝ) ^ 2 * ‖δ‖ ^ 2 *
          ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ‖x i‖ ^ 4) := by
  have hdiff : (hc0Meat x (fun i => u i - (x i) ⬝ᵥ δ) n) a b - (hc0Meat x u n) a b
      = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        (((u i - (x i) ⬝ᵥ δ) ^ 2 * ((x i) a * (x i) b))
          - ((u i) ^ 2 * ((x i) a * (x i) b))) := by
    simp only [hc0Meat_entry, ← mul_sub, ← Finset.sum_sub_distrib]
  have hnR : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  have per_term : ∀ i : ℕ, |((u i - (x i) ⬝ᵥ δ) ^ 2 * ((x i) a * (x i) b)
        - (u i) ^ 2 * ((x i) a * (x i) b))|
      ≤ 2 * (Fintype.card ι : ℝ) * ‖δ‖ * (‖x i‖ ^ 3 * |u i|)
        + (Fintype.card ι : ℝ) ^ 2 * ‖δ‖ ^ 2 * ‖x i‖ ^ 4 := by
    intro i
    have hd : |(x i) ⬝ᵥ δ| ≤ (Fintype.card ι : ℝ) * ‖x i‖ * ‖δ‖ :=
      abs_dotProduct_le_card _ _
    have hX : |(x i) a * (x i) b| ≤ ‖x i‖ * ‖x i‖ := by
      rw [abs_mul]
      exact mul_le_mul (abs_apply_le_norm_pi _ _) (abs_apply_le_norm_pi _ _)
        (abs_nonneg _) (norm_nonneg _)
    have ealg : (u i - (x i) ⬝ᵥ δ) ^ 2 - (u i) ^ 2
        = -2 * (u i) * ((x i) ⬝ᵥ δ) + ((x i) ⬝ᵥ δ) ^ 2 := by ring
    have hdecomp : (u i - (x i) ⬝ᵥ δ) ^ 2 * ((x i) a * (x i) b)
          - (u i) ^ 2 * ((x i) a * (x i) b)
        = ((u i - (x i) ⬝ᵥ δ) ^ 2 - (u i) ^ 2) * ((x i) a * (x i) b) := by ring
    have habs1 : |-2 * (u i) * ((x i) ⬝ᵥ δ)| = 2 * |u i| * |(x i) ⬝ᵥ δ| := by
      have h2 : (|-2| : ℝ) = 2 := by norm_num
      rw [abs_mul, abs_mul, h2]
    have habs2 : |((x i) ⬝ᵥ δ) ^ 2| = |(x i) ⬝ᵥ δ| ^ 2 := by
      rw [pow_two, abs_mul, ← pow_two]
    have hcross : |-2 * (u i) * ((x i) ⬝ᵥ δ) + ((x i) ⬝ᵥ δ) ^ 2|
        ≤ 2 * |u i| * |(x i) ⬝ᵥ δ| + |(x i) ⬝ᵥ δ| ^ 2 := by
      calc |-2 * (u i) * ((x i) ⬝ᵥ δ) + ((x i) ⬝ᵥ δ) ^ 2|
          ≤ |-2 * (u i) * ((x i) ⬝ᵥ δ)| + |((x i) ⬝ᵥ δ) ^ 2| := abs_add_le _ _
        _ = 2 * |u i| * |(x i) ⬝ᵥ δ| + |(x i) ⬝ᵥ δ| ^ 2 := by rw [habs1, habs2]
    have hA : 2 * |u i| * |(x i) ⬝ᵥ δ| * (‖x i‖ * ‖x i‖)
        ≤ 2 * (Fintype.card ι : ℝ) * ‖δ‖ * (‖x i‖ ^ 3 * |u i|) := by
      have h := mul_le_mul_of_nonneg_right hd
        (show (0 : ℝ) ≤ 2 * |u i| * (‖x i‖ * ‖x i‖) by positivity)
      linear_combination h
    have hB : |(x i) ⬝ᵥ δ| ^ 2 * (‖x i‖ * ‖x i‖)
        ≤ (Fintype.card ι : ℝ) ^ 2 * ‖δ‖ ^ 2 * ‖x i‖ ^ 4 := by
      have hsq : |(x i) ⬝ᵥ δ| ^ 2 ≤ ((Fintype.card ι : ℝ) * ‖x i‖ * ‖δ‖) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hd 2
      have h := mul_le_mul_of_nonneg_right hsq
        (show (0 : ℝ) ≤ ‖x i‖ * ‖x i‖ by positivity)
      linear_combination h
    rw [hdecomp, ealg, abs_mul]
    refine (mul_le_mul hcross hX (abs_nonneg _) (by positivity)).trans ?_
    have hfin := add_le_add hA hB
    linear_combination hfin
  rw [hdiff, abs_mul, abs_of_nonneg hnR]
  have hsum : |∑ i ∈ Finset.range n,
        (((u i - (x i) ⬝ᵥ δ) ^ 2 * ((x i) a * (x i) b))
          - ((u i) ^ 2 * ((x i) a * (x i) b)))|
      ≤ ∑ i ∈ Finset.range n, (2 * (Fintype.card ι : ℝ) * ‖δ‖ * (‖x i‖ ^ 3 * |u i|)
        + (Fintype.card ι : ℝ) ^ 2 * ‖δ‖ ^ 2 * ‖x i‖ ^ 4) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => per_term i))
  have hfin : (n : ℝ)⁻¹ * |∑ i ∈ Finset.range n,
        (((u i - (x i) ⬝ᵥ δ) ^ 2 * ((x i) a * (x i) b))
          - ((u i) ^ 2 * ((x i) a * (x i) b)))|
      ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (2 * (Fintype.card ι : ℝ) * ‖δ‖ * (‖x i‖ ^ 3 * |u i|)
        + (Fintype.card ι : ℝ) ^ 2 * ‖δ‖ ^ 2 * ‖x i‖ ^ 4) :=
    mul_le_mul_of_nonneg_left hsum hnR
  have heq : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (2 * (Fintype.card ι : ℝ) * ‖δ‖ * (‖x i‖ ^ 3 * |u i|)
        + (Fintype.card ι : ℝ) ^ 2 * ‖δ‖ ^ 2 * ‖x i‖ ^ 4)
      = 2 * (Fintype.card ι : ℝ) * ‖δ‖ *
          ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ‖x i‖ ^ 3 * |u i|) +
        (Fintype.card ι : ℝ) ^ 2 * ‖δ‖ ^ 2 *
          ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ‖x i‖ ^ 4) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
  rw [heq] at hfin
  exact hfin

/-- A.s. consistency of the HC0 meat, entrywise: under iid `(x_i, u_i)` pairs,
the moment conditions `E ‖x‖⁴ < ∞`, `E ‖x‖² u² < ∞`, and a.s. consistency of
`β̂_n`, each entry of the residual meat converges a.s. to
`Ω a b = E[u² * x_a * x_b]`. The oracle meat entries are integrable because
`|u² * x_a * x_b| ≤ ‖x‖² u²`. -/
theorem hc0Meat_tendsto_ae {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {x : ℕ → Ω → (ι → ℝ)} {u : ℕ → Ω → ℝ}
    {β : ι → ℝ} {βhat : ℕ → Ω → (ι → ℝ)}
    (hJoint : iIndepFun (fun i ω => (x i ω, u i ω)) μ)
    (hIdent : ∀ i, IdentDistrib (fun ω => (x i ω, u i ω))
      (fun ω => (x 0 ω, u 0 ω)) μ μ)
    (hMom4 : Integrable (fun ω => ‖x 0 ω‖ ^ 4) μ)
    (hMom2 : Integrable (fun ω => ‖x 0 ω‖ ^ 2 * (u 0 ω) ^ 2) μ)
    (hβ : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n : ℕ => βhat n ω) Filter.atTop (nhds β))
    (a b : ι) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => (hc0Meat (fun i => x i ω)
        (fun i => u i ω - (x i ω) ⬝ᵥ (βhat n ω - β)) n) a b)
      Filter.atTop
      (nhds (∫ ω, (u 0 ω) ^ 2 * (x 0 ω) a * (x 0 ω) b ∂μ)) := by
  have hφm : Measurable (fun p : (ι → ℝ) × ℝ => (p.2) ^ 2 * p.1 a * p.1 b) :=
    ((measurable_snd.pow_const 2).mul ((measurable_pi_apply a).comp measurable_fst)).mul
      ((measurable_pi_apply b).comp measurable_fst)
  have hφ3 : Measurable (fun p : (ι → ℝ) × ℝ => ‖p.1‖ ^ 3 * |p.2|) :=
    ((measurable_fst.norm).pow_const 3).mul measurable_snd.abs
  have hφ4 : Measurable (fun p : (ι → ℝ) × ℝ => ‖p.1‖ ^ 4) :=
    (measurable_fst.norm).pow_const 4
  have hIntMeat : Integrable (fun ω => (u 0 ω) ^ 2 * (x 0 ω) a * (x 0 ω) b) μ := by
    have hmeas : AEStronglyMeasurable (fun ω => (u 0 ω) ^ 2 * (x 0 ω) a * (x 0 ω) b) μ :=
      (hφm.comp_aemeasurable (hIdent 0).aemeasurable_fst).aestronglyMeasurable
    refine Integrable.mono' hMom2 hmeas (Filter.Eventually.of_forall fun ω => ?_)
    have hab : |(x 0 ω) a| * |(x 0 ω) b| ≤ ‖x 0 ω‖ * ‖x 0 ω‖ :=
      mul_le_mul (abs_apply_le_norm_pi _ _) (abs_apply_le_norm_pi _ _)
        (abs_nonneg _) (norm_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (u 0 ω))]
    calc (u 0 ω) ^ 2 * |(x 0 ω) a| * |(x 0 ω) b|
        = (u 0 ω) ^ 2 * (|(x 0 ω) a| * |(x 0 ω) b|) := by ring
      _ ≤ (u 0 ω) ^ 2 * (‖x 0 ω‖ * ‖x 0 ω‖) :=
        mul_le_mul_of_nonneg_left hab (sq_nonneg _)
      _ = ‖x 0 ω‖ ^ 2 * (u 0 ω) ^ 2 := by ring
  have hint3 : Integrable (fun ω => ‖x 0 ω‖ ^ 3 * |u 0 ω|) μ := by
    have hmeas : AEStronglyMeasurable (fun ω => ‖x 0 ω‖ ^ 3 * |u 0 ω|) μ := by
      have hgm : AEStronglyMeasurable
          (fun ω => ‖x 0 ω‖ ^ 4 * (‖x 0 ω‖ ^ 2 * (u 0 ω) ^ 2)) μ :=
        hMom4.aestronglyMeasurable.mul hMom2.aestronglyMeasurable
      have hsqrt : AEStronglyMeasurable
          (fun ω => √(‖x 0 ω‖ ^ 4 * (‖x 0 ω‖ ^ 2 * (u 0 ω) ^ 2))) μ :=
        Real.continuous_sqrt.comp_aestronglyMeasurable hgm
      have heq : (fun ω => ‖x 0 ω‖ ^ 3 * |u 0 ω|)
          = fun ω => √(‖x 0 ω‖ ^ 4 * (‖x 0 ω‖ ^ 2 * (u 0 ω) ^ 2)) := by
        funext ω
        have e : ‖x 0 ω‖ ^ 4 * (‖x 0 ω‖ ^ 2 * (u 0 ω) ^ 2)
            = (‖x 0 ω‖ ^ 3 * |u 0 ω|) ^ 2 := by rw [mul_pow, sq_abs]; ring
        rw [e, Real.sqrt_sq (by positivity)]
      rw [heq]
      exact hsqrt
    have hbound : ∀ᵐ ω ∂μ, ‖‖x 0 ω‖ ^ 3 * |u 0 ω|‖
        ≤ ‖x 0 ω‖ ^ 4 + ‖x 0 ω‖ ^ 2 * (u 0 ω) ^ 2 := by
      refine Filter.Eventually.of_forall (fun ω => ?_)
      have h2 := two_mul_le_add_pow_two (‖x 0 ω‖ ^ 2) (‖x 0 ω‖ * |u 0 ω|)
      have e1 : (‖x 0 ω‖ * |u 0 ω|) ^ 2 = ‖x 0 ω‖ ^ 2 * (u 0 ω) ^ 2 := by
        rw [mul_pow, sq_abs]
      have e2 : (‖x 0 ω‖ ^ 2) ^ 2 = ‖x 0 ω‖ ^ 4 := by ring
      rw [e1, e2] at h2
      have hnn : (0 : ℝ) ≤ ‖x 0 ω‖ ^ 4 + ‖x 0 ω‖ ^ 2 * (u 0 ω) ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith [h2, hnn]
    exact Integrable.mono' (hMom4.add hMom2) hmeas hbound
  have horc : ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        ((u i ω) ^ 2 * (x i ω) a * (x i ω) b))
      Filter.atTop
      (nhds (∫ ω, (u 0 ω) ^ 2 * (x 0 ω) a * (x 0 ω) b ∂μ)) :=
    strong_law_ae (fun i ω => (u i ω) ^ 2 * (x i ω) a * (x i ω) b) hIntMeat
      (fun i j hij => (hJoint.indepFun hij).comp hφm hφm)
      (fun i => (hIdent i).comp hφm)
  have h3 : ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, (‖x i ω‖ ^ 3 * |u i ω|))
      Filter.atTop
      (nhds (∫ ω, ‖x 0 ω‖ ^ 3 * |u 0 ω| ∂μ)) :=
    strong_law_ae (fun i ω => ‖x i ω‖ ^ 3 * |u i ω|) hint3
      (fun i j hij => (hJoint.indepFun hij).comp hφ3 hφ3)
      (fun i => (hIdent i).comp hφ3)
  have h4 : ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, (‖x i ω‖ ^ 4))
      Filter.atTop
      (nhds (∫ ω, ‖x 0 ω‖ ^ 4 ∂μ)) :=
    strong_law_ae (fun i ω => ‖x i ω‖ ^ 4) hMom4
      (fun i j hij => (hJoint.indepFun hij).comp hφ4 hφ4)
      (fun i => (hIdent i).comp hφ4)
  filter_upwards [horc, h3, h4, hβ] with ω horc h3 h4 hβω
  have hδ0 : Filter.Tendsto (fun n : ℕ => βhat n ω - β) Filter.atTop (nhds 0) :=
    tendsto_sub_nhds_zero_iff.mpr hβω
  have hδ : Filter.Tendsto (fun n : ℕ => ‖βhat n ω - β‖) Filter.atTop (nhds 0) := by
    simpa using hδ0.norm
  have horc' : Filter.Tendsto
      (fun n : ℕ => (hc0Meat (fun i => x i ω) (fun i => u i ω) n) a b)
      Filter.atTop
      (nhds (∫ ω, (u 0 ω) ^ 2 * (x 0 ω) a * (x 0 ω) b ∂μ)) := by
    refine horc.congr (fun n => ?_)
    rw [hc0Meat_entry, smul_eq_mul]
    show (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ((u i ω) ^ 2 * (x i ω) a * (x i ω) b)
      = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ((u i ω) ^ 2 * ((x i ω) a * (x i ω) b))
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h3' : Filter.Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ‖x i ω‖ ^ 3 * |u i ω|)
      Filter.atTop (nhds (∫ ω, ‖x 0 ω‖ ^ 3 * |u 0 ω| ∂μ)) :=
    h3.congr (fun n => smul_eq_mul _ _)
  have h4' : Filter.Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ‖x i ω‖ ^ 4)
      Filter.atTop (nhds (∫ ω, ‖x 0 ω‖ ^ 4 ∂μ)) :=
    h4.congr (fun n => smul_eq_mul _ _)
  have hδ2 : Filter.Tendsto (fun n : ℕ => ‖βhat n ω - β‖ ^ 2) Filter.atTop (nhds 0) := by
    simpa using hδ.pow 2
  have ht1 : Filter.Tendsto (fun n : ℕ => 2 * (Fintype.card ι : ℝ) * ‖βhat n ω - β‖
      * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ‖x i ω‖ ^ 3 * |u i ω|))
      Filter.atTop (nhds 0) := by
    have h := (tendsto_const_nhds (x := (2 : ℝ) * (Fintype.card ι : ℝ))).mul (hδ.mul h3')
    have hlim : (2 : ℝ) * (Fintype.card ι : ℝ)
        * (0 * (∫ ω, ‖x 0 ω‖ ^ 3 * |u 0 ω| ∂μ)) = 0 := by ring
    rw [hlim] at h
    refine h.congr (fun n => by ring)
  have ht2 : Filter.Tendsto (fun n : ℕ => (Fintype.card ι : ℝ) ^ 2 * ‖βhat n ω - β‖ ^ 2
      * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ‖x i ω‖ ^ 4))
      Filter.atTop (nhds 0) := by
    have h := (tendsto_const_nhds (x := (Fintype.card ι : ℝ) ^ 2)).mul (hδ2.mul h4')
    have hlim : (Fintype.card ι : ℝ) ^ 2 * (0 * (∫ ω, ‖x 0 ω‖ ^ 4 ∂μ)) = 0 := by ring
    rw [hlim] at h
    refine h.congr (fun n => by ring)
  have hB : Filter.Tendsto (fun n : ℕ =>
      (2 * (Fintype.card ι : ℝ) * ‖βhat n ω - β‖
        * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ‖x i ω‖ ^ 3 * |u i ω|)
      + (Fintype.card ι : ℝ) ^ 2 * ‖βhat n ω - β‖ ^ 2
        * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ‖x i ω‖ ^ 4)))
      Filter.atTop (nhds 0) := by
    have h := ht1.add ht2
    rwa [add_zero] at h
  have hev : ∀ᶠ n : ℕ in Filter.atTop, ‖(hc0Meat (fun i => x i ω)
        (fun i => u i ω - (x i ω) ⬝ᵥ (βhat n ω - β)) n) a b
        - (hc0Meat (fun i => x i ω) (fun i => u i ω) n) a b‖
      ≤ 2 * (Fintype.card ι : ℝ) * ‖βhat n ω - β‖
          * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ‖x i ω‖ ^ 3 * |u i ω|)
        + (Fintype.card ι : ℝ) ^ 2 * ‖βhat n ω - β‖ ^ 2
          * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ‖x i ω‖ ^ 4) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    rw [Real.norm_eq_abs]
    exact hc0Meat_entrywise_sub_le hn a b
  have hdiff : Filter.Tendsto (fun n : ℕ =>
      (hc0Meat (fun i => x i ω) (fun i => u i ω - (x i ω) ⬝ᵥ (βhat n ω - β)) n) a b
      - (hc0Meat (fun i => x i ω) (fun i => u i ω) n) a b)
      Filter.atTop (nhds 0) :=
    squeeze_zero_norm' hev hB
  have hfin := hdiff.add horc'
  rw [zero_add] at hfin
  exact hfin.congr (fun n => sub_add_cancel _ _)

/-- A.s. consistency of the HC0 sandwich `Q̂_n⁻¹ Ω̂_n Q̂_n⁻ᵀ`, entrywise, from entrywise
a.s. convergence of the bread inverse and the meat. The right factor is the transpose of
the bread inverse, so no symmetry of the bread is assumed. -/
theorem hc0Sandwich_tendsto_ae {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Qhat : ℕ → Ω → Matrix ι ι ℝ} {Q Ωm : Matrix ι ι ℝ}
    {meat : ℕ → Ω → Matrix ι ι ℝ}
    (hQinv : ∀ a b : ι, ∀ᵐ ω ∂μ, Filter.Tendsto (fun n : ℕ => ((Qhat n ω)⁻¹) a b)
      Filter.atTop (nhds (Q⁻¹ a b)))
    (hMeat : ∀ a b : ι, ∀ᵐ ω ∂μ, Filter.Tendsto (fun n : ℕ => (meat n ω) a b)
      Filter.atTop (nhds (Ωm a b)))
    (a b : ι) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => ((Qhat n ω)⁻¹ * meat n ω * ((Qhat n ω)⁻¹)ᵀ) a b)
      Filter.atTop (nhds ((Q⁻¹ * Ωm * (Q⁻¹)ᵀ) a b)) := by
  have h1 : ∀ᵐ ω ∂μ, ∀ c : ι, Filter.Tendsto (fun n : ℕ => ((Qhat n ω)⁻¹) a c)
      Filter.atTop (nhds ((Q⁻¹) a c)) :=
    ae_all_iff.mpr (fun c => hQinv a c)
  have h2 : ∀ᵐ ω ∂μ, ∀ d c : ι, Filter.Tendsto (fun n : ℕ => (meat n ω) d c)
      Filter.atTop (nhds (Ωm d c)) :=
    ae_all_iff.mpr (fun d => ae_all_iff.mpr (fun c => hMeat d c))
  have h3 : ∀ᵐ ω ∂μ, ∀ c : ι, Filter.Tendsto (fun n : ℕ => ((Qhat n ω)⁻¹) b c)
      Filter.atTop (nhds ((Q⁻¹) b c)) :=
    ae_all_iff.mpr (fun c => hQinv b c)
  filter_upwards [h1, h2, h3] with ω h1 h2 h3
  have hinner : ∀ c : ι, Filter.Tendsto
      (fun n : ℕ => (∑ d : ι, ((Qhat n ω)⁻¹) a d * (meat n ω) d c)
        * ((Qhat n ω)⁻¹) b c)
      Filter.atTop
      (nhds ((∑ d : ι, (Q⁻¹) a d * Ωm d c) * (Q⁻¹) b c)) := by
    intro c
    exact (tendsto_finsetSum Finset.univ (fun d _ => (h1 d).mul (h2 d c))).mul
      (h3 c)
  have houter : Filter.Tendsto
      (fun n : ℕ => ∑ c : ι, (∑ d : ι, ((Qhat n ω)⁻¹) a d * (meat n ω) d c)
        * ((Qhat n ω)⁻¹) b c)
      Filter.atTop
      (nhds (∑ c : ι, (∑ d : ι, (Q⁻¹) a d * Ωm d c) * (Q⁻¹) b c)) :=
    tendsto_finsetSum Finset.univ (fun c _ => hinner c)
  simpa only [Matrix.mul_apply, Matrix.transpose_apply] using houter

/-- A.s. consistency of the HC0 meat as a matrix: under the hypotheses of
`hc0Meat_tendsto_ae`, the residual meat converges a.s. in `Matrix ι ι ℝ` (product
topology) to the matrix `Ω` of entries `E[u² * x_a * x_b]`. -/
theorem hc0Meat_matrix_tendsto_ae {ι : Type*} [Fintype ι] [Nonempty ι]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {x : ℕ → Ω → (ι → ℝ)} {u : ℕ → Ω → ℝ}
    {β : ι → ℝ} {βhat : ℕ → Ω → (ι → ℝ)}
    (hJoint : iIndepFun (fun i ω => (x i ω, u i ω)) μ)
    (hIdent : ∀ i, IdentDistrib (fun ω => (x i ω, u i ω))
      (fun ω => (x 0 ω, u 0 ω)) μ μ)
    (hMom4 : Integrable (fun ω => ‖x 0 ω‖ ^ 4) μ)
    (hMom2 : Integrable (fun ω => ‖x 0 ω‖ ^ 2 * (u 0 ω) ^ 2) μ)
    (hβ : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n : ℕ => βhat n ω) Filter.atTop (nhds β)) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => hc0Meat (fun i => x i ω)
        (fun i => u i ω - (x i ω) ⬝ᵥ (βhat n ω - β)) n)
      Filter.atTop
      (nhds (Matrix.of fun a b => ∫ ω, (u 0 ω) ^ 2 * (x 0 ω) a * (x 0 ω) b ∂μ)) := by
  classical
  have h : ∀ᵐ ω ∂μ, ∀ a b : ι, Filter.Tendsto
      (fun n : ℕ => (hc0Meat (fun i => x i ω)
        (fun i => u i ω - (x i ω) ⬝ᵥ (βhat n ω - β)) n) a b)
      Filter.atTop
      (nhds (∫ ω, (u 0 ω) ^ 2 * (x 0 ω) a * (x 0 ω) b ∂μ)) :=
    ae_all_iff.mpr fun a => ae_all_iff.mpr fun b =>
      hc0Meat_tendsto_ae hJoint hIdent hMom4 hMom2 hβ a b
  filter_upwards [h] with ω hω
  exact tendsto_pi_nhds.mpr fun a => tendsto_pi_nhds.mpr fun b => hω a b

/-- A.s. consistency of the HC0 sandwich as a matrix: if the bread inverse and the meat
converge a.s. in `Matrix ι ι ℝ` (product topology), then
`Q̂_n⁻¹ Ω̂_n Q̂_n⁻ᵀ → Q⁻¹ Ωm Q⁻ᵀ` a.s. -/
theorem hc0Sandwich_matrix_tendsto_ae {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Qhat : ℕ → Ω → Matrix ι ι ℝ} {Q Ωm : Matrix ι ι ℝ}
    {meat : ℕ → Ω → Matrix ι ι ℝ}
    (hQinv : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n : ℕ => (Qhat n ω)⁻¹) Filter.atTop (nhds Q⁻¹))
    (hMeat : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n : ℕ => meat n ω) Filter.atTop (nhds Ωm)) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => (Qhat n ω)⁻¹ * meat n ω * ((Qhat n ω)⁻¹)ᵀ)
      Filter.atTop (nhds (Q⁻¹ * Ωm * (Q⁻¹)ᵀ)) := by
  have hentry : ∀ a b : ι, ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => ((Qhat n ω)⁻¹ * meat n ω * ((Qhat n ω)⁻¹)ᵀ) a b)
      Filter.atTop (nhds ((Q⁻¹ * Ωm * (Q⁻¹)ᵀ) a b)) :=
    hc0Sandwich_tendsto_ae
      (fun a b => hQinv.mono fun _ h => tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h a) b)
      (fun a b => hMeat.mono fun _ h => tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h a) b)
  filter_upwards [ae_all_iff.mpr fun a => ae_all_iff.mpr fun b => hentry a b] with ω hω
  exact tendsto_pi_nhds.mpr fun a => tendsto_pi_nhds.mpr fun b => hω a b

end MathlibExt.Probability.Statistics.HC0Sandwich
