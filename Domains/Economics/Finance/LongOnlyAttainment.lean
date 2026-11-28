/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Order.Filter.Extr
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Order.Compact
public import MathlibExt.Probability.Statistics.CovarianceMatrix

/-!
# Long-only target-slice attainment

A nonempty long-only target-return slice `targetSlice μv m` (nonnegative,
fully invested weights with `μv ⬝ᵥ w = m`) attains the minimum of the
quadratic form `w ⬝ᵥ (Sigma *ᵥ w)` (`exists_isMinOn_targetSlice`). No
definiteness of `Sigma` is needed. With `Sigma` the covariance matrix of
square-integrable returns and `μv` their expectations, this is attainment
of the covariance quadratic form (`exists_isMinOn_targetSlice_covariance`,
`exists_isMinOn_covMatrix_targetSlice`). No uniqueness, KKT, or
calibration claim is made.
-/

@[expose] public section

open Matrix

namespace MathlibExt.Probability.Finance.LongOnlyAttainment

/-- Long-only target-return slice: fully invested nonnegative weights whose
expected return `μv ⬝ᵥ w` equals the target `m`. -/
def targetSlice {ι : Type*} [Fintype ι] (μv : ι → ℝ) (m : ℝ) :
    Set (ι → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ μv ⬝ᵥ w = m}

/-- A nonempty long-only target-return slice attains the minimum of the
quadratic form `w ⬝ᵥ (Sigma *ᵥ w)`. No definiteness hypothesis on `Sigma`
is needed: the slice is compact and the objective is continuous. -/
theorem exists_isMinOn_targetSlice {ι : Type*} [Fintype ι]
    (Sigma : Matrix ι ι ℝ) (μv : ι → ℝ) (m : ℝ)
    (hW : (targetSlice μv m).Nonempty) :
    ∃ w ∈ targetSlice μv m,
      IsMinOn (fun w => w ⬝ᵥ (Sigma *ᵥ w)) (targetSlice μv m) w := by
  have hdot : Continuous fun w : ι → ℝ => μv ⬝ᵥ w := by
    simp only [dotProduct]
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)
  have hclosed : IsClosed (targetSlice μv m) := by
    have h1 : IsClosed {w : ι → ℝ | ∀ i, 0 ≤ w i} := by
      rw [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed {w : ι → ℝ | ∑ i, w i = 1} :=
      isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    have h3 : IsClosed {w : ι → ℝ | μv ⬝ᵥ w = m} :=
      isClosed_eq hdot continuous_const
    have heq : targetSlice μv m
        = {w : ι → ℝ | ∀ i, 0 ≤ w i} ∩ {w : ι → ℝ | ∑ i, w i = 1}
          ∩ {w : ι → ℝ | μv ⬝ᵥ w = m} := by
      ext w
      simp only [targetSlice, Set.mem_ofPred_eq, Set.mem_inter_iff]
      exact and_assoc.symm
    rw [heq]
    exact (h1.inter h2).inter h3
  have hsub : targetSlice μv m ⊆ {x : ι → ℝ | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1} := by
    intro w hw i
    obtain ⟨hge, hsum, -⟩ :
        (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ μv ⬝ᵥ w = m := hw
    refine Set.mem_Icc.mpr ⟨hge i, ?_⟩
    calc w i ≤ ∑ j, w j :=
            Finset.single_le_sum (fun j _ => hge j) (Finset.mem_univ i)
        _ = 1 := hsum
  have hcompact : IsCompact (targetSlice μv m) :=
    (isCompact_pi_infinite fun _ => isCompact_Icc).of_isClosed_subset hclosed hsub
  have hobj : Continuous fun w : ι → ℝ => w ⬝ᵥ (Sigma *ᵥ w) := by
    simp only [dotProduct]
    have hmv : ∀ i, Continuous fun w : ι → ℝ => (Sigma *ᵥ w) i := fun i => by
      simp only [Matrix.mulVec_apply_eq_sum]
      exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul (hmv i)
  exact hcompact.exists_isMinOn hW hobj.continuousOn

/-- Covariance form: for square-integrable returns `R` under a probability measure `μ`, with
expectations `μv i = ∫ ω, R i ω ∂μ`, a nonempty long-only target slice attains the
minimum of the covariance quadratic form. The matrix is spelled with
Mathlib `covariance`, entrywise the native `covMatrix`. -/
theorem exists_isMinOn_targetSlice_covariance {ι : Type*} [Fintype ι]
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (R : ι → Ω → ℝ)
    (hR : ∀ i, MeasureTheory.MemLp (R i) 2 μ) (m : ℝ)
    (hW : (targetSlice (fun i => ∫ ω, R i ω ∂μ) m).Nonempty) :
    ∃ w ∈ targetSlice (fun i => ∫ ω, R i ω ∂μ) m,
      IsMinOn (fun w => w ⬝ᵥ ((Matrix.of fun i j =>
        ProbabilityTheory.covariance (R i) (R j) μ) *ᵥ w))
        (targetSlice (fun i => ∫ ω, R i ω ∂μ) m) w := by
  have _ := hR
  exact exists_isMinOn_targetSlice _ _ _ hW

/-- Covariance-matrix form naming the native `covMatrix`: for square-integrable returns
`R` under a probability measure `μ`, with expectations as the target means, a nonempty
long-only target slice attains the minimum of `w ⬝ᵥ (covMatrix μ R *ᵥ w)`. -/
theorem exists_isMinOn_covMatrix_targetSlice {ι : Type*} [Fintype ι]
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (R : ι → Ω → ℝ)
    (hR : ∀ i, MeasureTheory.MemLp (R i) 2 μ) (m : ℝ)
    (hW : (targetSlice (fun i => ∫ ω, R i ω ∂μ) m).Nonempty) :
    ∃ w ∈ targetSlice (fun i => ∫ ω, R i ω ∂μ) m,
      IsMinOn (fun w => w ⬝ᵥ
        (MathlibExt.Probability.Finance.PortfolioVariance.covMatrix μ R *ᵥ w))
        (targetSlice (fun i => ∫ ω, R i ω ∂μ) m) w := by
  exact MathlibExt.Probability.Finance.LongOnlyAttainment.exists_isMinOn_targetSlice_covariance
    μ R hR m hW

end MathlibExt.Probability.Finance.LongOnlyAttainment
