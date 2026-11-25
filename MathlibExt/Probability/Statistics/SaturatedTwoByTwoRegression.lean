/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteProbability
public import MathlibExt.Probability.Distributions.CochranIndependence

import Mathlib.Tactic

@[expose] public section

open Matrix


/-!
# The saturated two-by-two regression and the four-cell mean contrast

Observations `ι` fall into four cells by two binary maps `d t : ι → Bool`. The saturated
regression `y i = β₀ + β₁ D i + β₂ T i + β₃ (D i * T i) + e i`, where `D i` and `T i` are the
`0/1` indicators of `d i` and `t i`, has one coefficient per cell. When all four cells are
populated its least-squares coefficients are read off the cell means `m_ab`: `β₀ = m₀₀`,
`β₁ = m₁₀ - m₀₀`, `β₂ = m₀₁ - m₀₀`, and the interaction `β₃ = (m₁₁ - m₁₀) - (m₀₁ - m₀₀)` is the
four-cell mean contrast. In a difference-in-differences design (`d` the treated group, `t` the
post period) `β₃` is the change in the treated group's mean minus the change in the control
group's mean.

These are numerical identities of the least-squares fit; no error model is assumed. Whether
the contrast identifies a treatment effect is a separate question (parallel trends and no
anticipation, `MathlibExt.Probability.Statistics.DifferenceInDifferences`). Cell means are
Atlas's sample group means `ProbabilityTheory.groupMean`, which take the junk value `0` on an
empty cell. Populated cells are exactly the full-column-rank condition
(`isUnit_gram_twoByTwoDesign_iff`). Without it the cell-mean coefficients still solve the
normal equations, but the solution is not unique, and `olsEstimator` takes its junk value.

## Main results

* `twoByTwoDesign_mulVec_cellMeanCoefficients`: at the cell-mean coefficients every fitted
  value is the mean of the observation's cell.
* `gram_mulVec_cellMeanCoefficients`: the cell-mean coefficients solve the normal equations,
  for every sample.
* `isUnit_gram_twoByTwoDesign_iff`: `Xᵀ X` is invertible iff all four cells are populated.
* `twoByTwoDesign_normal_eq_iff`, `olsEstimator_twoByTwoDesign`: with populated cells the
  cell-mean coefficients are the unique least-squares solution and the OLS estimate.
* `olsEstimator_twoByTwoDesign_interaction`: the OLS interaction coefficient is the four-cell
  mean contrast.

## References

* J. D. Angrist and J.-S. Pischke, *Mostly Harmless Econometrics*, Princeton University Press
  (2009), §3.1.4 (saturated models with two binary regressors and their interaction) and
  §5.2.1 (the regression form of difference-in-differences).
* J. M. Wooldridge, *Introductory Econometrics: A Modern Approach*, §13.2 (difference-in-
  differences with pooled cross sections).
-/

namespace MathlibExt.Probability.Statistics.SaturatedTwoByTwoRegression

open ProbabilityTheory MathlibExt.Probability.Statistics.LinearModel

/-- The design matrix of the saturated two-by-two regression
`y i = β₀ + β₁ D i + β₂ T i + β₃ (D i * T i) + e i`: row `i` is `(1, D i, T i, D i * T i)`,
where `D i` is `1` if `d i` holds and `0` otherwise, and `T i` is the same for `t i`. In a
difference-in-differences design `d` marks the treated group and `t` the post period. -/
noncomputable def twoByTwoDesign {ι : Type*} (d t : ι → Bool) : Matrix ι (Fin 4) ℝ :=
  Matrix.of fun i => ![1, if d i then 1 else 0, if t i then 1 else 0,
    (if d i then 1 else 0) * (if t i then 1 else 0)]

/-- The coefficients read off the four cell means `m_ab = groupMean (fun i => (d i, t i)) y (a, b)`
(`1` for `true`): the intercept `m₀₀`, the effect of `d` at `t = false`, `m₁₀ - m₀₀`, the effect
of `t` at `d = false`, `m₀₁ - m₀₀`, and the interaction, the four-cell mean contrast
`(m₁₁ - m₁₀) - (m₀₁ - m₀₀)`. An empty cell enters with its junk mean `0`. -/
noncomputable def cellMeanCoefficients {ι : Type*} [Fintype ι] (d t : ι → Bool) (y : ι → ℝ) :
    Fin 4 → ℝ :=
  ![groupMean (fun i => (d i, t i)) y (false, false),
    groupMean (fun i => (d i, t i)) y (true, false) -
      groupMean (fun i => (d i, t i)) y (false, false),
    groupMean (fun i => (d i, t i)) y (false, true) -
      groupMean (fun i => (d i, t i)) y (false, false),
    (groupMean (fun i => (d i, t i)) y (true, true) -
        groupMean (fun i => (d i, t i)) y (true, false)) -
      (groupMean (fun i => (d i, t i)) y (false, true) -
        groupMean (fun i => (d i, t i)) y (false, false))]

/-- Fitted values of the saturated two-by-two design at coefficients `β`. -/
theorem twoByTwoDesign_mulVec {ι : Type*} (d t : ι → Bool) (β : Fin 4 → ℝ) :
    twoByTwoDesign d t *ᵥ β = fun i =>
      β 0 + β 1 * (if d i then 1 else 0) + β 2 * (if t i then 1 else 0) +
        β 3 * ((if d i then 1 else 0) * (if t i then 1 else 0)) := by
  funext i
  simp [twoByTwoDesign, Matrix.mulVec]
  have h0 : vecHead β = β 0 := rfl
  have h1 : vecHead (vecTail β) = β 1 := rfl
  have h2 : vecHead (vecTail (vecTail β)) = β 2 := rfl
  have h3 : vecHead (vecTail (vecTail (vecTail β))) = β 3 := rfl
  rw [h0, h1, h2, h3]
  ring

/-- **The saturated fit reproduces the cell means**: at the cell-mean coefficients the fitted
value of every observation is the mean of its own cell. No cell needs to be populated beyond
the observation's own. -/
theorem twoByTwoDesign_mulVec_cellMeanCoefficients {ι : Type*} [Fintype ι] (d t : ι → Bool)
    (y : ι → ℝ) :
    twoByTwoDesign d t *ᵥ cellMeanCoefficients d t y =
      fun i => groupMean (fun j => (d j, t j)) y (d i, t i) := by
  rw [twoByTwoDesign_mulVec]
  funext i
  cases d i <;> cases t i <;> simp [cellMeanCoefficients]

open Finset in
private theorem card_mul_groupMean {ι : Type*} [Fintype ι] (d t : ι → Bool) (y : ι → ℝ)
    (c : Bool × Bool) :
    (#{i | (d i, t i) = c} : ℝ) * groupMean (fun j => (d j, t j)) y c =
      ∑ i with (d i, t i) = c, y i := by
  rw [groupMean]
  by_cases hn : #{i | (d i, t i) = c} = 0
  · rw [Finset.card_eq_zero.mp hn]
    simp
  · have hne : ((#{i | (d i, t i) = c} : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hne]

private theorem sum_mul_groupMean {ι : Type*} [Fintype ι] (d t : ι → Bool) (y : ι → ℝ)
    (w : Bool × Bool → ℝ) :
    ∑ i, w (d i, t i) * groupMean (fun j => (d j, t j)) y (d i, t i) =
      ∑ i, w (d i, t i) * y i := by
  have hfib : ∀ (f : ι → ℝ),
      ∑ i, f i = ∑ c, ∑ i ∈ Finset.univ.filter (fun i => (d i, t i) = c), f i := by
    intro f
    exact (Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_univ _) f).symm
  rw [hfib, hfib]
  apply Finset.sum_congr rfl
  intro c _
  have e1 : ∀ i ∈ Finset.univ.filter (fun i => (d i, t i) = c),
      w (d i, t i) * groupMean (fun j => (d j, t j)) y (d i, t i) =
        w c * groupMean (fun j => (d j, t j)) y c := by
    intro i hi
    have hc : (d i, t i) = c := (Finset.mem_filter.mp hi).2
    rw [hc]
  have e2 : ∀ i ∈ Finset.univ.filter (fun i => (d i, t i) = c),
      w (d i, t i) * y i = w c * y i := by
    intro i hi
    have hc : (d i, t i) = c := (Finset.mem_filter.mp hi).2
    rw [hc]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_const, nsmul_eq_mul]
  exact card_mul_groupMean d t y c

/-- **The cell-mean coefficients solve the normal equations** of the saturated two-by-two
regression for every sample. Empty cells are allowed: they contain no residual, so their junk
mean `0` does not enter. -/
theorem gram_mulVec_cellMeanCoefficients {ι : Type*} [Fintype ι] (d t : ι → Bool)
    (y : ι → ℝ) :
    ((twoByTwoDesign d t)ᵀ * twoByTwoDesign d t) *ᵥ cellMeanCoefficients d t y =
      (twoByTwoDesign d t)ᵀ *ᵥ y := by
  rw [← Matrix.mulVec_mulVec, twoByTwoDesign_mulVec_cellMeanCoefficients]
  ext j
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  fin_cases j
  · simpa [twoByTwoDesign] using sum_mul_groupMean d t y (fun _ => 1)
  · simpa [twoByTwoDesign] using
      sum_mul_groupMean d t y (fun c => if c.1 then (1 : ℝ) else 0)
  · simpa [twoByTwoDesign] using
      sum_mul_groupMean d t y (fun c => if c.2 then (1 : ℝ) else 0)
  · simpa [twoByTwoDesign] using sum_mul_groupMean d t y
      (fun c => (if c.1 then (1 : ℝ) else 0) * (if c.2 then (1 : ℝ) else 0))

/-- **Full column rank**: the Gram matrix `Xᵀ X` of the saturated two-by-two design is
invertible if and only if all four cells are populated. -/
theorem isUnit_gram_twoByTwoDesign_iff {ι : Type*} [Fintype ι] (d t : ι → Bool) :
    IsUnit ((twoByTwoDesign d t)ᵀ * twoByTwoDesign d t) ↔ ∀ a b, ∃ i, d i = a ∧ t i = b := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  constructor
  · intro hdet a b
    by_contra hnone
    cases a <;> cases b
    · refine hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨![1, -1, -1, (1 : ℝ)], ?_, ?_⟩)
      · intro h
        have h0 := congrFun h 0
        simp at h0
      · rw [← Matrix.mulVec_mulVec]
        have hX : twoByTwoDesign d t *ᵥ ![1, -1, -1, (1 : ℝ)] = 0 := by
          rw [twoByTwoDesign_mulVec]
          funext i
          cases hd : d i <;> cases ht : t i
          · exact (hnone ⟨i, hd, ht⟩).elim
          · simp
          · simp
          · simp
        rw [hX, Matrix.mulVec_zero]
    · refine hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨![0, 0, 1, (-1 : ℝ)], ?_, ?_⟩)
      · intro h
        have h0 := congrFun h 2
        simp at h0
      · rw [← Matrix.mulVec_mulVec]
        have hX : twoByTwoDesign d t *ᵥ ![0, 0, 1, (-1 : ℝ)] = 0 := by
          rw [twoByTwoDesign_mulVec]
          funext i
          cases hd : d i <;> cases ht : t i
          · simp
          · exact (hnone ⟨i, hd, ht⟩).elim
          · simp
          · simp
        rw [hX, Matrix.mulVec_zero]
    · refine hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨![0, 1, 0, (-1 : ℝ)], ?_, ?_⟩)
      · intro h
        have h0 := congrFun h 1
        simp at h0
      · rw [← Matrix.mulVec_mulVec]
        have hX : twoByTwoDesign d t *ᵥ ![0, 1, 0, (-1 : ℝ)] = 0 := by
          rw [twoByTwoDesign_mulVec]
          funext i
          cases hd : d i <;> cases ht : t i
          · simp
          · simp
          · exact (hnone ⟨i, hd, ht⟩).elim
          · simp
        rw [hX, Matrix.mulVec_zero]
    · refine hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨![0, 0, 0, (1 : ℝ)], ?_, ?_⟩)
      · intro h
        have h0 := congrFun h 3
        simp at h0
      · rw [← Matrix.mulVec_mulVec]
        have hX : twoByTwoDesign d t *ᵥ ![0, 0, 0, (1 : ℝ)] = 0 := by
          rw [twoByTwoDesign_mulVec]
          funext i
          cases hd : d i <;> cases ht : t i
          · simp
          · simp
          · simp
          · exact (hnone ⟨i, hd, ht⟩).elim
        rw [hX, Matrix.mulVec_zero]
  · intro hcell
    by_contra hdet0
    obtain ⟨v, hv0, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
    have hXv : twoByTwoDesign d t *ᵥ v = 0 := by
      have hdot : (twoByTwoDesign d t *ᵥ v) ⬝ᵥ (twoByTwoDesign d t *ᵥ v) = 0 := by
        have e1 : (twoByTwoDesign d t *ᵥ v) ⬝ᵥ (twoByTwoDesign d t *ᵥ v)
            = ((twoByTwoDesign d t *ᵥ v) ᵥ* twoByTwoDesign d t) ⬝ᵥ v :=
          Matrix.dotProduct_mulVec _ _ _
        have e2 : ((twoByTwoDesign d t *ᵥ v) ᵥ* twoByTwoDesign d t)
            = (twoByTwoDesign d t)ᵀ *ᵥ (twoByTwoDesign d t *ᵥ v) := by
          have hvv := Matrix.vecMul_transpose (twoByTwoDesign d t)ᵀ
            (twoByTwoDesign d t *ᵥ v)
          rwa [Matrix.transpose_transpose] at hvv
        rw [e1, e2, Matrix.mulVec_mulVec, hGv]
        simp [dotProduct]
      have hsq : ∑ i, ((twoByTwoDesign d t *ᵥ v) i) ^ 2 = 0 := by
        have hdot' : (twoByTwoDesign d t *ᵥ v) ⬝ᵥ (twoByTwoDesign d t *ᵥ v)
            = ∑ i, ((twoByTwoDesign d t *ᵥ v) i) ^ 2 := by
          simp [dotProduct, pow_two]
        rwa [hdot'] at hdot
      have hall : ∀ i, (twoByTwoDesign d t *ᵥ v) i = 0 := by
        have hall' : ∀ i ∈ Finset.univ, ((twoByTwoDesign d t *ᵥ v) i) ^ 2 = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hsq
        intro i
        exact sq_eq_zero_iff.mp (hall' i (Finset.mem_univ i))
      exact funext hall
    have hv00 : v = 0 := by
      rw [twoByTwoDesign_mulVec] at hXv
      obtain ⟨i00, h00d, h00t⟩ := hcell false false
      obtain ⟨i10, h10d, h10t⟩ := hcell true false
      obtain ⟨i01, h01d, h01t⟩ := hcell false true
      obtain ⟨i11, h11d, h11t⟩ := hcell true true
      have e00 := congrFun hXv i00
      have e10 := congrFun hXv i10
      have e01 := congrFun hXv i01
      have e11 := congrFun hXv i11
      simp [h00d, h00t] at e00
      simp [h10d, h10t] at e10
      simp [h01d, h01t] at e01
      simp [h11d, h11t] at e11
      have z0 : v 0 = 0 := by linarith
      have z1 : v 1 = 0 := by linarith
      have z2 : v 2 = 0 := by linarith
      have z3 : v 3 = 0 := by linarith
      funext j
      fin_cases j
      · exact z0
      · exact z1
      · exact z2
      · exact z3
    exact hv0 hv00

/-- **OLS on the saturated two-by-two design**: with all four cells populated, the
least-squares estimate is the cell-mean coefficient vector. -/
theorem olsEstimator_twoByTwoDesign {ι : Type*} [Fintype ι] [DecidableEq ι] {d t : ι → Bool}
    (hcell : ∀ a b, ∃ i, d i = a ∧ t i = b) (y : ι → ℝ) :
    olsEstimator (twoByTwoDesign d t) y = cellMeanCoefficients d t y := by
  have hU : IsUnit ((twoByTwoDesign d t)ᵀ * twoByTwoDesign d t) :=
    (isUnit_gram_twoByTwoDesign_iff d t).mpr hcell
  exact ((MathlibExt.Probability.FiniteProbability.eq_olsEstimator_iff hU y _).mp
    (gram_mulVec_cellMeanCoefficients d t y)).symm

/-- **Unique least-squares solution**: with all four cells populated, a coefficient vector
solves the normal equations `(Xᵀ X) β = Xᵀ y` if and only if it is the cell-mean coefficient
vector. -/
theorem twoByTwoDesign_normal_eq_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {d t : ι → Bool}
    (hcell : ∀ a b, ∃ i, d i = a ∧ t i = b) (y : ι → ℝ) (β : Fin 4 → ℝ) :
    ((twoByTwoDesign d t)ᵀ * twoByTwoDesign d t) *ᵥ β = (twoByTwoDesign d t)ᵀ *ᵥ y ↔
      β = cellMeanCoefficients d t y := by
  rw [MathlibExt.Probability.FiniteProbability.eq_olsEstimator_iff
    ((isUnit_gram_twoByTwoDesign_iff d t).mpr hcell), olsEstimator_twoByTwoDesign hcell]

/-- **The saturated two-by-two regression interaction is the four-cell mean contrast**: with
all four cells populated, the OLS coefficient on `D * T` is
`(m₁₁ - m₁₀) - (m₀₁ - m₀₀)`, the change of the `d`-cell means across `t` minus that of the
other cells (the difference in differences of the four cell means). -/
theorem olsEstimator_twoByTwoDesign_interaction {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d t : ι → Bool} (hcell : ∀ a b, ∃ i, d i = a ∧ t i = b) (y : ι → ℝ) :
    olsEstimator (twoByTwoDesign d t) y 3 =
      (groupMean (fun i => (d i, t i)) y (true, true) -
          groupMean (fun i => (d i, t i)) y (true, false)) -
        (groupMean (fun i => (d i, t i)) y (false, true) -
          groupMean (fun i => (d i, t i)) y (false, false)) := by
  rw [olsEstimator_twoByTwoDesign hcell]
  rfl

end MathlibExt.Probability.Statistics.SaturatedTwoByTwoRegression
