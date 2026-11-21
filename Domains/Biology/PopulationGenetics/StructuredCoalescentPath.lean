/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.StructuredCoalescent
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.HittingTime

/-!
# Path-space means of the island-pair coalescence time

`Domains.Biology.PopulationGenetics.StructuredCoalescent` solves the backward (first-step)
equations of the two-lineage structured coalescent in the finite island model with `d` demes
and `M = 4Nm` (time in units of `2N` generations), with off-diagonal rates `rate d M` and
closed-form solution `meanCoalescenceTime d M` (`T₀ = d`, `T₁ = d + (d - 1) / M`). This file
identifies those numbers with expectations over the path process `ctmcPath (rateMatrix d M) s`
of `MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path`: the coalescence time is the
hitting time of the coalesced state, `H = inf {t ≥ 0 | X t = coalesced}`, valued in `ℝ≥0∞`,
and the expectations are lower Lebesgue integrals, so no integrability hypothesis is needed
(they are proved finite).

## Main results

* `rateMatrix`, `isRateMatrix_rateMatrix`: the Q-matrix of the island-pair chain is a rate
  matrix for `d ≥ 2` and `M ≥ 0`.
* `rateMatrix_mulVec_sub`: the generator acts by first differences,
  `(Q h) s = ∑ₜ q(s, t) (h t - h s)`.
* `lintegral_coalescenceTime`: `E_s H = meanCoalescenceTime d M s` for `d ≥ 2` and `M > 0`.
* `lintegral_coalescenceTime_same`, `lintegral_coalescenceTime_different`: the values `d` and
  `d + (d - 1) / M`.
* `lintegral_coalescenceTime_different_zero`, `lintegral_coalescenceTime_same_zero`: boundary
  guards at `M = 0` (the integral from `different` is infinite; from `same` it is `1`).

The proofs combine the general identification of hitting-time means with the minimal
nonnegative solutions of the backward equations
(`ProbabilityTheory.IsRateMatrix.ctmcHittingTime_backward`) with uniqueness of the solution of
the island-pair system (`firstStepEquations_iff`).

## References

* C. Strobeck, *Average number of nucleotide differences in a sample from a single
  subpopulation: a test for population subdivision*, Genetics 117 (1987), 149–153.
* M. Slatkin, *Inbreeding coefficients and coalescence times*, Genet. Res. 58 (1991), 167–175.
* T. Notohara, *The coalescent and the genealogical process in geographically structured
  population*, J. Math. Biol. 29 (1990), 59–75.
* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §3.3.
-/

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.StructuredCoalescentPath

open MeasureTheory ProbabilityTheory
open MathlibExt.Biology.PopulationGenetics.StructuredCoalescent PairState
open scoped Matrix NNReal ENNReal

variable [MeasurableSpace PairState] [DiscreteMeasurableSpace PairState]

/-- The Q-matrix of the two-lineage structured coalescent (clause 1): off-diagonal entries
`rate d M`, diagonal entries `-exitRate d M s`. -/
noncomputable def rateMatrix (d : ℕ) (M : ℝ) : Matrix PairState PairState ℝ := fun s t =>
  if s = t then -exitRate d M s else rate d M s t

/-- For `2 ≤ d` and `0 ≤ M`, `rateMatrix d M` is a rate matrix (clause 2). -/
theorem isRateMatrix_rateMatrix {d : ℕ} (hd : 2 ≤ d) {M : ℝ} (hM : 0 ≤ M) :
    IsRateMatrix (rateMatrix d M) := by
  have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  constructor
  · intro i j hij
    cases i <;> cases j <;> simp [rateMatrix, rate] <;>
      first | exact absurd rfl hij | positivity
  · intro s
    cases s <;> simp [rateMatrix, exitRate, PairState.sum_eq, rate]

/-- The generator acts by first differences (clause 3): `(rateMatrix d M *ᵥ h) s` is
`∑ t, rate d M s t * (h t - h s)`. -/
theorem rateMatrix_mulVec_sub (d : ℕ) (M : ℝ) (h : PairState → ℝ) :
    (rateMatrix d M *ᵥ h) = fun s => ∑ t, rate d M s t * (h t - h s) := by
  funext s
  cases s <;>
    simp [Matrix.mulVec, dotProduct, rateMatrix, exitRate, PairState.sum_eq, rate] <;>
    ring

private lemma meanCoalescenceTime_nonneg {d : ℕ} (hd : 2 ≤ d) {M : ℝ} (hM : 0 < M)
    (s : PairState) : 0 ≤ meanCoalescenceTime d M s := by
  cases s
  · simp only [meanCoalescenceTime, withinTime]
    positivity
  · simp only [meanCoalescenceTime, betweenTime]
    have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
      have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    exact add_nonneg (Nat.cast_nonneg d) (div_nonneg hd1 hM.le)
  · simp only [meanCoalescenceTime, le_rfl]

/-- **Mean coalescence time, path form** (clause 4): for `d ≥ 2` demes and `M > 0`, the lower
Lebesgue integral of the hitting time of the coalesced state, from any state `s`, is
`meanCoalescenceTime d M s`. -/
theorem lintegral_coalescenceTime {d : ℕ} (hd : 2 ≤ d) {M : ℝ} (hM : 0 < M)
    (s : PairState) :
    ∫⁻ ω, ctmcHittingTime (rateMatrix d M) s {PairState.coalesced} ω
      ∂ctmcInputMeasure (isRateMatrix_rateMatrix hd hM.le) =
      ENNReal.ofReal (meanCoalescenceTime d M s) := by
  have hEq : ∀ i ∉ ({PairState.coalesced} : Set PairState),
      ((rateMatrix d M) *ᵥ meanCoalescenceTime d M) i = -1 := by
    intro i hi
    have hi' : i ≠ PairState.coalesced := by simpa using hi
    rw [rateMatrix_mulVec_sub]
    exact ((firstStepEquations_iff hd hM _).2 rfl).2 i hi'
  obtain ⟨hle, h0, heq⟩ := (isRateMatrix_rateMatrix hd hM.le).ctmcHittingTime_backward
    (A := {PairState.coalesced}) (meanCoalescenceTime_nonneg hd hM) hEq
  have hFS : FirstStepEquations d M (fun j =>
      (∫⁻ ω, ctmcHittingTime (rateMatrix d M) j {PairState.coalesced} ω
        ∂ctmcInputMeasure (isRateMatrix_rateMatrix hd hM.le)).toReal) := by
    constructor
    · exact h0 _ rfl
    · intro i hi'
      have hi : i ∉ ({PairState.coalesced} : Set PairState) := by simpa using hi'
      have h := heq i hi
      rw [rateMatrix_mulVec_sub] at h
      exact h
  have hEq2 := (firstStepEquations_iff hd hM _).1 hFS
  have hToReal : (∫⁻ ω, ctmcHittingTime (rateMatrix d M) s {PairState.coalesced} ω
      ∂ctmcInputMeasure (isRateMatrix_rateMatrix hd hM.le)).toReal =
      meanCoalescenceTime d M s :=
    congrFun hEq2 s
  rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle s)), hToReal]

/-- From the same deme the mean coalescence time is `d` (clause 5). -/
theorem lintegral_coalescenceTime_same {d : ℕ} (hd : 2 ≤ d) {M : ℝ} (hM : 0 < M) :
    ∫⁻ ω, ctmcHittingTime (rateMatrix d M) same {PairState.coalesced} ω
      ∂ctmcInputMeasure (isRateMatrix_rateMatrix hd hM.le) = ENNReal.ofReal d := by
  have h := lintegral_coalescenceTime hd hM PairState.same
  simpa [meanCoalescenceTime, withinTime] using h

/-- From different demes the mean coalescence time is `d + (d - 1) / M` (clause 5). -/
theorem lintegral_coalescenceTime_different {d : ℕ} (hd : 2 ≤ d) {M : ℝ} (hM : 0 < M) :
    ∫⁻ ω, ctmcHittingTime (rateMatrix d M) different {PairState.coalesced} ω
      ∂ctmcInputMeasure (isRateMatrix_rateMatrix hd hM.le) =
      ENNReal.ofReal (d + (d - 1) / M) := by
  have h := lintegral_coalescenceTime hd hM PairState.different
  simpa [meanCoalescenceTime, betweenTime] using h

/-- Boundary guard at `M = 0` (clause 6): from different demes the lineages never meet, so the
mean coalescence time is infinite (this protects the junk value `betweenTime d 0 = d` from any
probabilistic reading). -/
theorem lintegral_coalescenceTime_different_zero {d : ℕ} (hd : 2 ≤ d) :
    ∫⁻ ω, ctmcHittingTime (rateMatrix d 0) different {PairState.coalesced} ω
      ∂ctmcInputMeasure (isRateMatrix_rateMatrix hd le_rfl) = ∞ := by
  have hQ : rateMatrix d 0 different different = 0 := by
    simp [rateMatrix, exitRate, PairState.sum_eq, rate]
  have hHit : ∀ ω, ctmcHittingTime (rateMatrix d 0) different {PairState.coalesced} ω = ∞ := by
    intro ω
    have hi : different ∉ ({PairState.coalesced} : Set PairState) := by simp
    rw [ctmcHittingTime_eq_add hi ω]
    have hHold : ctmcHoldingTime (rateMatrix d 0) different ω 0 = ∞ := by
      simp [ctmcHoldingTime, ctmcJumpChain, hQ]
    rw [hHold, top_add]
  simp [hHit]

/-- Boundary guard at `M = 0` (clause 6): from the same deme the coalescence time is an `Exp(1)`
clock (migration never fires), so the mean coalescence time is `1`. -/
theorem lintegral_coalescenceTime_same_zero {d : ℕ} (hd : 2 ≤ d) :
    ∫⁻ ω, ctmcHittingTime (rateMatrix d 0) same {PairState.coalesced} ω
      ∂ctmcInputMeasure (isRateMatrix_rateMatrix hd le_rfl) = 1 := by
  have hQ : rateMatrix d 0 same same = -1 := by
    simp [rateMatrix, exitRate, PairState.sum_eq, rate]
  have hQne : rateMatrix d 0 same same ≠ 0 := by rw [hQ]; norm_num
  have hi : same ∉ ({PairState.coalesced} : Set PairState) := by simp
  have hEq := (isRateMatrix_rateMatrix hd le_rfl).lintegral_ctmcHittingTime
    (A := {PairState.coalesced}) hi hQne
  rw [hEq]
  have hDiag : (1 : ℝ) / -rateMatrix d 0 same same = 1 := by rw [hQ]; norm_num
  have hQsd : rateMatrix d 0 same different = 0 := by simp [rateMatrix, rate]
  have hQsc : rateMatrix d 0 same coalesced = 1 := by simp [rateMatrix, rate]
  have hJump_same : ctmcJumpMatrix (rateMatrix d 0) same same = 0 := by
    simp [ctmcJumpMatrix, hQne]
  have hJump_diff : ctmcJumpMatrix (rateMatrix d 0) same different = 0 := by
    simp [ctmcJumpMatrix, hQsd, hQ]
  have hJump_coal : ctmcJumpMatrix (rateMatrix d 0) same coalesced = 1 := by
    simp [ctmcJumpMatrix, hQsc, hQ]
  have hCoal : ∫⁻ ω, ctmcHittingTime (rateMatrix d 0) coalesced {PairState.coalesced} ω
      ∂ctmcInputMeasure (isRateMatrix_rateMatrix hd le_rfl) = 0 :=
    (isRateMatrix_rateMatrix hd le_rfl).lintegral_ctmcHittingTime_of_mem (by simp)
  rw [hDiag, PairState.sum_eq, hJump_same, hJump_diff, hJump_coal, hCoal]
  simp

end MathlibExt.Biology.PopulationGenetics.StructuredCoalescentPath
