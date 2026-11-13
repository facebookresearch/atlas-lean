/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.GTRInference
public import MathlibExt.Biology.Phylogenetics.SubstitutionModels
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.Matrix.Order
import MathlibExt.Probability.Statistics.Slutsky

/-!
# Log-det recovery of the GTR rate matrix from a pairwise divergence matrix

Let two aligned sequences be related by a GTR branch (`SubstitutionModels.gtrRate`, Tavaré 1986)
with base frequencies `π`, symmetric exchangeabilities `s` and branch length `t`, so that the
**divergence matrix** of an aligned site, `F i j = P(X = i, Y = j)`, is

`F = Π P(t)`, with `Π = diagonal π` and `P(t) = exp (t • Q)`, `Q = gtrRate π s`.

This file gives an explicit estimator that inverts this map up to the rate/time scale, proves
that it recovers `Q / (-tr Q)` exactly from the true divergence matrix, and proves that it is
consistent when `F` is estimated by the empirical pair-site frequencies.

## The estimator

For any real matrix `F` (in practice the empirical divergence matrix of two sequences):

* `baseFreq F i = (∑ j, F i j + ∑ j, F j i) / 2`, the average of the two marginals;
* `normDivergence F = D⁻¹ Fₛ D⁻¹`, where `Fₛ = (F + Fᵀ) / 2` and `D = diagonal (√ baseFreq F)`;
  it is symmetric for every `F`;
* `logGenerator F = D⁻¹ log (normDivergence F) D`, with `log` the real logarithm of the
  continuous functional calculus of symmetric matrices;
* `logDetDistance F = -tr log (normDivergence F)`, the **log-det distance**: when
  `normDivergence F` is positive definite it equals `-log det (normDivergence F)`
  (`logDetDistance_eq_neg_log_det`), which is the paralinear / LogDet distance
  `-log det Fₛ + ∑ i, log (baseFreq F i)` of the symmetrized divergence matrix
  (`logDetDistance_eq_logDet`);
* `rateEstimate F = (logDetDistance F)⁻¹ • logGenerator F`, the rate matrix normalized to
  `tr = -1`.

## Main results

* `logGenerator_gtr`, `logDetDistance_gtr`, `rateEstimate_gtr`, `baseFreq_gtr`: **exact
  recovery.** At `F = Π exp (t • Q)` with `π > 0`, symmetric `s` and nonnegative off-diagonal
  `s`, the estimator returns `logGenerator F = t • Q`, `logDetDistance F = -t * tr Q`, the base
  frequencies `π`, and, for `t ≠ 0`, `rateEstimate F = (-tr Q)⁻¹ • Q`. The exchangeabilities are
  recovered up to the same scale (`exchangeability_gtr`).
* `continuousAt_rateEstimate`, `continuousAt_logDetDistance`: the estimator is continuous at
  the true divergence matrix when `t ≠ 0` and `s > 0` off the diagonal (on at least two states).
* `tendsto_rateEstimate_gtr`: **recovery consistency** for any consistent divergence estimate.
* `ae_tendsto_rateEstimate_empirical`, `tendstoInMeasure_rateEstimate_empirical`: **recovery
  consistency from data**: with aligned site pairs drawn independently from the GTR divergence
  matrix, the estimator applied to the empirical pair-site frequencies converges to
  `(-tr Q)⁻¹ • Q` almost surely and (entrywise) in probability.

## Source receipt (API-00)

* Source: the LogDet / paralinear distance of Lockhart, Steel, Hendy and Penny (1994) and Lake
  (1994), and the matrix-logarithm recovery of a reversible generator from one transition matrix
  used for GTR distances (Tavaré 1986; Rodríguez, Oliver, Marín and Medina 1990; Felsenstein
  2004, chapter 13). For a reversible `Q` with `Π Q` symmetric, `D Q D⁻¹` is symmetric
  (`D = diagonal √π`), so `D⁻¹ F D⁻¹ = exp (t D Q D⁻¹)` is a symmetric positive definite
  matrix whose real logarithm is `t D Q D⁻¹`; its trace is `log det (D⁻¹ F D⁻¹) = t tr Q`.
* Reused: `SubstitutionModels.gtrRate`, `isRateMatrix_gtrRate`,
  `vecMul_ctmcTransition_gtrRate`, `isDetailedBalance_gtrRate` and
  `isDetailedBalance_ctmcTransition_gtrRate`; `IsRateMatrix.sum_ctmcTransition`; Mathlib's
  continuous functional calculus for Hermitian matrices (`CFC.log_exp`, `cfc_map_spectrum`,
  `Matrix.IsHermitian.cfc_eq`) and its continuity (`ContinuousAt.cfc`,
  `upperHemicontinuous_spectrum`, with the scoped isometric functional calculus of
  `Matrix.Norms.L2Operator`); `GTRInference.empiricalFreq` and
  `GTRInference.ae_tendsto_empiricalFreq` / `tendstoInMeasure_empiricalFreq` (T67) for the
  sampling law; `MeasureTheory.TendstoInMeasure.comp_const_of_continuousAt` (`Slutsky`) for the
  continuous mapping step in probability.
* Proved here: the estimator, its exact recovery, its continuity at the true divergence matrix,
  the trace/log-det identity, and the consistency corollaries.
* Not covered elsewhere: T67 (`GTRInference`) proves consistency of an abstract
  minimum-distance estimator from an identifiability hypothesis; it contains no explicit
  inversion and no log-det construction. `CSLibExt.Bioinformatics.Phylogenetics.FelsensteinZone`
  defines the scalar paralinear distance and its additivity, but lives in `CSLibExt` and cannot
  be imported here; `logDetDistance_eq_logDet` states the same formula for the symmetrized
  matrix. `GTRIdentifiability` (T66, #1565, merged) is not imported per the task spec; its
  `isSymm_conj_sqrt` is private there, so the conjugation lemma is restated here.

## References

* S. Tavaré, *Some probabilistic and statistical problems in the analysis of DNA sequences*,
  Lectures on Mathematics in the Life Sciences 17 (1986), 57–86.
* F. Rodríguez, J. L. Oliver, A. Marín and J. R. Medina, *The general stochastic model of
  nucleotide substitution*, J. Theor. Biol. 142 (1990), 485–501.
* P. J. Lockhart, M. A. Steel, M. D. Hendy and D. Penny, *Recovering evolutionary trees under a
  more realistic model of sequence evolution*, Mol. Biol. Evol. 11 (1994), 605–612.
* J. A. Lake, *Reconstructing evolutionary trees from DNA and protein sequences: paralinear
  distances*, Proc. Natl. Acad. Sci. USA 91 (1994), 1455–1459.
* J. Felsenstein, *Inferring Phylogenies*, Sinauer, 2004, chapter 13.
-/

@[expose] public section

open Finset Matrix ProbabilityTheory Filter Topology MeasureTheory

namespace MathlibExt.Biology.Phylogenetics.GTRLogDetRecovery

open SubstitutionModels

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The estimator -/

/-- The **base-frequency estimate** of a divergence matrix: the average of its row and column
marginals. -/
noncomputable def baseFreq (F : Matrix ι ι ℝ) (i : ι) : ℝ :=
  (∑ j, F i j + ∑ j, F j i) / 2

/-- The **normalized divergence matrix** `D⁻¹ Fₛ D⁻¹`, with `Fₛ = (F + Fᵀ) / 2` and
`D = diagonal (√ baseFreq F)`. It is symmetric for every `F`. -/
noncomputable def normDivergence (F : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => (F i j + F j i) / 2 / (√(baseFreq F i) * √(baseFreq F j))

/-- The **log-det generator** `D⁻¹ log (normDivergence F) D`, where `log` is the real logarithm
of the continuous functional calculus. At the true divergence matrix it equals `t • Q`. -/
noncomputable def logGenerator (F : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => cfc Real.log (normDivergence F) i j * √(baseFreq F j) / √(baseFreq F i)

/-- The **log-det distance** `-tr log (normDivergence F)`. When `normDivergence F` is positive
definite this is `-log det (normDivergence F)` (`logDetDistance_eq_neg_log_det`). -/
noncomputable def logDetDistance (F : Matrix ι ι ℝ) : ℝ :=
  -(cfc Real.log (normDivergence F)).trace

/-- The **log-det rate estimate**: the log-det generator normalized by the log-det distance, so
that its trace is `-1`. -/
noncomputable def rateEstimate (F : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (logDetDistance F)⁻¹ • logGenerator F

omit [DecidableEq ι] in
theorem isSelfAdjoint_normDivergence (F : Matrix ι ι ℝ) : IsSelfAdjoint (normDivergence F) := by
  rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  ext i j
  simp only [normDivergence, transpose_apply, of_apply]
  rw [add_comm (F j i), mul_comm (√(baseFreq F j))]

/-! ## The log-det distance as a log-determinant -/

/-- For a symmetric real matrix with positive eigenvalues, the trace of its real logarithm is
the logarithm of its determinant. -/
theorem trace_cfc_log_eq_log_det {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    (cfc Real.log A).trace = Real.log A.det := by
  have hH := hA.isHermitian
  rw [hH.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_mul_cycle,
    Unitary.coe_star_mul_self,
    Matrix.one_mul, trace_diagonal, hH.det_eq_prod_eigenvalues]
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id]
  rw [Real.log_prod fun i _ => (hA.eigenvalues_pos i).ne']

/-- **The log-det distance is a log-determinant**: if `normDivergence F` is positive definite,
`logDetDistance F = -log det (normDivergence F)`. -/
theorem logDetDistance_eq_neg_log_det {F : Matrix ι ι ℝ} (hF : (normDivergence F).PosDef) :
    logDetDistance F = -Real.log (normDivergence F).det := by
  rw [logDetDistance, trace_cfc_log_eq_log_det hF]

/-- **Paralinear form of the log-det distance**: with positive base-frequency estimates and a
positive definite normalized divergence matrix, `logDetDistance F` equals the paralinear (LogDet)
distance `-log det Fₛ + ∑ i, log (baseFreq F i)` of the symmetrized divergence matrix
`Fₛ = (F + Fᵀ) / 2`, whose two marginals are both `baseFreq F` (Lake 1994; Lockhart et al.
1994). -/
theorem logDetDistance_eq_logDet {F : Matrix ι ι ℝ} (hb : ∀ i, 0 < baseFreq F i)
    (hF : (normDivergence F).PosDef) :
    logDetDistance F =
      -Real.log (Matrix.of fun i j => (F i j + F j i) / 2).det + ∑ i, Real.log (baseFreq F i) := by
  set E : Matrix ι ι ℝ := diagonal fun i => (√(baseFreq F i))⁻¹
  have hM : normDivergence F = E * (Matrix.of fun i j => (F i j + F j i) / 2) * E := by
    ext i j
    simp only [normDivergence, E, of_apply, diagonal_mul, mul_diagonal]
    ring
  have hdetE : E.det * E.det = (∏ i, baseFreq F i)⁻¹ := by
    simp only [E, det_diagonal, ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← mul_inv, Real.mul_self_sqrt (hb i).le]
  have hdet : (normDivergence F).det =
      (Matrix.of fun i j => (F i j + F j i) / 2).det * (∏ i, baseFreq F i)⁻¹ := by
    rw [hM, det_mul, det_mul, ← hdetE]
    ring
  have hprod : 0 < ∏ i, baseFreq F i := Finset.prod_pos fun i _ => hb i
  have hpos := hF.det_pos
  have hFs : (Matrix.of fun i j => (F i j + F j i) / 2).det ≠ 0 := by
    intro h
    rw [hdet, h, zero_mul] at hpos
    exact lt_irrefl _ hpos
  rw [logDetDistance_eq_neg_log_det hF, hdet, Real.log_mul hFs (inv_ne_zero hprod.ne'),
    Real.log_inv, Real.log_prod fun i _ => (hb i).ne']
  ring

/-! ## Exact recovery at the true divergence matrix -/

section Recovery

variable {π : ι → ℝ} {s : Matrix ι ι ℝ}

/-- A generator in detailed balance with a positive vector `π` becomes symmetric after
conjugation by `diagonal √π`. -/
theorem isSymm_conj_sqrt (hπ : ∀ i, 0 < π i) {Q : Matrix ι ι ℝ} (hQ : IsDetailedBalance π Q) :
    (diagonal (fun i => √(π i)) * Q * diagonal (fun i => (√(π i))⁻¹)).IsSymm := by
  refine IsSymm.ext fun i j => ?_
  simp only [mul_diagonal, diagonal_mul]
  have hi := Real.sqrt_pos.2 (hπ i)
  have hj := Real.sqrt_pos.2 (hπ j)
  have h := hQ i j
  rw [← Real.mul_self_sqrt (hπ i).le, ← Real.mul_self_sqrt (hπ j).le] at h
  field_simp
  linear_combination (-1 : ℝ) * h

theorem baseFreq_gtr (hπ : ∀ i, 0 < π i) (hsymm : ∀ i j, s i j = s j i)
    (hs : ∀ i j, i ≠ j → 0 ≤ s i j) (t : ℝ) :
    baseFreq (diagonal π * ctmcTransition (gtrRate π s) t) = π := by
  funext i
  have hrow : ∑ j, (diagonal π * ctmcTransition (gtrRate π s) t) i j = π i := by
    simp only [diagonal_mul, ← Finset.mul_sum,
      (isRateMatrix_gtrRate (fun k => (hπ k).le) hs).sum_ctmcTransition, mul_one]
  have hcol : ∑ j, (diagonal π * ctmcTransition (gtrRate π s) t) j i = π i := by
    have := congrFun (vecMul_ctmcTransition_gtrRate π hsymm t) i
    simpa [diagonal_mul, vecMul, dotProduct] using this
  rw [baseFreq, hrow, hcol]
  ring

/-- At the true divergence matrix, the normalized divergence matrix is the exponential of the
symmetric matrix `D (t • Q) D⁻¹`. -/
theorem normDivergence_gtr (hπ : ∀ i, 0 < π i) (hsymm : ∀ i j, s i j = s j i)
    (hs : ∀ i j, i ≠ j → 0 ≤ s i j) (t : ℝ) :
    normDivergence (diagonal π * ctmcTransition (gtrRate π s) t) =
      NormedSpace.exp (diagonal (fun i => √(π i)) * (t • gtrRate π s) *
        diagonal (fun i => (√(π i))⁻¹)) := by
  set D : Matrix ι ι ℝ := diagonal fun i => √(π i)
  set E : Matrix ι ι ℝ := diagonal fun i => (√(π i))⁻¹
  have hDE : D * E = 1 := by
    simp only [D, E, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (Real.sqrt_pos.2 (hπ i)).ne'
  have hE : D⁻¹ = E := inv_eq_right_inv hDE
  have hU : IsUnit D := (isUnit_iff_isUnit_det D).2 (isUnit_det_of_right_inverse hDE)
  rw [← hE, exp_conj _ _ hU, hE]
  have hdb := isDetailedBalance_ctmcTransition_gtrRate π hsymm t
  have hb := baseFreq_gtr hπ hsymm hs t
  ext i j
  simp only [normDivergence, of_apply, hb, D, E, mul_diagonal, diagonal_mul]
  rw [hdb j i]
  simp only [ctmcTransition]
  have hi := Real.sqrt_pos.2 (hπ i)
  have hj := Real.sqrt_pos.2 (hπ j)
  conv_lhs => rw [← Real.mul_self_sqrt (hπ i).le]
  field_simp
  rw [Real.sqrt_sq hi.le]
  ring

/-- The symmetric matrix `D (t • Q) D⁻¹` whose exponential is the normalized divergence. -/
private theorem isSelfAdjoint_conj (hπ : ∀ i, 0 < π i) (hsymm : ∀ i j, s i j = s j i) (t : ℝ) :
    IsSelfAdjoint (diagonal (fun i => √(π i)) * (t • gtrRate π s) *
      diagonal (fun i => (√(π i))⁻¹)) := by
  have hdb : IsDetailedBalance π (t • gtrRate π s) := fun i j => by
    simp only [Matrix.smul_apply, smul_eq_mul]
    linear_combination t * isDetailedBalance_gtrRate π hsymm i j
  have h := (isSymm_conj_sqrt hπ hdb).eq
  rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  exact h

/-- The real logarithm of the normalized divergence matrix at the true divergence matrix. -/
theorem cfc_log_normDivergence_gtr (hπ : ∀ i, 0 < π i) (hsymm : ∀ i j, s i j = s j i)
    (hs : ∀ i j, i ≠ j → 0 ≤ s i j) (t : ℝ) :
    cfc Real.log (normDivergence (diagonal π * ctmcTransition (gtrRate π s) t)) =
      diagonal (fun i => √(π i)) * (t • gtrRate π s) * diagonal (fun i => (√(π i))⁻¹) := by
  open scoped Matrix.Norms.L2Operator in
  rw [normDivergence_gtr hπ hsymm hs t]
  exact CFC.log_exp _ (isSelfAdjoint_conj hπ hsymm t)

/-- **Exact recovery of the scaled generator**: at the true divergence matrix
`Π exp (t • Q)`, the log-det generator is `t • Q`. -/
theorem logGenerator_gtr (hπ : ∀ i, 0 < π i) (hsymm : ∀ i j, s i j = s j i)
    (hs : ∀ i j, i ≠ j → 0 ≤ s i j) (t : ℝ) :
    logGenerator (diagonal π * ctmcTransition (gtrRate π s) t) = t • gtrRate π s := by
  ext i j
  rw [logGenerator, of_apply, cfc_log_normDivergence_gtr hπ hsymm hs t,
    baseFreq_gtr hπ hsymm hs t]
  simp only [mul_diagonal, diagonal_mul]
  have hi := (Real.sqrt_pos.2 (hπ i)).ne'
  have hj := (Real.sqrt_pos.2 (hπ j)).ne'
  field_simp

/-- **Exact recovery of the log-det distance**: at the true divergence matrix it is
`-t * tr Q`, the expected number of substitutions per site scaled by the trace normalization. -/
theorem logDetDistance_gtr (hπ : ∀ i, 0 < π i) (hsymm : ∀ i j, s i j = s j i)
    (hs : ∀ i j, i ≠ j → 0 ≤ s i j) (t : ℝ) :
    logDetDistance (diagonal π * ctmcTransition (gtrRate π s) t) = -t * (gtrRate π s).trace := by
  rw [logDetDistance, cfc_log_normDivergence_gtr hπ hsymm hs t, trace, trace, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [diag_apply, mul_diagonal, diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  have hi := (Real.sqrt_pos.2 (hπ i)).ne'
  field_simp

/-- **Exact recovery of the GTR rate matrix up to scale**: at the true divergence matrix
`Π exp (t • Q)` with `t ≠ 0`, the log-det rate estimate is `Q / (-tr Q)`. -/
theorem rateEstimate_gtr (hπ : ∀ i, 0 < π i) (hsymm : ∀ i j, s i j = s j i)
    (hs : ∀ i j, i ≠ j → 0 ≤ s i j) {t : ℝ} (ht : t ≠ 0) :
    rateEstimate (diagonal π * ctmcTransition (gtrRate π s) t) =
      (-(gtrRate π s).trace)⁻¹ • gtrRate π s := by
  rw [rateEstimate, logDetDistance_gtr hπ hsymm hs t, logGenerator_gtr hπ hsymm hs t, smul_smul,
    neg_mul, ← mul_neg, mul_inv, mul_comm t⁻¹, mul_assoc, inv_mul_cancel₀ ht, mul_one]

/-- **Recovery of the exchangeabilities up to scale**: off the diagonal,
`s i j / (-tr Q) = rateEstimate F i j / baseFreq F j` at the true divergence matrix. -/
theorem exchangeability_gtr (hπ : ∀ i, 0 < π i) (hsymm : ∀ i j, s i j = s j i)
    (hs : ∀ i j, i ≠ j → 0 ≤ s i j) {t : ℝ} (ht : t ≠ 0) {i j : ι} (hij : i ≠ j) :
    rateEstimate (diagonal π * ctmcTransition (gtrRate π s) t) i j /
        baseFreq (diagonal π * ctmcTransition (gtrRate π s) t) j =
      (-(gtrRate π s).trace)⁻¹ * s i j := by
  rw [rateEstimate_gtr hπ hsymm hs ht, baseFreq_gtr hπ hsymm hs t]
  simp only [Matrix.smul_apply, smul_eq_mul, gtrRate, of_apply, hij, ite_false]
  field_simp [(hπ j).ne']

/-- With at least two states and positive parameters, the GTR matrix has negative trace. -/
theorem trace_gtrRate_neg [Nontrivial ι] (hπ : ∀ i, 0 < π i)
    (hs : ∀ i j, i ≠ j → 0 < s i j) : (gtrRate π s).trace < 0 := by
  rw [trace]
  refine Finset.sum_neg (fun i _ => ?_) Finset.univ_nonempty
  obtain ⟨k, hk⟩ := exists_ne i
  have hpos : 0 < ∑ k ∈ univ.erase i, s i k * π k :=
    Finset.sum_pos (fun k hk => mul_pos (hs i k (ne_of_mem_erase hk).symm) (hπ k))
      ⟨k, mem_erase.2 ⟨hk, mem_univ k⟩⟩
  simpa [gtrRate] using hpos

end Recovery

/-! ## Continuity of the estimator at the true divergence matrix -/

section Continuity

omit [DecidableEq ι] in
theorem continuous_baseFreq (i : ι) : Continuous fun F : Matrix ι ι ℝ => baseFreq F i :=
  ((continuous_finsetSum _ fun j _ => continuous_id.matrix_elem i j).add
    (continuous_finsetSum _ fun j _ => continuous_id.matrix_elem j i)).div_const 2

omit [DecidableEq ι] in
theorem continuousAt_normDivergence {F₀ : Matrix ι ι ℝ} (hb : ∀ i, 0 < baseFreq F₀ i) :
    ContinuousAt normDivergence F₀ := by
  refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => ?_
  refine ContinuousAt.div ?_ ?_ ?_
  · exact ((continuous_id.matrix_elem i j).add (continuous_id.matrix_elem j i)).div_const
      2 |>.continuousAt
  · exact ((continuous_baseFreq i).sqrt.mul (continuous_baseFreq j).sqrt).continuousAt
  · exact mul_ne_zero (Real.sqrt_pos.2 (hb i)).ne' (Real.sqrt_pos.2 (hb j)).ne'

/-- The real logarithm of the normalized divergence matrix is continuous at every `F₀` with
positive base frequencies whose normalized divergence matrix has positive spectrum. -/
theorem continuousAt_cfc_log_normDivergence {F₀ : Matrix ι ι ℝ} (hb : ∀ i, 0 < baseFreq F₀ i)
    (hspec : spectrum ℝ (normDivergence F₀) ⊆ Set.Ioi 0) :
    ContinuousAt (fun F => cfc Real.log (normDivergence F)) F₀ := by
  open scoped Matrix.Norms.L2Operator in
  obtain ⟨K, ⟨hKA, hK⟩, hKs⟩ :=
    (spectrum.isCompact (𝕜 := ℝ) (normDivergence F₀)).nhdsSet_basis_isCompact.mem_iff.mp
      (isOpen_Ioi.mem_nhdsSet.2 hspec)
  open scoped Matrix.Norms.L2Operator in
  have hev : ∀ᶠ A in 𝓝 (normDivergence F₀), spectrum ℝ A ⊆ K :=
    (upperHemicontinuous_spectrum ℝ (Matrix ι ι ℝ)).upperHemicontinuousAt _ _ hKA |>.mono
      fun _ ↦ subset_of_mem_nhdsSet
  open scoped Matrix.Norms.L2Operator in
  exact ContinuousAt.cfc hK Real.log (continuousAt_normDivergence hb)
    ((continuousAt_normDivergence hb).eventually hev)
    (Eventually.of_forall isSelfAdjoint_normDivergence)
    (Real.continuousOn_log.mono fun x hx => (hKs hx).ne')

theorem continuousAt_logGenerator {F₀ : Matrix ι ι ℝ} (hb : ∀ i, 0 < baseFreq F₀ i)
    (hspec : spectrum ℝ (normDivergence F₀) ⊆ Set.Ioi 0) :
    ContinuousAt logGenerator F₀ := by
  have hL := continuousAt_cfc_log_normDivergence hb hspec
  refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => ?_
  refine ContinuousAt.div (ContinuousAt.mul ?_ ?_) ?_ ?_
  · exact (continuous_id.matrix_elem i j).continuousAt.comp hL
  · exact (continuous_baseFreq j).sqrt.continuousAt
  · exact (continuous_baseFreq i).sqrt.continuousAt
  · exact (Real.sqrt_pos.2 (hb i)).ne'

theorem continuousAt_logDetDistance {F₀ : Matrix ι ι ℝ} (hb : ∀ i, 0 < baseFreq F₀ i)
    (hspec : spectrum ℝ (normDivergence F₀) ⊆ Set.Ioi 0) :
    ContinuousAt logDetDistance F₀ :=
  (continuous_id.matrix_trace.continuousAt.comp
    (continuousAt_cfc_log_normDivergence hb hspec)).neg

/-- **Continuity of the log-det rate estimate** at every `F₀` with positive base frequencies, a
normalized divergence matrix with positive spectrum, and nonzero log-det distance. -/
theorem continuousAt_rateEstimate {F₀ : Matrix ι ι ℝ} (hb : ∀ i, 0 < baseFreq F₀ i)
    (hspec : spectrum ℝ (normDivergence F₀) ⊆ Set.Ioi 0) (hd : logDetDistance F₀ ≠ 0) :
    ContinuousAt rateEstimate F₀ :=
  ((continuousAt_logDetDistance hb hspec).inv₀ hd).smul (continuousAt_logGenerator hb hspec)

variable {π : ι → ℝ} {s : Matrix ι ι ℝ}

/-- At the true divergence matrix, the normalized divergence matrix has positive spectrum: it is
the exponential of a symmetric matrix. -/
theorem spectrum_normDivergence_gtr (hπ : ∀ i, 0 < π i) (hsymm : ∀ i j, s i j = s j i)
    (hs : ∀ i j, i ≠ j → 0 ≤ s i j) (t : ℝ) :
    spectrum ℝ (normDivergence (diagonal π * ctmcTransition (gtrRate π s) t)) ⊆ Set.Ioi 0 := by
  open scoped Matrix.Norms.L2Operator in
  rw [normDivergence_gtr hπ hsymm hs t,
    ← CFC.real_exp_eq_normedSpace_exp (isSelfAdjoint_conj hπ hsymm t), cfc_map_spectrum _ _
      (isSelfAdjoint_conj hπ hsymm t)]
  rintro _ ⟨x, -, rfl⟩
  exact Real.exp_pos x

/-- At the true divergence matrix with `t ≠ 0`, `s > 0` off the diagonal and at least two
states, the log-det distance is nonzero. -/
theorem logDetDistance_gtr_ne_zero [Nontrivial ι] (hπ : ∀ i, 0 < π i)
    (hsymm : ∀ i j, s i j = s j i) (hs : ∀ i j, i ≠ j → 0 < s i j) {t : ℝ} (ht : t ≠ 0) :
    logDetDistance (diagonal π * ctmcTransition (gtrRate π s) t) ≠ 0 := by
  rw [logDetDistance_gtr hπ hsymm (fun i j h => (hs i j h).le) t]
  exact mul_ne_zero (neg_ne_zero.2 ht) (trace_gtrRate_neg hπ hs).ne

/-- **The log-det rate estimate is continuous at the true divergence matrix.** -/
theorem continuousAt_rateEstimate_gtr [Nontrivial ι] (hπ : ∀ i, 0 < π i)
    (hsymm : ∀ i j, s i j = s j i) (hs : ∀ i j, i ≠ j → 0 < s i j) {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt rateEstimate (diagonal π * ctmcTransition (gtrRate π s) t) := by
  have hs' : ∀ i j, i ≠ j → 0 ≤ s i j := fun i j h => (hs i j h).le
  refine continuousAt_rateEstimate (fun i => ?_) (spectrum_normDivergence_gtr hπ hsymm hs' t)
    (logDetDistance_gtr_ne_zero hπ hsymm hs ht)
  rw [baseFreq_gtr hπ hsymm hs' t]
  exact hπ i

/-- **The log-det distance is continuous at the true divergence matrix.** -/
theorem continuousAt_logDetDistance_gtr (hπ : ∀ i, 0 < π i) (hsymm : ∀ i j, s i j = s j i)
    (hs : ∀ i j, i ≠ j → 0 ≤ s i j) (t : ℝ) :
    ContinuousAt logDetDistance (diagonal π * ctmcTransition (gtrRate π s) t) := by
  refine continuousAt_logDetDistance (fun i => ?_) (spectrum_normDivergence_gtr hπ hsymm hs t)
  rw [baseFreq_gtr hπ hsymm hs t]
  exact hπ i

/-- **Recovery consistency**: for any divergence estimate `F̂` converging to the true divergence
matrix `Π exp (t • Q)` (with `t ≠ 0`, `s > 0` off the diagonal, at least two states), the
log-det rate estimate converges to `Q / (-tr Q)` and the log-det distance to `-t * tr Q`. -/
theorem tendsto_rateEstimate_gtr [Nontrivial ι] (hπ : ∀ i, 0 < π i)
    (hsymm : ∀ i j, s i j = s j i) (hs : ∀ i j, i ≠ j → 0 < s i j) {t : ℝ} (ht : t ≠ 0)
    {α : Type*} {l : Filter α} {F : α → Matrix ι ι ℝ}
    (hF : Tendsto F l (𝓝 (diagonal π * ctmcTransition (gtrRate π s) t))) :
    Tendsto (fun a => rateEstimate (F a)) l (𝓝 ((-(gtrRate π s).trace)⁻¹ • gtrRate π s)) ∧
      Tendsto (fun a => logDetDistance (F a)) l (𝓝 (-t * (gtrRate π s).trace)) := by
  have hs' : ∀ i j, i ≠ j → 0 ≤ s i j := fun i j h => (hs i j h).le
  refine ⟨?_, ?_⟩
  · rw [← rateEstimate_gtr hπ hsymm hs' ht]
    exact (continuousAt_rateEstimate_gtr hπ hsymm hs ht).tendsto.comp hF
  · rw [← logDetDistance_gtr hπ hsymm hs' t]
    exact (continuousAt_logDetDistance_gtr hπ hsymm hs' t).tendsto.comp hF

end Continuity

/-! ## Consistency from aligned site pairs -/

section Sampling

open Function

variable {π : ι → ℝ} {s : Matrix ι ι ℝ} [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- The **empirical divergence matrix** of the first `n` aligned site pairs, as a matrix. -/
noncomputable def empiricalDivergence (X : ℕ → Ω → ι × ι) (n : ℕ) (ω : Ω) : Matrix ι ι ℝ :=
  Matrix.of fun i j => GTRInference.empiricalFreq X n ω (i, j)

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace Ω] in
theorem continuous_reshape :
    Continuous fun p : ι × ι → ℝ => (Matrix.of fun i j => p (i, j) : Matrix ι ι ℝ) :=
  continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)

/-- **Recovery consistency from data (almost surely).** Let the aligned site pairs
`X i : Ω → ι × ι` be measurable, pairwise independent and identically distributed with the GTR
divergence law `P (X 0 = (i, j)) = π i * P(t) i j` (`t > 0`, `s > 0` off the diagonal, at least
two states; for `t < 0` this law has negative entries). Then almost surely the log-det rate
estimate of the empirical divergence matrix converges to `Q / (-tr Q)` and its log-det distance
to `-t * tr Q`. -/
theorem ae_tendsto_rateEstimate_empirical [Nontrivial ι] (hπ : ∀ i, 0 < π i)
    (hsymm : ∀ i j, s i j = s j i) (hs : ∀ i j, i ≠ j → 0 < s i j) {t : ℝ} (ht : 0 < t)
    {X : ℕ → Ω → ι × ι} (hX : ∀ i, Measurable (X i)) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hlaw : ∀ a : ι × ι, P.real (X 0 ⁻¹' {a}) = π a.1 * ctmcTransition (gtrRate π s) t a.1 a.2) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n => rateEstimate (empiricalDivergence X n ω)) atTop
          (𝓝 ((-(gtrRate π s).trace)⁻¹ • gtrRate π s)) ∧
        Tendsto (fun n => logDetDistance (empiricalDivergence X n ω)) atTop
          (𝓝 (-t * (gtrRate π s).trace)) := by
  filter_upwards [GTRInference.ae_tendsto_empiricalFreq hX hindep hident hlaw] with ω hω
  refine tendsto_rateEstimate_gtr hπ hsymm hs ht.ne' ?_
  have heq : diagonal π * ctmcTransition (gtrRate π s) t =
      Matrix.of fun i j => π i * ctmcTransition (gtrRate π s) t i j := by
    ext i j
    simp [diagonal_mul]
  rw [heq]
  exact (continuous_reshape.tendsto _).comp hω

/-- **Recovery consistency from data (in probability)**, entrywise: under the sampling law of
`ae_tendsto_rateEstimate_empirical`, every entry of the log-det rate estimate of the empirical
divergence matrix converges in probability to the corresponding entry of `Q / (-tr Q)`, and the
log-det distance converges in probability to `-t * tr Q`. -/
theorem tendstoInMeasure_rateEstimate_empirical [Nontrivial ι] (hπ : ∀ i, 0 < π i)
    (hsymm : ∀ i j, s i j = s j i) (hs : ∀ i j, i ≠ j → 0 < s i j) {t : ℝ} (ht : 0 < t)
    {X : ℕ → Ω → ι × ι} (hX : ∀ i, Measurable (X i)) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hlaw : ∀ a : ι × ι, P.real (X 0 ⁻¹' {a}) = π a.1 * ctmcTransition (gtrRate π s) t a.1 a.2) :
    (∀ i j, TendstoInMeasure P (fun n ω => rateEstimate (empiricalDivergence X n ω) i j) atTop
        fun _ => ((-(gtrRate π s).trace)⁻¹ • gtrRate π s) i j) ∧
      TendstoInMeasure P (fun n ω => logDetDistance (empiricalDivergence X n ω)) atTop
        fun _ => -t * (gtrRate π s).trace := by
  have hs' : ∀ i j, i ≠ j → 0 ≤ s i j := fun i j h => (hs i j h).le
  have hfreq := GTRInference.tendstoInMeasure_empiricalFreq hX hindep hident hlaw
  set p₀ : ι × ι → ℝ := fun a => π a.1 * ctmcTransition (gtrRate π s) t a.1 a.2
  have hreshape : (Matrix.of fun i j => p₀ (i, j) : Matrix ι ι ℝ) =
      diagonal π * ctmcTransition (gtrRate π s) t := by
    ext i j
    simp [p₀]
  have hcont : ContinuousAt (fun p : ι × ι → ℝ => (Matrix.of fun i j => p (i, j) : Matrix ι ι ℝ))
      p₀ := continuous_reshape.continuousAt
  refine ⟨fun i j => ?_, ?_⟩
  · have hg : ContinuousAt
        (fun p : ι × ι → ℝ => rateEstimate (Matrix.of fun i j => p (i, j)) i j) p₀ := by
      refine (continuous_id.matrix_elem i j).continuousAt.comp ?_
      refine ContinuousAt.comp (g := rateEstimate) ?_ hcont
      rw [hreshape]
      exact continuousAt_rateEstimate_gtr hπ hsymm hs ht.ne'
    have := TendstoInMeasure.comp_const_of_continuousAt hg hfreq
    simp only [hreshape, rateEstimate_gtr hπ hsymm hs' ht.ne'] at this
    exact this
  · have hg : ContinuousAt
        (fun p : ι × ι → ℝ => logDetDistance (Matrix.of fun i j => p (i, j))) p₀ := by
      refine ContinuousAt.comp (g := logDetDistance) ?_ hcont
      rw [hreshape]
      exact continuousAt_logDetDistance_gtr hπ hsymm hs' t
    have := TendstoInMeasure.comp_const_of_continuousAt hg hfreq
    simp only [hreshape, logDetDistance_gtr hπ hsymm hs' t] at this
    exact this

end Sampling

end MathlibExt.Biology.Phylogenetics.GTRLogDetRecovery
