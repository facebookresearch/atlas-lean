/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LDScoreRegression
public import MathlibExt.Biology.StatisticalGenetics.LDScoreVariance

/-!
# LD-score regression: `Var(ĥ²) → 0` from fourth moments and bounded LD scores

`LDScoreVariance` (T161) proves `Var(ĥ²) → 0` for the unweighted LD-score regression
estimator `ĥ² = b̂ · M / N` under its LD-block model `LDBlockModel`, which *assumes* the
fourth-moment bound `Var(χ²_j) ≤ V` on the association statistics directly. Its docstring
remarks that a uniform `V` should correspond to bounded LD scores `ℓ_j` with `N / M` and the
confounding term `N a` bounded. `LDScoreDesignSequence` (T206) obtains `V` from almost surely
bounded effects and noise. This file derives `V` from a fourth-moment condition on the scores
instead, with no bounded-support assumption, and with the LD scores entering the bound.

## The model extension

`LDScore.Model` fixes only second moments. The extension (`ScoreBlockModel`) is stated on the
scores `β̂_j = X_jᵀ y / N` (`betaHatStrat`), of which the statistics are the squares
`χ²_j = N β̂_j²` (`chiSqStrat`):

* **LD blocks / independence:** markers are partitioned into blocks of at most `K` markers, and
  scores of different blocks are independent (statistics of different blocks are then
  independent as functions of them);
* **finite fourth moments:** each score is in `L⁴`, so each statistic is in `L²`.

On top of it the LD-score regression theorems assume

* **a kurtosis bound:** `𝔼[(χ²_j)²] ≤ κ₄ (𝔼 χ²_j)²`. For a Gaussian score (of any mean)
  `𝔼[β̂⁴] ≤ 3 (𝔼 β̂²)²`, so `κ₄ = 3` covers Gaussian scores; that fact is not proved here;
* **bounded LD scores:** `ℓ_j ≤ L`, together with `N ≤ λ M` and `N a ≤ A`.

By the LD-score regression identity (`LDScoreRegression.integral_chiSqStrat_eq`),
`𝔼 χ²_j = 1 + N h² ℓ_j / M + N a - h² ≤ 1 + λ L + A`, so
`Var(χ²_j) ≤ 𝔼[(χ²_j)²] ≤ κ₄ (1 + λ L + A)²` uniformly in the design.

The `L⁴` field matters: Lean's integral of a non-integrable function is `0`, so without it the
kurtosis bound and a variance bound would hold vacuously for a score with infinite fourth
moment (see the test file).

## Main results

* `memLp_sq_of_memLp_four`, `variance_sq_le_integral`: `f ∈ L⁴` gives `f² ∈ L²` and
  `Var(a f²) ≤ 𝔼[(a f²)²]`.
* `ScoreBlockModel`, `ScoreBlockModel.toLDBlockModel`: the score-level model and the T161
  `LDBlockModel` it induces for the statistics `a β̂_j²`.
* `integral_chiSqStrat_le`: `0 ≤ 𝔼 χ²_j ≤ 1 + λ L + A` under bounded LD scores.
* `ldBlockModel_chiSqStrat`: the T161 model for `chiSqStrat` with `V = κ₄ (1 + λ L + A)²`.
* `variance_olsH2Hat_le_of_fourthMoment`: for one design,
  `Var(ĥ²) ≤ (M / N)² · K κ₄ (1 + λ L + A)² / S_ℓℓ`.
* `tendsto_variance_olsH2Hat_of_fourthMoment`: along designs with `M → ∞`,
  `κ M ≤ N ≤ λ M`, `S_ℓℓ ≥ c M`, bounded LD scores and confounding, and the fourth-moment
  model with uniform `K` and `κ₄`, `Var(ĥ²) → 0`.
* `tendstoInMeasure_olsH2Hat_of_fourthMoment`: under the same hypotheses, `ĥ² → h²` in
  probability (T147's `tendstoInMeasure_olsH2Hat` with its `hvar` discharged).

## References

* B. K. Bulik-Sullivan, P.-R. Loh, H. K. Finucane, S. Ripke, J. Yang, Schizophrenia Working
  Group of the Psychiatric Genomics Consortium, N. Patterson, M. J. Daly, A. L. Price,
  B. M. Neale, *LD Score regression distinguishes confounding from polygenicity in
  genome-wide association studies*, Nat. Genet. 47 (2015), 291–295.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open MathlibExt.Biology.StatisticalGenetics.LDScore
  MathlibExt.Biology.StatisticalGenetics.LDScoreInflation
  MathlibExt.Biology.StatisticalGenetics.LDScoreRegression
  MathlibExt.Biology.StatisticalGenetics.LDScoreVariance
  MathlibExt.Probability.FiniteProbability

namespace MathlibExt.Biology.StatisticalGenetics.LDScoreVarianceLimit

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Fourth moments -/

/-- The square of a random variable with finite fourth moment has finite second moment. -/
theorem memLp_sq_of_memLp_four {f : Ω → ℝ} (hf : MemLp f 4 μ) :
    MemLp (fun ω => f ω ^ 2) 2 μ := by
  have hm : AEStronglyMeasurable (fun ω => f ω ^ 2) μ := hf.aestronglyMeasurable.pow 2
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  have h : Integrable (fun ω => ‖f ω‖ ^ 4) μ :=
    MemLp.integrable_norm_pow (p := 4) (by exact_mod_cast hf) (by norm_num)
  refine h.congr (Eventually.of_forall fun ω => ?_)
  simp only
  rw [Real.norm_eq_abs, ← sq_abs (f ω)]
  ring

/-- For `f ∈ L⁴` and a probability measure, `Var(a f²) ≤ 𝔼[(a f²)²]`. -/
theorem variance_sq_le_integral [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 4 μ)
    (a : ℝ) : Var[fun ω => a * f ω ^ 2; μ] ≤ ∫ ω, (a * f ω ^ 2) ^ 2 ∂μ :=
  variance_le_expectation_sq ((memLp_sq_of_memLp_four hf).const_mul a).aestronglyMeasurable

/-! ### The score-level model -/

/-- **Score-level LD-block model** (the fourth-moment / independence extension of
`LDScore.Model`) for scores `z : Fin M → Ω → ℝ`: the markers are partitioned into blocks of at
most `K` markers, scores of markers in different blocks are independent, and every score has a
finite fourth moment. -/
structure ScoreBlockModel {M : ℕ} (μ : Measure Ω) (z : Fin M → Ω → ℝ) (K : ℕ) where
  /-- The LD block of each marker. -/
  block : Fin M → ℕ
  /-- Every LD block has at most `K` markers. -/
  card_block_le : ∀ j, #{k | block k = block j} ≤ K
  /-- Scores of markers in different LD blocks are independent. -/
  indepFun : ∀ j k, block j ≠ block k → IndepFun (z j) (z k) μ
  /-- Every score has a finite fourth moment. -/
  memLp : ∀ j, MemLp (z j) 4 μ

namespace ScoreBlockModel

variable {M K : ℕ} {z : Fin M → Ω → ℝ}

/-- **From scores to statistics.** A score-level model induces T161's `LDBlockModel` for the
statistics `a z_j²`, with any `V` bounding their second moments `𝔼[(a z_j²)²]`. -/
def toLDBlockModel [IsProbabilityMeasure μ] (S : ScoreBlockModel μ z K) (a : ℝ) {V : ℝ}
    (hV : ∀ j, ∫ ω, (a * z j ω ^ 2) ^ 2 ∂μ ≤ V) :
    LDBlockModel μ (fun j ω => a * z j ω ^ 2) K V where
  block := S.block
  card_block_le := S.card_block_le
  indepFun j k h :=
    (S.indepFun j k h).comp (φ := fun x : ℝ => a * x ^ 2) (ψ := fun x : ℝ => a * x ^ 2)
      (measurable_const.mul (measurable_id.pow_const 2))
      (measurable_const.mul (measurable_id.pow_const 2))
  memLp j := (memLp_sq_of_memLp_four (S.memLp j)).const_mul a
  variance_le j := (variance_sq_le_integral (S.memLp j) a).trans (hV j)

@[simp]
theorem toLDBlockModel_block [IsProbabilityMeasure μ] (S : ScoreBlockModel μ z K) (a : ℝ)
    {V : ℝ} (hV : ∀ j, ∫ ω, (a * z j ω ^ 2) ^ 2 ∂μ ≤ V) :
    (S.toLDBlockModel a hV).block = S.block := rfl

end ScoreBlockModel

/-! ### Bounded LD scores bound the expected statistics -/

variable {N M : ℕ}

/-- **Bounded LD bounds the expected statistic.** For a probability measure, mean-zero effects
and noise, a standardized genotype matrix, `N ≠ 0`, a common confounding term `a`, LD scores at
most `L`, `N ≤ λ M` and `N a ≤ A`: `0 ≤ 𝔼 χ²_j ≤ 1 + λ L + A`. -/
theorem integral_chiSqStrat_le [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hX : IsStandardized X)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (s : ℝ)
    (c : Fin N → ℝ) {a : ℝ} (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a)
    {L lam A : ℝ} (hL : ∀ j, ldScore X j ≤ L) (hNM : (N : ℝ) ≤ lam * M) (hA : N * a ≤ A)
    (j : Fin M) :
    0 ≤ ∫ ω, chiSqStrat D X s c j ω ∂μ ∧ ∫ ω, chiSqStrat D X s c j ω ∂μ ≤ 1 + lam * L + A := by
  refine ⟨integral_nonneg fun ω => by unfold chiSqStrat; positivity, ?_⟩
  rw [integral_chiSqStrat_eq D X hN hX hβ hε s c ha j]
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (Fin.pos j)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have h0 := D.h2_nonneg (Fin.pos j)
  have h1 := D.h2_le_one (Nat.pos_of_ne_zero hN)
  have hℓ1 := hX.one_le_ldScore hN j
  have hℓL := hL j
  have hlam : 0 ≤ lam := by
    by_contra h
    have h' := not_le.mp h
    nlinarith
  -- `N h² ℓ_j ≤ λ M L`
  have key : (N : ℝ) * D.h2 * ldScore X j ≤ lam * M * L := by
    have e1 : (N : ℝ) * D.h2 * ldScore X j ≤ N * ldScore X j := by
      have : (N : ℝ) * D.h2 ≤ N * 1 := mul_le_mul_of_nonneg_left h1 hNpos.le
      nlinarith
    have e2 : (N : ℝ) * ldScore X j ≤ N * L := mul_le_mul_of_nonneg_left hℓL hNpos.le
    have e3 : (N : ℝ) * L ≤ lam * M * L := mul_le_mul_of_nonneg_right hNM (by linarith)
    linarith
  have hdiv : (N : ℝ) * D.h2 * ldScore X j / M ≤ lam * L := by
    rw [div_le_iff₀ hMpos]
    linarith
  linarith

/-- **The T161 LD-block model for LD-score regression, from fourth moments.** Under a
score-level model for the scores `β̂_j` (`betaHatStrat`) with block size at most `K`, the
kurtosis bound `𝔼[(χ²_j)²] ≤ κ₄ (𝔼 χ²_j)²`, LD scores at most `L`, `N ≤ λ M` and `N a ≤ A`, the
statistics `χ²_j` (`chiSqStrat`) satisfy T161's `LDBlockModel` with
`V = κ₄ (1 + λ L + A)²`. -/
noncomputable def ldBlockModel_chiSqStrat [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hX : IsStandardized X)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (s : ℝ)
    (c : Fin N → ℝ) {a : ℝ} (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) {K : ℕ}
    (S : ScoreBlockModel μ (betaHatStrat D X s c) K) {κ₄ L lam A : ℝ} (hκ₄ : 0 ≤ κ₄)
    (hkurt : ∀ j, ∫ ω, chiSqStrat D X s c j ω ^ 2 ∂μ ≤
      κ₄ * (∫ ω, chiSqStrat D X s c j ω ∂μ) ^ 2)
    (hL : ∀ j, ldScore X j ≤ L) (hNM : (N : ℝ) ≤ lam * M) (hA : N * a ≤ A) :
    LDBlockModel μ (chiSqStrat D X s c) K (κ₄ * (1 + lam * L + A) ^ 2) :=
  S.toLDBlockModel N fun j => by
    obtain ⟨h0, h1⟩ := integral_chiSqStrat_le D X hN hX hβ hε s c ha hL hNM hA j
    exact (hkurt j).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 2) hκ₄)

/-! ### Variance bound and limit -/

/-- **Variance bound for one design.** Under the hypotheses of `ldBlockModel_chiSqStrat`,
`Var(ĥ²) ≤ (M / N)² · (K κ₄ (1 + λ L + A)² / S_ℓℓ)`. -/
theorem variance_olsH2Hat_le_of_fourthMoment [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hX : IsStandardized X)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (s : ℝ)
    (c : Fin N → ℝ) {a : ℝ} (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) {K : ℕ}
    (S : ScoreBlockModel μ (betaHatStrat D X s c) K) {κ₄ L lam A : ℝ} (hκ₄ : 0 ≤ κ₄)
    (hkurt : ∀ j, ∫ ω, chiSqStrat D X s c j ω ^ 2 ∂μ ≤
      κ₄ * (∫ ω, chiSqStrat D X s c j ω ∂μ) ^ 2)
    (hL : ∀ j, ldScore X j ≤ L) (hNM : (N : ℝ) ≤ lam * M) (hA : N * a ≤ A) :
    Var[fun ω => olsH2Hat N M (ldScore X) fun j => chiSqStrat D X s c j ω; μ] ≤
      ((M : ℝ) / N) ^ 2 * (K * (κ₄ * (1 + lam * L + A) ^ 2) / sxy (ldScore X) (ldScore X)) :=
  let B := ldBlockModel_chiSqStrat D X hN hX hβ hε s c ha S hκ₄ hkurt hL hNM hA
  variance_h2Hat_le (ldScore X) B.memLp B.sum_abs_covariance_le fun _ => rfl

/-- **`Var(ĥ²) → 0` as `M → ∞` from fourth moments and bounded LD scores.** Along a family of
designs with `M → ∞`, `κ M ≤ N ≤ λ M` (`κ > 0`), LD-score spread `S_ℓℓ ≥ c₀ M` (`c₀ > 0`),
LD scores at most `L`, confounding `N a ≤ A`, and scores satisfying the score-level model with
block size at most `K` and the kurtosis bound with constant `κ₄`, all uniform in the design,
the variance of the unweighted LD-score regression estimator tends to `0`. -/
theorem tendsto_variance_olsH2Hat_of_fourthMoment [IsProbabilityMeasure μ] {ι : Type*}
    {l : Filter ι} {N M : ι → ℕ} (D : ∀ n, Model μ (N n) (M n))
    (X : ∀ n, Matrix (Fin (N n)) (Fin (M n)) ℝ) (hN : ∀ n, N n ≠ 0)
    (hX : ∀ n, IsStandardized (X n)) (hβ : ∀ n k, ∫ ω, (D n).beta k ω ∂μ = 0)
    (hε : ∀ n i, ∫ ω, (D n).eps i ω ∂μ = 0) (s : ι → ℝ) (c : ∀ n, Fin (N n) → ℝ) (a : ι → ℝ)
    (ha : ∀ n j, s n ^ 2 * ((∑ i, X n i j * c n i) / N n) ^ 2 = a n) {K : ℕ}
    (S : ∀ n, ScoreBlockModel μ (betaHatStrat (D n) (X n) (s n) (c n)) K)
    {κ₄ L lam A : ℝ} (hκ₄ : 0 ≤ κ₄)
    (hkurt : ∀ n j, ∫ ω, chiSqStrat (D n) (X n) (s n) (c n) j ω ^ 2 ∂μ ≤
      κ₄ * (∫ ω, chiSqStrat (D n) (X n) (s n) (c n) j ω ∂μ) ^ 2)
    (hL : ∀ n j, ldScore (X n) j ≤ L) (hNMle : ∀ n, (N n : ℝ) ≤ lam * M n)
    (hA : ∀ n, N n * a n ≤ A) {c₀ κ : ℝ} (hc₀ : 0 < c₀) (hκ : 0 < κ)
    (hspread : ∀ n, c₀ * M n ≤ sxy (ldScore (X n)) (ldScore (X n)))
    (hNM : ∀ n, κ * M n ≤ N n) (hM : Tendsto M l atTop) :
    Tendsto (fun n => Var[fun ω =>
      olsH2Hat (N n) (M n) (ldScore (X n)) fun j => chiSqStrat (D n) (X n) (s n) (c n) j ω; μ])
      l (𝓝 0) :=
  tendsto_variance_h2Hat_of_ldBlock (fun n => ldScore (X n))
    (fun n => ldBlockModel_chiSqStrat (D n) (X n) (hN n) (hX n) (hβ n) (hε n) (s n) (c n)
      (ha n) (S n) hκ₄ (hkurt n) (hL n) (hNMle n) (hA n))
    hc₀ hκ hspread hNM hM fun _ _ => rfl

/-- **Consistency of LD-score regression from fourth moments and bounded LD scores.** Under the
hypotheses of `tendsto_variance_olsH2Hat_of_fourthMoment`, with common heritability `h²` and at
least one marker in every design, `ĥ² → h²` in probability. This is T147's
`tendstoInMeasure_olsH2Hat` with its variance hypothesis discharged through T161. -/
theorem tendstoInMeasure_olsH2Hat_of_fourthMoment [IsProbabilityMeasure μ] {ι : Type*}
    {l : Filter ι} {N M : ι → ℕ} (D : ∀ n, Model μ (N n) (M n))
    (X : ∀ n, Matrix (Fin (N n)) (Fin (M n)) ℝ) {h2 : ℝ} (hh2 : ∀ n, (D n).h2 = h2)
    (hN : ∀ n, N n ≠ 0) (hM0 : ∀ n, M n ≠ 0)
    (hX : ∀ n, IsStandardized (X n)) (hβ : ∀ n k, ∫ ω, (D n).beta k ω ∂μ = 0)
    (hε : ∀ n i, ∫ ω, (D n).eps i ω ∂μ = 0) (s : ι → ℝ) (c : ∀ n, Fin (N n) → ℝ) (a : ι → ℝ)
    (ha : ∀ n j, s n ^ 2 * ((∑ i, X n i j * c n i) / N n) ^ 2 = a n) {K : ℕ}
    (S : ∀ n, ScoreBlockModel μ (betaHatStrat (D n) (X n) (s n) (c n)) K)
    {κ₄ L lam A : ℝ} (hκ₄ : 0 ≤ κ₄)
    (hkurt : ∀ n j, ∫ ω, chiSqStrat (D n) (X n) (s n) (c n) j ω ^ 2 ∂μ ≤
      κ₄ * (∫ ω, chiSqStrat (D n) (X n) (s n) (c n) j ω ∂μ) ^ 2)
    (hL : ∀ n j, ldScore (X n) j ≤ L) (hNMle : ∀ n, (N n : ℝ) ≤ lam * M n)
    (hA : ∀ n, N n * a n ≤ A) {c₀ κ : ℝ} (hc₀ : 0 < c₀) (hκ : 0 < κ)
    (hspread : ∀ n, c₀ * M n ≤ sxy (ldScore (X n)) (ldScore (X n)))
    (hNM : ∀ n, κ * M n ≤ N n) (hM : Tendsto M l atTop) :
    TendstoInMeasure μ (fun n ω =>
      olsH2Hat (N n) (M n) (ldScore (X n)) fun j => chiSqStrat (D n) (X n) (s n) (c n) j ω)
      l fun _ => h2 := by
  have hℓ : ∀ n, sxy (ldScore (X n)) (ldScore (X n)) ≠ 0 := fun n => by
    have hMpos : (0 : ℝ) < M n := by exact_mod_cast Nat.pos_of_ne_zero (hM0 n)
    exact (lt_of_lt_of_le (mul_pos hc₀ hMpos) (hspread n)).ne'
  refine tendstoInMeasure_olsH2Hat D X hh2 hN hM0 hX hℓ hβ hε s c a ha ?_
  exact tendsto_evariance_h2Hat_chiSqStrat D X s c
    (fun n => ldBlockModel_chiSqStrat (D n) (X n) (hN n) (hX n) (hβ n) (hε n) (s n) (c n)
      (ha n) (S n) hκ₄ (hkurt n) (hL n) (hNMle n) (hA n))
    hc₀ hκ hspread hNM hM fun _ _ => rfl

end MathlibExt.Biology.StatisticalGenetics.LDScoreVarianceLimit
