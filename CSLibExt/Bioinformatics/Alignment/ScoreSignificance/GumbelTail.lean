/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Distributions.Exponential

/-!
# Gumbel tail of the maximal segment score

For a score sequence `x 0, x 1, …` the **maximal segment score** of the first `n` scores is
`Mₙ = max_{0 ≤ i ≤ j ≤ n} (x i + ⋯ + x (j - 1))` (`maxSegmentScore`; the empty segment is
allowed, so `Mₙ ≥ 0`). For i.i.d. scores `X` with negative mean and a Cramér root `θ > 0`
(`E e^{θ X} = 1`), Iglehart (1972) and Karlin–Dembo (1992) proved

* **nonlattice scores**: `P(Mₙ ≤ log n / θ + x) → exp (-K e^{-θ x})` for every `x`;
* **lattice scores** (span `h`): there is no limit in general; instead
  `exp (-K e^{-θ x}) ≤ liminf ≤ limsup ≤ exp (-K e^{-θ (x + h)})`.

The constant is `K = C / A`, where `A` is the mean length of a ladder excursion (the mean
descending ladder epoch) and `C` is the renewal constant of the excursion-height tail
`P(Y > t) ~ C e^{-θ t}`. Renewal theory expresses `C` through the ladder-height distribution
(Cramér root, tilted ladder-height mean, span); that computation is not formalized here.

## Proof structure and what is assumed

The classical proof has two parts.

1. *Renewal / regenerative input* (assumed). Cut the random walk `Sₖ = X 0 + ⋯ + X (k - 1)` at
   its descending ladder epochs. The excursion heights `Y i` are i.i.d., the renewal theorem
   gives their tail `P(Y > t) ~ C e^{-θ t}` (nonlattice) or `P(Y ≥ (k + 1) h) ~
   C e^{-θ (k + 1) h}` (lattice), the number `N n` of excursions completed by time `n`
   satisfies `N n / n → 1 / A` in probability, and pathwise
   `max_{i < N n} Y i ≤ Mₙ ≤ max_{i ≤ N n} Y i`. These facts are bundled as explicit
   hypotheses: `LadderInput` (independence, distribution function `F`, ladder-count law of large
   numbers, pathwise sandwich) and the tail hypotheses of the theorems. They are *not* derived
   from the scores here.
2. *Extreme-value step* (proved). From the ladder input alone, if `n (1 - F tₙ)` has liminf
   `≥ c₁` and limsup `≤ c₂`, then `liminf P(Mₙ ≤ tₙ) ≥ exp (-c₂ / A)` and
   `limsup P(Mₙ ≤ tₙ) ≤ exp (-c₁ / A)`, along any filter `L ≤ atTop`. Taking
   `tₙ = log n / θ + x` gives the Gumbel limit in the nonlattice case; in the lattice case
   `n (1 - F tₙ) = (C + o(1)) e^{-θ x} e^{-θ h (1 - {tₙ / h})}` oscillates with the fractional
   part `{tₙ / h}`, which is dense in `[0, 1)` because `log (n + 1) - log n → 0`.

## Main results

* `LadderInput.tendsto_real_le_log_div_add`: **nonlattice Gumbel limit**
  `P(Mₙ ≤ log n / θ + x) → exp (-(C / A) e^{-θ x})`.
* `LadderInput.eventually_lattice_bounds`: **lattice liminf/limsup bounds**.
* `LadderInput.frequently_lattice_le`, `LadderInput.frequently_le_lattice`: both lattice bounds
  are approached infinitely often, so they are the exact liminf and limsup.
* `LadderInput.not_tendsto_lattice`: for `C > 0` the lattice probabilities do not converge.
* `NonlatticeRenewalInput.tendsto_gumbel`, `LatticeRenewalInput.eventually_bounds`,
  `LatticeRenewalInput.frequently_bounds`, `LatticeRenewalInput.not_tendsto`: the same
  statements for `Mₙ = maxSegmentScore` of i.i.d. scores satisfying `CramerScores`.
* `mgf_sub_eq_one`: for two-sided exponential scores `X = E₁ - E₂`, `E₁ ~ Exp(a)`,
  `E₂ ~ Exp(b)`, `0 < b < a`, the Cramér root is `θ = a - b`; `tendsto_tail_of_eq_exp`:
  exponential excursion tails `P(Y > t) = p e^{-θ t}` have renewal constant `C = p`.

## Scope: not a BLAST E-value theorem

This is the *single-sequence* theory: one i.i.d. score sequence and its best segment. The BLAST
E-value `K m n e^{-λ S}` concerns local alignments of *two* sequences (Dembo–Karlin–Zeitouni
1994), whose scores are not a single i.i.d. walk; nothing here proves it, and no universal
E-value statement is claimed.

## Reuse search

Pinned Mathlib v4.35.0, CSLib and the Atlas libraries (searched 2026-11-11) contain no
extreme-value, ladder-variable or Cramér-root development. `IsMaxSubarraySum`
(`CSLibExt.Algorithms.Lean.DynamicProgramming.MaximumSubarray`) is the maximum over *nonempty*
runs of a list; `maxSegmentScore` allows the empty segment and is indexed by prefixes of an
infinite sequence, as in the probabilistic literature. Independence, moment generating functions
and the exponential distribution are Mathlib's `iIndepFun`, `mgf` and `expMeasure`.

## References

* D. L. Iglehart, *Extreme values in the GI/G/1 queue*, Ann. Math. Statist. 43 (1972),
  627–635.
* S. Karlin and A. Dembo, *Limit distributions of maximal segmental score among Markov-dependent
  partial sums*, Adv. Appl. Probab. 24 (1992), 113–140, Theorem 1.
* S. Karlin and S. F. Altschul, *Methods for assessing the statistical significance of molecular
  sequence features by using general scoring schemes*, PNAS 87 (1990), 2264–2268.
* A. Dembo, S. Karlin and O. Zeitouni, *Limit distribution of maximal non-aligned two-sequence
  segmental score*, Ann. Probab. 22 (1994), 2022–2039.
* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II, 2nd ed.,
  Wiley, 1971, §§XI–XII (renewal theorem, ladder variables).
-/

@[expose] public section

namespace Cslib.Bioinformatics.Alignment.ScoreSignificance

open MeasureTheory ProbabilityTheory Filter Topology

/-- The score `x i + ⋯ + x (j - 1)` of the segment `[i, j)` of a score sequence `x`; it is `0`
when `j ≤ i` (the empty segment). -/
def segmentScore (x : ℕ → ℝ) (i j : ℕ) : ℝ := ∑ k ∈ Finset.Ico i j, x k

/-- The maximal segment score `Mₙ = max_{0 ≤ i ≤ j ≤ n} (x i + ⋯ + x (j - 1))` of the first `n`
scores `x 0, …, x (n - 1)`. The empty segment is allowed, so `Mₙ ≥ 0`.

This is the same quantity as T49's `maxSegScore (List.ofFn fun i : Fin n => x i)`; it is restated
here because T49 is not on `main`. TODO: prove the equality once T49 lands. -/
noncomputable def maxSegmentScore (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).sup' ⟨(0, 0), by simp⟩
    fun p => segmentScore x p.1 p.2

/-- Every segment of the first `n` scores scores at most `Mₙ`. -/
theorem segmentScore_le_maxSegmentScore {x : ℕ → ℝ} {n i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) :
    segmentScore x i j ≤ maxSegmentScore x n :=
  Finset.le_sup' (fun p : ℕ × ℕ => segmentScore x p.1 p.2) (b := (i, j))
    (Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩)

/-- `Mₙ ≥ 0`: the empty segment scores `0`. -/
theorem zero_le_maxSegmentScore (x : ℕ → ℝ) (n : ℕ) : 0 ≤ maxSegmentScore x n := by
  simpa [segmentScore] using
    segmentScore_le_maxSegmentScore (x := x) (i := 0) (j := 0) (Nat.zero_le n) (Nat.zero_le n)

/-- `Mₙ` is nondecreasing in `n`. -/
theorem maxSegmentScore_mono (x : ℕ → ℝ) : Monotone (maxSegmentScore x) := fun m n h =>
  Finset.sup'_le _ _ fun p hp => by
    simp only [Finset.mem_product, Finset.mem_range] at hp
    exact segmentScore_le_maxSegmentScore (by omega) (by omega)

/-- **Ladder (regenerative) input** for a maximal-segment-type score `M n ω`: the regenerative
structure that the descending ladder epochs of the score walk provide, taken as a hypothesis.
The excursion heights `Y i` are i.i.d. with distribution function `F`, the number `N n` of
excursions completed by time `n` satisfies `N n / n → 1 / A` in probability, and pathwise
`max_{i < N n} Y i ≤ M n ≤ max_{i ≤ N n} Y i`. -/
structure LadderInput {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : ℕ → Ω → ℝ) where
  /-- The maximal height `Y i` of the `i`-th ladder excursion. -/
  Y : ℕ → Ω → ℝ
  /-- The number `N n` of ladder excursions completed by time `n`. -/
  N : ℕ → Ω → ℕ
  /-- The distribution function of an excursion height. -/
  F : ℝ → ℝ
  /-- The mean length of a ladder excursion (mean ladder epoch). -/
  A : ℝ
  /-- The mean excursion length is positive. -/
  A_pos : 0 < A
  /-- Each excursion height is measurable. -/
  measurable_Y : ∀ i, Measurable (Y i)
  /-- The excursion heights are independent. -/
  iIndepFun_Y : iIndepFun Y P
  /-- Every excursion height has distribution function `F`. -/
  real_Y_le : ∀ i t, P.real {ω | Y i ω ≤ t} = F t
  /-- Ladder-count law of large numbers: `N n / n → 1 / A` in probability. -/
  count_lln : ∀ ε > 0,
    Tendsto (fun n : ℕ => P.real {ω | ε ≤ |(N n ω : ℝ) / n - A⁻¹|}) atTop (𝓝 0)
  /-- Upper half of the pathwise sandwich: `Mₙ ≤ max_{i ≤ N n} Y i` (the last, incomplete
  excursion is dominated by the complete excursion containing it). -/
  le_of_forall_le : ∀ᵐ ω ∂P, ∀ n t, (∀ i ≤ N n ω, Y i ω ≤ t) → M n ω ≤ t
  /-- Lower half of the pathwise sandwich: `max_{i < N n} Y i ≤ Mₙ`. -/
  le_of_lt_count : ∀ᵐ ω ∂P, ∀ n, ∀ i < N n ω, Y i ω ≤ M n ω

namespace LadderInput

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {M : ℕ → Ω → ℝ}

/-- Independence: `P(Y 0, …, Y (m - 1) ≤ t) = F(t)^m`. -/
theorem real_forall_lt_le [IsProbabilityMeasure P] (I : LadderInput P M) (m : ℕ) (t : ℝ) :
    P.real {ω | ∀ i < m, I.Y i ω ≤ t} = I.F t ^ m := by
  have hset : {ω | ∀ i < m, I.Y i ω ≤ t} = ⋂ i ∈ Finset.range m, I.Y i ⁻¹' Set.Iic t := by
    ext ω; simp
  rw [hset, measureReal_def, I.iIndepFun_Y.meas_biInter
    (fun i _ => ⟨Set.Iic t, measurableSet_Iic, rfl⟩), ENNReal.toReal_prod]
  simp only [← measureReal_def]
  have h : ∀ i, P.real (I.Y i ⁻¹' Set.Iic t) = I.F t := fun i => I.real_Y_le i t
  simp only [h, Finset.prod_const, Finset.card_range]

/-- `F ≥ 0`. -/
theorem F_nonneg [IsProbabilityMeasure P] (I : LadderInput P M) (t : ℝ) : 0 ≤ I.F t :=
  I.real_Y_le 0 t ▸ measureReal_nonneg

/-- `F ≤ 1`. -/
theorem F_le_one [IsProbabilityMeasure P] (I : LadderInput P M) (t : ℝ) : I.F t ≤ 1 :=
  I.real_Y_le 0 t ▸ measureReal_le_one

/-- Upper sandwich: if at least `m` excursions are complete, all their heights are `≤ Mₙ`. -/
theorem real_le_le [IsProbabilityMeasure P] (I : LadderInput P M) (n m : ℕ) (t : ℝ) :
    P.real {ω | M n ω ≤ t} ≤ I.F t ^ m + P.real {ω | I.N n ω < m} := by
  rw [← I.real_forall_lt_le m t]
  refine le_trans ?_ (measureReal_union_le _ _)
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  filter_upwards [I.le_of_lt_count] with ω hω hM
  by_cases h : I.N n ω < m
  · exact Or.inr h
  · exact Or.inl fun i hi => (hω n i (by omega)).trans hM

/-- Lower sandwich: if fewer than `m` excursions are complete, `Mₙ` is at most the largest
of the first `m` excursion heights. -/
theorem le_real_le [IsProbabilityMeasure P] (I : LadderInput P M) (n m : ℕ) (t : ℝ) :
    I.F t ^ m - P.real {ω | m ≤ I.N n ω} ≤ P.real {ω | M n ω ≤ t} := by
  rw [← I.real_forall_lt_le m t, sub_le_iff_le_add]
  refine le_trans ?_ (measureReal_union_le _ _)
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  filter_upwards [I.le_of_forall_le] with ω hω hY
  by_cases h : m ≤ I.N n ω
  · exact Or.inr h
  · exact Or.inl (hω n t fun i hi => hY i (by omega))

private theorem tendsto_real_count_lt [IsProbabilityMeasure P] (I : LadderInput P M) {η : ℝ}
    (hη : 0 < η) :
    Tendsto (fun n : ℕ => P.real {ω | I.N n ω < ⌊(1 - η) * n / I.A⌋₊}) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (I.count_lln (η / I.A) (div_pos hη I.A_pos))
    (Eventually.of_forall fun _ => measureReal_nonneg) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  refine measureReal_mono fun ω (hω : I.N n ω < _) => ?_
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hA := I.A_pos
  have h1 : (I.N n ω : ℝ) < (1 - η) * n / I.A := Nat.lt_of_lt_floor hω
  have h2 : (I.N n ω : ℝ) / n < (1 - η) / I.A := by
    rw [div_lt_div_iff₀ hn' hA]; rw [lt_div_iff₀ hA] at h1; linarith
  have h3 : η / I.A = I.A⁻¹ - (1 - η) / I.A := by field_simp; ring
  change η / I.A ≤ |(I.N n ω : ℝ) / n - I.A⁻¹|
  rw [abs_sub_comm]; exact le_trans (by linarith) (le_abs_self _)

private theorem tendsto_real_ceil_le_count [IsProbabilityMeasure P] (I : LadderInput P M) {η : ℝ}
    (hη : 0 < η) :
    Tendsto (fun n : ℕ => P.real {ω | ⌈(1 + η) * n / I.A⌉₊ ≤ I.N n ω}) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (I.count_lln (η / I.A) (div_pos hη I.A_pos))
    (Eventually.of_forall fun _ => measureReal_nonneg) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  refine measureReal_mono fun ω (hω : ⌈_⌉₊ ≤ I.N n ω) => ?_
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hA := I.A_pos
  have h1 : (1 + η) * n / I.A ≤ (I.N n ω : ℝ) := Nat.ceil_le.1 hω
  have h2 : (1 + η) / I.A ≤ (I.N n ω : ℝ) / n := by
    rw [div_le_div_iff₀ hA hn']; rw [div_le_iff₀ hA] at h1; linarith
  have h3 : η / I.A = (1 + η) / I.A - I.A⁻¹ := by field_simp; ring
  change η / I.A ≤ |(I.N n ω : ℝ) / n - I.A⁻¹|
  exact le_trans (by linarith) (le_abs_self _)

private theorem tendsto_tail_zero [IsProbabilityMeasure P] (I : LadderInput P M) {L : Filter ℕ}
    (hL : L ≤ atTop) {t : ℕ → ℝ} {chi : ℝ}
    (hhi : ∀ δ > 0, ∀ᶠ n : ℕ in L, (n : ℝ) * (1 - I.F (t n)) ≤ chi + δ) :
    Tendsto (fun n => 1 - I.F (t n)) L (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ => (chi + 1) / (n : ℝ)) L (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (chi + 1)).mono_left hL
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
    (Eventually.of_forall fun n => sub_nonneg.2 (I.F_le_one _)) ?_
  filter_upwards [hhi 1 one_pos, hL (eventually_ge_atTop 1)] with n hn h1
  have hn' : (0 : ℝ) < n := by exact_mod_cast h1
  rw [le_div_iff₀ hn']; linarith

/-- **Extreme-value upper bound.** If `liminf n (1 - F tₙ) ≥ c` along `L` (`hlo`), then
`limsup P(Mₙ ≤ tₙ) ≤ exp (-c / A)` along `L`. The limsup bound `hhi` (some finite `chi`) is
also required: it gives `1 - F tₙ → 0`. -/
theorem eventually_real_le_le [IsProbabilityMeasure P] (I : LadderInput P M) {L : Filter ℕ}
    (hL : L ≤ atTop) (t : ℕ → ℝ) {clo chi : ℝ}
    (hlo : ∀ δ > 0, ∀ᶠ n in L, clo - δ ≤ n * (1 - I.F (t n)))
    (hhi : ∀ δ > 0, ∀ᶠ n : ℕ in L, (n : ℝ) * (1 - I.F (t n)) ≤ chi + δ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in L, P.real {ω | M n ω ≤ t n} ≤ Real.exp (-(clo / I.A)) + ε := by
  have hA := I.A_pos
  set g : ℝ → ℝ := fun η => Real.exp (-((1 - η) * (clo - η) / I.A)) with hg_def
  have hg : Tendsto g (𝓝[>] 0) (𝓝 (Real.exp (-(clo / I.A)))) := by
    have hc : Continuous g := by fun_prop
    simpa [g] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨η, hgη, hη⟩ := ((hg.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε3))).and
    (Ioo_mem_nhdsGT one_pos : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] 0)).exists
  have hp := I.tendsto_tail_zero hL hhi
  have hexp : Tendsto (fun n => g η * Real.exp (1 - I.F (t n))) L (𝓝 (g η)) := by
    simpa using tendsto_const_nhds.mul ((Real.continuous_exp.tendsto 0).comp hp)
  have hcount := (I.tendsto_real_count_lt hη.1).mono_left hL
  filter_upwards [hexp.eventually (gt_mem_nhds (lt_add_of_pos_right (g η) hε3)),
    hcount.eventually (gt_mem_nhds hε3), hlo η hη.1] with n h1 h2 h3
  set p := 1 - I.F (t n) with hp_def
  set m := ⌊(1 - η) * n / I.A⌋₊
  have hp0 : 0 ≤ p := sub_nonneg.2 (I.F_le_one _)
  have hF : I.F (t n) ^ m ≤ Real.exp (-(m * p)) := by
    rw [show -(m * p) = m * (-p) by ring, Real.exp_nat_mul,
      show I.F (t n) = 1 - p by rw [hp_def]; ring]
    exact pow_le_pow_left₀ (by linarith [I.F_nonneg (t n)]) (Real.one_sub_le_exp_neg p) m
  have hy : ((1 - η) * n / I.A - 1) * p ≤ m * p :=
    mul_le_mul_of_nonneg_right (by linarith [Nat.lt_floor_add_one ((1 - η) * n / I.A)]) hp0
  have hc : (1 - η) * (clo - η) / I.A ≤ (1 - η) * n / I.A * p := by
    rw [div_mul_eq_mul_div, mul_assoc]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by linarith [hη.2])) hA.le
  have hE : Real.exp (-(m * p)) ≤ g η * Real.exp p := by
    rw [hg_def, ← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  linarith [I.real_le_le n m (t n)]

/-- **Extreme-value lower bound.** If `limsup n (1 - F tₙ) ≤ c` along `L`, then
`liminf P(Mₙ ≤ tₙ) ≥ exp (-c / A)` along `L`. -/
theorem eventually_le_real_le [IsProbabilityMeasure P] (I : LadderInput P M) {L : Filter ℕ}
    (hL : L ≤ atTop) (t : ℕ → ℝ) {chi : ℝ}
    (hhi : ∀ δ > 0, ∀ᶠ n : ℕ in L, (n : ℝ) * (1 - I.F (t n)) ≤ chi + δ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in L, Real.exp (-(chi / I.A)) - ε ≤ P.real {ω | M n ω ≤ t n} := by
  have hA := I.A_pos
  set g : ℝ → ℝ := fun η => Real.exp (-((1 + η) * (chi + η) / I.A + η)) with hg_def
  have hg : Tendsto g (𝓝[>] 0) (𝓝 (Real.exp (-(chi / I.A)))) := by
    have hc : Continuous g := by fun_prop
    simpa [g] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨η, hgη, hη⟩ := ((hg.eventually (lt_mem_nhds (sub_lt_self _ hε2))).and
    (Ioo_mem_nhdsGT one_pos : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] 0)).exists
  have hp := I.tendsto_tail_zero hL hhi
  set B := (1 + η) * (chi + η) / I.A
  have hh : Tendsto (fun n => (B + (1 - I.F (t n))) / (1 - (1 - I.F (t n)))) L (𝓝 B) := by
    have h := ((tendsto_const_nhds (x := B)).add hp).div
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hp) (by norm_num : (1 : ℝ) - 0 ≠ 0)
    simpa [Pi.div_def] using h
  have hcount := (I.tendsto_real_ceil_le_count hη.1).mono_left hL
  filter_upwards [hh.eventually (gt_mem_nhds (lt_add_of_pos_right B hη.1)),
    hp.eventually (gt_mem_nhds one_pos), hcount.eventually (gt_mem_nhds hε2), hhi η hη.1,
    hL (eventually_ge_atTop 0)] with n h1 hp1 h2 h3 _
  set p := 1 - I.F (t n) with hp_def
  set m := ⌈(1 + η) * n / I.A⌉₊
  have hp0 : 0 ≤ p := sub_nonneg.2 (I.F_le_one _)
  have hq : 0 < 1 - p := by linarith
  have hlog : -(p / (1 - p)) ≤ Real.log (1 - p) := by
    have := Real.one_sub_inv_le_log_of_pos hq
    rwa [show 1 - (1 - p)⁻¹ = -(p / (1 - p)) by field_simp; ring] at this
  have hF : Real.exp (-(m * p / (1 - p))) ≤ I.F (t n) ^ m := by
    rw [show -(m * p / (1 - p)) = m * (-(p / (1 - p))) by ring, Real.exp_nat_mul,
      show I.F (t n) = 1 - p by rw [hp_def]; ring]
    refine pow_le_pow_left₀ (Real.exp_pos _).le ?_ m
    calc Real.exp (-(p / (1 - p))) ≤ Real.exp (Real.log (1 - p)) := Real.exp_le_exp.2 hlog
      _ = 1 - p := Real.exp_log hq
  have hm : (m : ℝ) * p ≤ B + p := by
    have hm1 : (m : ℝ) ≤ (1 + η) * n / I.A + 1 :=
      (Nat.ceil_lt_add_one (by have := hη.1; positivity)).le
    have hB : (1 + η) * n / I.A * p ≤ B := by
      rw [div_mul_eq_mul_div, mul_assoc]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left h3 (by linarith [hη.1])) hA.le
    nlinarith
  have hE : g η ≤ Real.exp (-(m * p / (1 - p))) := by
    rw [hg_def]; refine Real.exp_le_exp.2 (neg_le_neg ?_)
    calc (m : ℝ) * p / (1 - p) ≤ (B + p) / (1 - p) := div_le_div_of_nonneg_right hm hq.le
      _ ≤ B + η := h1.le
  linarith [I.le_real_le n m (t n)]

/-- Two-sided form: if `n (1 - F tₙ) → c` along `L`, then `P(Mₙ ≤ tₙ) → exp (-c / A)` along `L`. -/
theorem tendsto_real_le_of_tendsto [IsProbabilityMeasure P] (I : LadderInput P M) {L : Filter ℕ}
    (hL : L ≤ atTop) (t : ℕ → ℝ) {c : ℝ}
    (hc : Tendsto (fun n : ℕ => (n : ℝ) * (1 - I.F (t n))) L (𝓝 c)) :
    Tendsto (fun n => P.real {ω | M n ω ≤ t n}) L (𝓝 (Real.exp (-(c / I.A)))) := by
  have hlo : ∀ δ > 0, ∀ᶠ n in L, c - δ ≤ n * (1 - I.F (t n)) := fun δ hδ =>
    (hc.eventually (lt_mem_nhds (sub_lt_self c hδ))).mono fun _ h => h.le
  have hhi : ∀ δ > 0, ∀ᶠ n : ℕ in L, (n : ℝ) * (1 - I.F (t n)) ≤ c + δ := fun δ hδ =>
    (hc.eventually (gt_mem_nhds (lt_add_of_pos_right c hδ))).mono fun _ h => h.le
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [I.eventually_le_real_le hL t hhi (half_pos (sub_pos.2 ha))] with n hn
    linarith
  · filter_upwards [I.eventually_real_le_le hL t hlo hhi (half_pos (sub_pos.2 ha))] with n hn
    linarith

/-- **Gumbel limit, nonlattice case** (Iglehart 1972; Karlin–Dembo 1992, Theorem 1).

If the excursion heights have the exponential tail `P(Y > t) ~ C e^{-θ t}` given by the
renewal theorem in the nonlattice case, then for every `x`,
`P(Mₙ ≤ log n / θ + x) → exp (-K e^{-θ x})` with `K = C / A`. -/
theorem tendsto_real_le_log_div_add [IsProbabilityMeasure P] (I : LadderInput P M) {θ C : ℝ}
    (hθ : 0 < θ) (htail : Tendsto (fun t => (1 - I.F t) * Real.exp (θ * t)) atTop (𝓝 C))
    (x : ℝ) :
    Tendsto (fun n : ℕ => P.real {ω | M n ω ≤ Real.log n / θ + x}) atTop
      (𝓝 (Real.exp (-(C / I.A * Real.exp (-(θ * x)))))) := by
  have ht : Tendsto (fun n : ℕ => Real.log n / θ + x) atTop atTop :=
    tendsto_atTop_add_const_right _ x
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const hθ)
  have hc : Tendsto (fun n : ℕ => (n : ℝ) * (1 - I.F (Real.log n / θ + x))) atTop
      (𝓝 (C * Real.exp (-(θ * x)))) := by
    refine ((htail.comp ht).mul_const (Real.exp (-(θ * x)))).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Function.comp_apply]
    rw [mul_assoc, ← Real.exp_add,
      show θ * (Real.log n / θ + x) + -(θ * x) = Real.log n by field_simp; ring,
      Real.exp_log hn', mul_comm]
  convert I.tendsto_real_le_of_tendsto le_rfl _ hc using 3
  ring

/-! ### Lattice case -/

/-- If the excursion heights lie on the lattice `hℤ`, their distribution function is constant on
each cell `[k h, (k + 1) h)`. -/
theorem F_eq_F_floor_mul [IsProbabilityMeasure P] (I : LadderInput P M) {h : ℝ} (hh : 0 < h)
    (hlat : ∀ i, ∀ᵐ ω ∂P, ∃ k : ℤ, I.Y i ω = k * h) (t : ℝ) :
    I.F t = I.F (⌊t / h⌋ * h) := by
  rw [← I.real_Y_le 0 t, ← I.real_Y_le 0 (⌊t / h⌋ * h), measureReal_def, measureReal_def]
  congr 1
  refine measure_congr ?_
  filter_upwards [hlat 0] with ω ⟨k, hk⟩
  change (I.Y 0 ω ≤ t) = (I.Y 0 ω ≤ ⌊t / h⌋ * h)
  rw [hk]
  refine propext ⟨fun hkt => ?_, fun hkt => hkt.trans ?_⟩
  · have h1 : (k : ℝ) ≤ t / h := (le_div_iff₀ hh).2 hkt
    have h2 : k ≤ ⌊t / h⌋ := Int.le_floor.2 h1
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast h2) hh.le
  · calc (⌊t / h⌋ : ℝ) * h ≤ t / h * h := mul_le_mul_of_nonneg_right (Int.floor_le _) hh.le
      _ = t := div_mul_cancel₀ t hh.ne'

private theorem lattice_mul_eq [IsProbabilityMeasure P] (I : LadderInput P M) {θ h : ℝ}
    (hθ : 0 < θ) (hh : 0 < h) (hlat : ∀ i, ∀ᵐ ω ∂P, ∃ k : ℤ, I.Y i ω = k * h) (x : ℝ) {n : ℕ}
    (hn : 1 ≤ n) (hk : 0 ≤ ⌊(Real.log n / θ + x) / h⌋) :
    (n : ℝ) * (1 - I.F (Real.log n / θ + x)) =
      (1 - I.F ((⌊(Real.log n / θ + x) / h⌋.toNat : ℕ) * h)) *
          Real.exp (θ * (((⌊(Real.log n / θ + x) / h⌋.toNat : ℕ) + 1) * h)) *
          Real.exp (-(θ * x)) *
        Real.exp (-(θ * h * (1 - Int.fract ((Real.log n / θ + x) / h)))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set u := (Real.log n / θ + x) / h with hu
  have hkn : ((⌊u⌋.toNat : ℕ) : ℝ) = (⌊u⌋ : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk
  rw [hkn, I.F_eq_F_floor_mul hh hlat (Real.log n / θ + x), ← hu, mul_assoc, mul_assoc,
    ← Real.exp_add, ← Real.exp_add, ← Int.self_sub_floor,
    show θ * ((⌊u⌋ + 1) * h) + (-(θ * x) + -(θ * h * (1 - (u - ⌊u⌋)))) = Real.log n by
      rw [hu]; field_simp; ring,
    Real.exp_log hn', mul_comm]

private theorem lattice_bounds_along [IsProbabilityMeasure P] (I : LadderInput P M)
    {θ h C : ℝ} (hθ : 0 < θ) (hh : 0 < h) (hlat : ∀ i, ∀ᵐ ω ∂P, ∃ k : ℤ, I.Y i ω = k * h)
    (htail : Tendsto (fun k : ℕ => (1 - I.F (k * h)) * Real.exp (θ * ((k + 1) * h))) atTop
      (𝓝 C)) (x : ℝ) {L : Filter ℕ} (hL : L ≤ atTop) {lo hi : ℝ}
    (hf : ∀ᶠ n : ℕ in L, lo ≤ Real.exp (-(θ * h * (1 - Int.fract ((Real.log n / θ + x) / h)))) ∧
      Real.exp (-(θ * h * (1 - Int.fract ((Real.log n / θ + x) / h)))) ≤ hi)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in L, Real.exp (-(C * Real.exp (-(θ * x)) * hi / I.A)) - ε ≤
        P.real {ω | M n ω ≤ Real.log n / θ + x} ∧
      P.real {ω | M n ω ≤ Real.log n / θ + x} ≤
        Real.exp (-(C * Real.exp (-(θ * x)) * lo / I.A)) + ε := by
  set u : ℕ → ℝ := fun n => (Real.log n / θ + x) / h with hu_def
  have hu : Tendsto u atTop atTop :=
    (tendsto_atTop_add_const_right _ x ((Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).atTop_div_const hθ)).atTop_div_const hh
  have hk : Tendsto (fun n => (⌊u n⌋.toNat : ℕ)) atTop atTop := by
    refine tendsto_atTop.2 fun b => (hu.eventually_ge_atTop (b : ℝ)).mono fun n hn => ?_
    have h1 : (b : ℤ) ≤ ⌊u n⌋ := Int.le_floor.2 (by exact_mod_cast hn)
    have h2 := Int.self_le_toNat ⌊u n⌋
    omega
  set a : ℕ → ℝ := fun n => (1 - I.F ((⌊u n⌋.toNat : ℕ) * h)) *
    Real.exp (θ * (((⌊u n⌋.toNat : ℕ) + 1) * h)) * Real.exp (-(θ * x)) with ha_def
  have ha : Tendsto a L (𝓝 (C * Real.exp (-(θ * x)))) :=
    (((htail.comp hk).mul_const _)).mono_left hL
  have ha0 : ∀ n, 0 ≤ a n := fun n =>
    mul_nonneg (mul_nonneg (sub_nonneg.2 (I.F_le_one _)) (Real.exp_pos _).le) (Real.exp_pos _).le
  have hev : ∀ᶠ n : ℕ in L, (n : ℝ) * (1 - I.F (Real.log n / θ + x)) =
      a n * Real.exp (-(θ * h * (1 - Int.fract (u n)))) := by
    filter_upwards [hL (eventually_ge_atTop 1),
      hL (hu.eventually_ge_atTop 0)] with n hn hun
    exact I.lattice_mul_eq hθ hh hlat x hn (Int.floor_nonneg.2 hun)
  set c := C * Real.exp (-(θ * x))
  have hhi : ∀ δ > 0, ∀ᶠ n : ℕ in L,
      (n : ℝ) * (1 - I.F (Real.log n / θ + x)) ≤ c * hi + δ := fun δ hδ => by
    filter_upwards [hev, hf, (ha.mul_const hi).eventually (gt_mem_nhds
      (lt_add_of_pos_right (c * hi) hδ))] with n h1 h2 h3
    rw [h1]
    exact (mul_le_mul_of_nonneg_left h2.2 (ha0 n)).trans h3.le
  have hlo : ∀ δ > 0, ∀ᶠ n : ℕ in L,
      c * lo - δ ≤ (n : ℝ) * (1 - I.F (Real.log n / θ + x)) := fun δ hδ => by
    filter_upwards [hev, hf, (ha.mul_const lo).eventually (lt_mem_nhds
      (sub_lt_self (c * lo) hδ))] with n h1 h2 h3
    rw [h1]
    exact h3.le.trans (mul_le_mul_of_nonneg_left h2.1 (ha0 n))
  exact (I.eventually_le_real_le hL (fun n : ℕ => Real.log n / θ + x) hhi hε).and
    (I.eventually_real_le_le hL (fun n : ℕ => Real.log n / θ + x) hlo hhi hε)

/-- **Lattice case: liminf/limsup bounds** (Karlin–Dembo 1992, Theorem 1, lattice case).

If the excursion heights lie on the lattice `hℤ` and the lattice renewal theorem gives
`P(Y > k h) = P(Y ≥ (k + 1) h) ~ C e^{-θ (k + 1) h}`, then with `K = C / A`, for every `ε > 0`,
eventually
`exp (-K e^{-θ x}) - ε ≤ P(Mₙ ≤ log n / θ + x) ≤ exp (-K e^{-θ (x + h)}) + ε`,
that is, `liminf ≥ exp (-K e^{-θ x})` and `limsup ≤ exp (-K e^{-θ (x + h)})`. -/
theorem eventually_lattice_bounds [IsProbabilityMeasure P] (I : LadderInput P M)
    {θ h C : ℝ} (hθ : 0 < θ) (hh : 0 < h) (hlat : ∀ i, ∀ᵐ ω ∂P, ∃ k : ℤ, I.Y i ω = k * h)
    (htail : Tendsto (fun k : ℕ => (1 - I.F (k * h)) * Real.exp (θ * ((k + 1) * h))) atTop
      (𝓝 C)) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-(C / I.A * Real.exp (-(θ * x)))) - ε ≤
        P.real {ω | M n ω ≤ Real.log n / θ + x} ∧
      P.real {ω | M n ω ≤ Real.log n / θ + x} ≤
        Real.exp (-(C / I.A * Real.exp (-(θ * (x + h))))) + ε := by
  have hf : ∀ᶠ n : ℕ in atTop, Real.exp (-(θ * h)) ≤
        Real.exp (-(θ * h * (1 - Int.fract ((Real.log n / θ + x) / h)))) ∧
      Real.exp (-(θ * h * (1 - Int.fract ((Real.log n / θ + x) / h)))) ≤ 1 :=
    Eventually.of_forall fun n => by
      have h0 := Int.fract_nonneg ((Real.log n / θ + x) / h)
      have h1 := Int.fract_lt_one ((Real.log n / θ + x) / h)
      have hθh : 0 < θ * h := mul_pos hθ hh
      refine ⟨Real.exp_le_exp.2 ?_, Real.exp_le_one_iff.2 ?_⟩ <;> nlinarith
  have e1 : C * Real.exp (-(θ * x)) * 1 / I.A = C / I.A * Real.exp (-(θ * x)) := by ring
  have e2 : C * Real.exp (-(θ * x)) * Real.exp (-(θ * h)) / I.A =
      C / I.A * Real.exp (-(θ * (x + h))) := by
    rw [mul_assoc, ← Real.exp_add]; ring_nf
  simpa only [e1, e2] using I.lattice_bounds_along hθ hh hlat htail x le_rfl hf hε

private theorem frequently_fract_lt_and_gt {u : ℕ → ℝ} (hu : Tendsto u atTop atTop)
    (hdu : Tendsto (fun n => u (n + 1) - u n) atTop (𝓝 0)) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∃ᶠ n in atTop, Int.fract (u n) < δ) ∧ (∃ᶠ n in atTop, 1 - δ < Int.fract (u n)) := by
  classical
  have key : ∀ N : ℕ, ∃ j ≥ N, Int.fract (u (j + 1)) < δ ∧ 1 - δ < Int.fract (u j) := by
    intro N
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
      ((hdu.eventually (gt_mem_nhds hδ)).and (eventually_ge_atTop N))
    set k : ℤ := ⌊u N₁⌋ + 1 with hk_def
    have hk : u N₁ < k := by rw [hk_def]; push_cast; exact Int.lt_floor_add_one _
    have hex : ∃ n, N₁ ≤ n ∧ (k : ℝ) ≤ u n :=
      ((hu.eventually_ge_atTop (k : ℝ)).and (eventually_ge_atTop N₁)).exists.imp
        fun n h => ⟨h.2, h.1⟩
    have hn₀ := Nat.find_spec hex
    have hne : Nat.find hex ≠ N₁ := fun h => by
      have := hn₀.2; rw [h] at this; linarith
    obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 :=
      Nat.exists_eq_succ_of_ne_zero (by have := hn₀.1; omega)
    have hjN : N₁ ≤ j := by have := hn₀.1; omega
    have hjk : u j < k := by
      have := Nat.find_min hex (show j < Nat.find hex by omega)
      exact lt_of_not_ge fun h => this ⟨hjN, h⟩
    obtain ⟨hstep, hN⟩ := hN₁ j hjN
    have h1 : (k : ℝ) ≤ u (j + 1) := hj ▸ hn₀.2
    refine ⟨j, hN, ?_, ?_⟩
    · have : ⌊u (j + 1)⌋ = k := Int.floor_eq_iff.2 ⟨h1, by linarith⟩
      rw [← Int.self_sub_floor, this]; linarith
    · have : ⌊u j⌋ = k - 1 := Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
      rw [← Int.self_sub_floor, this]; push_cast; linarith
  refine ⟨frequently_atTop.2 fun N => ?_, frequently_atTop.2 fun N => ?_⟩
  · obtain ⟨j, hj, h, -⟩ := key N; exact ⟨j + 1, by omega, h⟩
  · obtain ⟨j, hj, -, h⟩ := key N; exact ⟨j, hj, h⟩

private theorem frequently_fract_log {θ h : ℝ} (hθ : 0 < θ) (hh : 0 < h) (x : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∃ᶠ n : ℕ in atTop, Int.fract ((Real.log n / θ + x) / h) < δ) ∧
      (∃ᶠ n : ℕ in atTop, 1 - δ < Int.fract ((Real.log n / θ + x) / h)) := by
  refine frequently_fract_lt_and_gt (u := fun n : ℕ => (Real.log n / θ + x) / h) ?_ ?_ hδ hδ1
  · exact (tendsto_atTop_add_const_right _ x ((Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).atTop_div_const hθ)).atTop_div_const hh
  · have := (Real.tendsto_log_nat_add_one_sub_log.div_const θ).div_const h
    rw [zero_div, zero_div] at this
    refine this.congr fun n => ?_
    push_cast; field_simp; ring

/-- **Lattice case: the liminf is approached.** For every `ε > 0`, infinitely often
`P(Mₙ ≤ log n / θ + x) ≤ exp (-K e^{-θ x}) + ε` (`K = C / A`). -/
theorem frequently_lattice_le [IsProbabilityMeasure P] (I : LadderInput P M)
    {θ h C : ℝ} (hθ : 0 < θ) (hh : 0 < h) (hlat : ∀ i, ∀ᵐ ω ∂P, ∃ k : ℤ, I.Y i ω = k * h)
    (htail : Tendsto (fun k : ℕ => (1 - I.F (k * h)) * Real.exp (θ * ((k + 1) * h))) atTop
      (𝓝 C)) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ n : ℕ in atTop, P.real {ω | M n ω ≤ Real.log n / θ + x} ≤
      Real.exp (-(C / I.A * Real.exp (-(θ * x)))) + ε := by
  set c := C * Real.exp (-(θ * x))
  set g : ℝ → ℝ := fun δ => Real.exp (-(c * Real.exp (-(θ * h * δ)) / I.A)) with hg_def
  have hg : Tendsto g (𝓝[>] 0) (𝓝 (Real.exp (-(C / I.A * Real.exp (-(θ * x)))))) := by
    have hc : Continuous g := by fun_prop
    have e : g 0 = Real.exp (-(C / I.A * Real.exp (-(θ * x)))) := by simp [g, c]; ring_nf
    simpa [e] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨δ, hgδ, hδ⟩ := ((hg.eventually (gt_mem_nhds (lt_add_of_pos_right _ (half_pos hε)))).and
    (Ioc_mem_nhdsGT one_pos : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] 0)).exists
  set S := {n : ℕ | 1 - δ < Int.fract ((Real.log n / θ + x) / h)}
  have hf : ∀ᶠ n : ℕ in atTop ⊓ 𝓟 S, Real.exp (-(θ * h * δ)) ≤
        Real.exp (-(θ * h * (1 - Int.fract ((Real.log n / θ + x) / h)))) ∧
      Real.exp (-(θ * h * (1 - Int.fract ((Real.log n / θ + x) / h)))) ≤ 1 := by
    refine eventually_inf_principal.2 (Eventually.of_forall fun n (hn : 1 - δ < _) => ?_)
    have h1 := Int.fract_lt_one ((Real.log n / θ + x) / h)
    have hθh : 0 < θ * h := mul_pos hθ hh
    refine ⟨Real.exp_le_exp.2 ?_, Real.exp_le_one_iff.2 ?_⟩ <;> nlinarith
  have hev := eventually_inf_principal.1
    (I.lattice_bounds_along hθ hh hlat htail x inf_le_left hf (half_pos hε))
  refine ((frequently_fract_log hθ hh x hδ.1 hδ.2).2.and_eventually hev).mono
    fun n ⟨hS, hn⟩ => ?_
  have := (hn hS).2
  have e : C * Real.exp (-(θ * x)) * Real.exp (-(θ * h * δ)) / I.A =
      c * Real.exp (-(θ * h * δ)) / I.A := rfl
  rw [e] at this
  linarith

/-- **Lattice case: the limsup is approached.** For every `ε > 0`, infinitely often
`exp (-K e^{-θ (x + h)}) - ε ≤ P(Mₙ ≤ log n / θ + x)` (`K = C / A`). -/
theorem frequently_le_lattice [IsProbabilityMeasure P] (I : LadderInput P M)
    {θ h C : ℝ} (hθ : 0 < θ) (hh : 0 < h) (hlat : ∀ i, ∀ᵐ ω ∂P, ∃ k : ℤ, I.Y i ω = k * h)
    (htail : Tendsto (fun k : ℕ => (1 - I.F (k * h)) * Real.exp (θ * ((k + 1) * h))) atTop
      (𝓝 C)) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ n : ℕ in atTop, Real.exp (-(C / I.A * Real.exp (-(θ * (x + h))))) - ε ≤
      P.real {ω | M n ω ≤ Real.log n / θ + x} := by
  set c := C * Real.exp (-(θ * x))
  set g : ℝ → ℝ := fun δ => Real.exp (-(c * Real.exp (-(θ * h * (1 - δ))) / I.A)) with hg_def
  have hg : Tendsto g (𝓝[>] 0) (𝓝 (Real.exp (-(C / I.A * Real.exp (-(θ * (x + h))))))) := by
    have hc : Continuous g := by fun_prop
    have e : g 0 = Real.exp (-(C / I.A * Real.exp (-(θ * (x + h))))) := by
      simp only [g, c, sub_zero, mul_one]
      rw [mul_assoc, ← Real.exp_add]; ring_nf
    simpa [e] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨δ, hgδ, hδ⟩ := ((hg.eventually (lt_mem_nhds (sub_lt_self _ (half_pos hε)))).and
    (Ioc_mem_nhdsGT one_pos : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] 0)).exists
  set S := {n : ℕ | Int.fract ((Real.log n / θ + x) / h) < δ}
  have hf : ∀ᶠ n : ℕ in atTop ⊓ 𝓟 S, 0 ≤
        Real.exp (-(θ * h * (1 - Int.fract ((Real.log n / θ + x) / h)))) ∧
      Real.exp (-(θ * h * (1 - Int.fract ((Real.log n / θ + x) / h)))) ≤
        Real.exp (-(θ * h * (1 - δ))) := by
    refine eventually_inf_principal.2 (Eventually.of_forall fun n (hn : _ < δ) => ?_)
    have hθh : 0 < θ * h := mul_pos hθ hh
    exact ⟨(Real.exp_pos _).le, Real.exp_le_exp.2 (by nlinarith)⟩
  have hev := eventually_inf_principal.1
    (I.lattice_bounds_along hθ hh hlat htail x inf_le_left hf (half_pos hε))
  refine ((frequently_fract_log hθ hh x hδ.1 hδ.2).1.and_eventually hev).mono
    fun n ⟨hS, hn⟩ => ?_
  have := (hn hS).1
  have e : C * Real.exp (-(θ * x)) * Real.exp (-(θ * h * (1 - δ))) / I.A =
      c * Real.exp (-(θ * h * (1 - δ))) / I.A := rfl
  rw [e] at this
  linarith

/-- **Lattice case: no Gumbel limit.** If `C > 0`, `P(Mₙ ≤ log n / θ + x)` does not converge:
its liminf `exp (-K e^{-θ x})` and limsup `exp (-K e^{-θ (x + h)})` differ. -/
theorem not_tendsto_lattice [IsProbabilityMeasure P] (I : LadderInput P M)
    {θ h C : ℝ} (hθ : 0 < θ) (hh : 0 < h) (hC : 0 < C)
    (hlat : ∀ i, ∀ᵐ ω ∂P, ∃ k : ℤ, I.Y i ω = k * h)
    (htail : Tendsto (fun k : ℕ => (1 - I.F (k * h)) * Real.exp (θ * ((k + 1) * h))) atTop
      (𝓝 C)) (x : ℝ) (l : ℝ) :
    ¬ Tendsto (fun n : ℕ => P.real {ω | M n ω ≤ Real.log n / θ + x}) atTop (𝓝 l) := by
  intro hl
  set a := Real.exp (-(C / I.A * Real.exp (-(θ * x))))
  set b := Real.exp (-(C / I.A * Real.exp (-(θ * (x + h)))))
  have hab : a < b := by
    have hK : 0 < C / I.A := div_pos hC I.A_pos
    refine Real.exp_lt_exp.2 (neg_lt_neg (mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 ?_) hK))
    nlinarith
  have hε : 0 < (b - a) / 5 := by linarith
  have hnear := Metric.tendsto_nhds.1 hl _ hε
  obtain ⟨n, h1, h2⟩ := ((I.frequently_lattice_le hθ hh hlat htail x hε).and_eventually
    hnear).exists
  obtain ⟨m, h3, h4⟩ := ((I.frequently_le_lattice hθ hh hlat htail x hε).and_eventually
    hnear).exists
  rw [Real.dist_eq, abs_lt] at h2 h4
  linarith

end LadderInput

/-! ### Maximal segment scores of i.i.d. scores in the Cramér setting -/

section Scores

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Cramér conditions** for an i.i.d. score sequence `X 0, X 1, …` with root `θ`: the scores are
independent and identically distributed, integrable with negative mean (`E X < 0`), and
`θ > 0` solves the Cramér equation `E e^{θ X} = 1` (in particular `e^{θ X}` is integrable, since
`mgf` is `0` otherwise). -/
structure CramerScores (P : Measure Ω) (X : ℕ → Ω → ℝ) (θ : ℝ) : Prop where
  /-- Each score is measurable. -/
  measurable : ∀ i, Measurable (X i)
  /-- The scores are independent. -/
  iIndepFun : iIndepFun X P
  /-- The scores are identically distributed. -/
  identDistrib : ∀ i, IdentDistrib (X i) (X 0) P P
  /-- The scores are integrable. -/
  integrable : Integrable (X 0) P
  /-- Negative drift: `E X < 0`. -/
  integral_neg : ∫ ω, X 0 ω ∂P < 0
  /-- The Cramér root is positive. -/
  pos : 0 < θ
  /-- The Cramér equation `E e^{θ X} = 1`. -/
  mgf_eq_one : mgf (X 0) P θ = 1

/-- The maximal segment score `Mₙ(ω)` of the score sequence `X 0 ω, …, X (n - 1) ω`. -/
noncomputable abbrev maxSegmentScoreRV (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  maxSegmentScore (fun k => X k ω) n

/-- **Renewal input, nonlattice case.** Cramér conditions on nonlattice i.i.d. scores, together
with the two inputs that renewal theory supplies and that are taken here as hypotheses: the
ladder decomposition of the maximal segment score (`ladder`) and the nonlattice renewal tail
`P(Y > t) ~ C e^{-θ t}` of the excursion heights (`tendsto_tail`). The fields `cramer` and
`nonlattice` record the setting in which renewal theory provides `ladder` and `tendsto_tail`;
the limit theorem uses only the latter two.

No instance of this structure (or of `LatticeRenewalInput`) is constructed here: that would
require deriving the ladder input from the scores. Non-vacuity is shown only for `LadderInput`,
in the test file. -/
structure NonlatticeRenewalInput (P : Measure Ω) (X : ℕ → Ω → ℝ) where
  /-- The Cramér root. -/
  θ : ℝ
  /-- The Cramér conditions with root `θ`. -/
  cramer : CramerScores P X θ
  /-- The scores are nonlattice: they are not a.s. supported on any lattice `hℤ`. -/
  nonlattice : ∀ h > 0, ¬ ∀ᵐ ω ∂P, ∃ k : ℤ, X 0 ω = k * h
  /-- The ladder decomposition of the maximal segment score. -/
  ladder : LadderInput P (maxSegmentScoreRV X)
  /-- The renewal constant of the excursion-height tail. -/
  C : ℝ
  /-- Nonlattice renewal tail `P(Y > t) ~ C e^{-θ t}`. -/
  tendsto_tail : Tendsto (fun t => (1 - ladder.F t) * Real.exp (θ * t)) atTop (𝓝 C)

/-- The Gumbel constant `K = C / A`: renewal tail constant over mean ladder-epoch length. -/
noncomputable def NonlatticeRenewalInput.K {P : Measure Ω} {X : ℕ → Ω → ℝ}
    (R : NonlatticeRenewalInput P X) : ℝ :=
  R.C / R.ladder.A

/-- **Gumbel limit for the maximal segment score of nonlattice i.i.d. scores**:
`P(Mₙ ≤ log n / θ + x) → exp (-K e^{-θ x})`, `K = C / A`, given the renewal input. -/
theorem NonlatticeRenewalInput.tendsto_gumbel {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (R : NonlatticeRenewalInput P X) (x : ℝ) :
    Tendsto (fun n : ℕ => P.real {ω | maxSegmentScoreRV X n ω ≤ Real.log n / R.θ + x}) atTop
      (𝓝 (Real.exp (-(R.K * Real.exp (-(R.θ * x)))))) :=
  R.ladder.tendsto_real_le_log_div_add R.cramer.pos R.tendsto_tail x

/-- **Renewal input, lattice case** with span `h`: Cramér conditions on i.i.d. scores supported
on `hℤ`, the ladder decomposition of the maximal segment score with excursion heights on `hℤ`
(`ladder`, `lattice_Y`), and the lattice renewal tail `P(Y ≥ (k + 1) h) ~ C e^{-θ (k + 1) h}`
(`tendsto_tail`). As in `NonlatticeRenewalInput`, `cramer` and `lattice` record the setting;
the limit theorems use the remaining fields. -/
structure LatticeRenewalInput (P : Measure Ω) (X : ℕ → Ω → ℝ) where
  /-- The Cramér root. -/
  θ : ℝ
  /-- The lattice span. -/
  h : ℝ
  /-- The Cramér conditions with root `θ`. -/
  cramer : CramerScores P X θ
  /-- The span is positive. -/
  h_pos : 0 < h
  /-- The scores lie on the lattice `hℤ`. -/
  lattice : ∀ i, ∀ᵐ ω ∂P, ∃ k : ℤ, X i ω = k * h
  /-- The ladder decomposition of the maximal segment score. -/
  ladder : LadderInput P (maxSegmentScoreRV X)
  /-- The excursion heights lie on the lattice `hℤ`. -/
  lattice_Y : ∀ i, ∀ᵐ ω ∂P, ∃ k : ℤ, ladder.Y i ω = k * h
  /-- The renewal constant of the lattice excursion-height tail. -/
  C : ℝ
  /-- Lattice renewal tail `P(Y > k h) = P(Y ≥ (k + 1) h) ~ C e^{-θ (k + 1) h}`. -/
  tendsto_tail : Tendsto (fun k : ℕ => (1 - ladder.F (k * h)) * Real.exp (θ * ((k + 1) * h)))
    atTop (𝓝 C)

/-- The constant `K = C / A` of the lattice bounds. -/
noncomputable def LatticeRenewalInput.K {P : Measure Ω} {X : ℕ → Ω → ℝ}
    (R : LatticeRenewalInput P X) : ℝ :=
  R.C / R.ladder.A

/-- **Lattice scores: liminf/limsup bounds** for the maximal segment score: for every `ε > 0`,
eventually `exp (-K e^{-θ x}) - ε ≤ P(Mₙ ≤ log n / θ + x) ≤ exp (-K e^{-θ (x + h)}) + ε`. -/
theorem LatticeRenewalInput.eventually_bounds {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (R : LatticeRenewalInput P X) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-(R.K * Real.exp (-(R.θ * x)))) - ε ≤
        P.real {ω | maxSegmentScoreRV X n ω ≤ Real.log n / R.θ + x} ∧
      P.real {ω | maxSegmentScoreRV X n ω ≤ Real.log n / R.θ + x} ≤
        Real.exp (-(R.K * Real.exp (-(R.θ * (x + R.h))))) + ε :=
  R.ladder.eventually_lattice_bounds R.cramer.pos R.h_pos R.lattice_Y R.tendsto_tail x hε

/-- **Lattice scores: both bounds are approached (within any `ε`) infinitely often**, so they
are the exact liminf and limsup of `P(Mₙ ≤ log n / θ + x)`. -/
theorem LatticeRenewalInput.frequently_bounds {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (R : LatticeRenewalInput P X) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∃ᶠ n : ℕ in atTop, P.real {ω | maxSegmentScoreRV X n ω ≤ Real.log n / R.θ + x} ≤
        Real.exp (-(R.K * Real.exp (-(R.θ * x)))) + ε) ∧
      ∃ᶠ n : ℕ in atTop, Real.exp (-(R.K * Real.exp (-(R.θ * (x + R.h))))) - ε ≤
        P.real {ω | maxSegmentScoreRV X n ω ≤ Real.log n / R.θ + x} :=
  ⟨R.ladder.frequently_lattice_le R.cramer.pos R.h_pos R.lattice_Y R.tendsto_tail x hε,
    R.ladder.frequently_le_lattice R.cramer.pos R.h_pos R.lattice_Y R.tendsto_tail x hε⟩

/-- **Lattice scores: no Gumbel limit.** If `C > 0`, `P(Mₙ ≤ log n / θ + x)` converges to no
limit. -/
theorem LatticeRenewalInput.not_tendsto {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (R : LatticeRenewalInput P X) (hC : 0 < R.C) (x l : ℝ) :
    ¬ Tendsto (fun n : ℕ => P.real {ω | maxSegmentScoreRV X n ω ≤ Real.log n / R.θ + x}) atTop
      (𝓝 l) :=
  R.ladder.not_tendsto_lattice R.cramer.pos R.h_pos hC R.lattice_Y R.tendsto_tail x l

end Scores

/-! ### Example: exponential scores -/

section Example

/-- The moment generating function of the exponential distribution with rate `r`:
`E e^{s Y} = r / (r - s)` for `s < r`. -/
theorem mgf_id_expMeasure {r s : ℝ} (hr : 0 < r) (hs : s < r) :
    mgf id (expMeasure r) s = r / (r - s) := by
  have hpdf : ∀ x, (exponentialPDF r x).toReal • Real.exp (s * id x) =
      Set.indicator (Set.Ici 0) (fun x => r * Real.exp ((s - r) * x)) x := by
    intro x
    rw [exponentialPDF_eq, smul_eq_mul, id]
    split_ifs with h
    · rw [ENNReal.toReal_ofReal (by positivity), Set.indicator_of_mem (Set.mem_Ici.2 h),
        mul_assoc, ← Real.exp_add]
      ring_nf
    · rw [ENNReal.toReal_ofReal le_rfl, Set.indicator_of_notMem (by simpa using h), zero_mul]
  change ∫ x, Real.exp (s * id x) ∂(volume.withDensity (exponentialPDF r)) = _
  rw [integral_withDensity_eq_integral_toReal_smul (f := exponentialPDF r)
      (measurable_exponentialPDFReal r).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [hpdf]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul,
    integral_exp_mul_Ioi (by linarith) 0]
  have : r - s ≠ 0 := by linarith
  rw [mul_zero, Real.exp_zero, show s - r = -(r - s) by ring]
  field_simp

/-- **Cramér root of two-sided exponential scores.** If `X = E₁ - E₂` with independent
`E₁ ~ Exp(a)`, `E₂ ~ Exp(b)` and `0 < b < a` (so `E X = 1/a - 1/b < 0`), then
`θ = a - b` solves the Cramér equation `E e^{θ X} = 1`:
`E e^{θ X} = a / (a - θ) · b / (b + θ) = (a / b) (b / a) = 1`. -/
theorem mgf_sub_eq_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E₁ E₂ : Ω → ℝ}
    {a b : ℝ} (hb : 0 < b) (hba : b < a) (hm₁ : Measurable E₁) (hm₂ : Measurable E₂)
    (h₁ : P.map E₁ = expMeasure a) (h₂ : P.map E₂ = expMeasure b) (hind : IndepFun E₁ E₂ P) :
    mgf (fun ω => E₁ ω - E₂ ω) P (a - b) = 1 := by
  have hX : (fun ω => E₁ ω - E₂ ω) = E₁ + (-E₂) := by ext ω; simp [sub_eq_add_neg]
  have hind' : IndepFun E₁ (-E₂) P := hind.comp measurable_id measurable_neg
  rw [hX, IndepFun.mgf_add' hind' hm₁.aestronglyMeasurable
      hm₂.neg.aestronglyMeasurable, mgf_neg, ← mgf_id_map hm₁.aemeasurable,
    ← mgf_id_map hm₂.aemeasurable, h₁, h₂, mgf_id_expMeasure (by linarith) (by linarith),
    mgf_id_expMeasure hb (by linarith)]
  have : a - (a - b) = b := by ring
  rw [this, show b - -(a - b) = a by ring]
  have ha : a ≠ 0 := by linarith
  field_simp

/-- **Exponential excursion tails.** If the excursion heights have the tail
`P(Y > t) = p e^{-θ t}` for `t ≥ 0`, the renewal constant of `NonlatticeRenewalInput` is `C = p`
(so `K = p / A`). -/
theorem tendsto_tail_of_eq_exp {F : ℝ → ℝ} {θ p : ℝ}
    (hF : ∀ t, 0 ≤ t → 1 - F t = p * Real.exp (-(θ * t))) :
    Tendsto (fun t => (1 - F t) * Real.exp (θ * t)) atTop (𝓝 p) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [hF t ht, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

end Example

end Cslib.Bioinformatics.Alignment.ScoreSignificance
