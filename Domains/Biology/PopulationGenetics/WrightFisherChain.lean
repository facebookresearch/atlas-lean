/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteMarkovChain
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

import MathlibExt.Probability.ErgodicMarkovChain
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The Wright–Fisher chain

The neutral Wright–Fisher model of a population of `M` gene copies: the state `i : Fin (M + 1)`
is the number of copies of allele `A`, and the next generation is drawn by `M` independent
draws with replacement, so the transition law from `i` is `Binomial(M, i / M)`.

## Main results

* `wrightFisher M`: the transition matrix, a `StochasticMatrix M`.
* `wrightFisher_prob_eq_binomial`: its rows are Mathlib's binomial laws `Bin(M, i / M)`.
* `sum_matPow_mul_wrightFisher`: the allele count is a martingale,
  `∑ j, P^t(i, j) j = i`.
* `wrightFisher_prob_zero_zero`, `wrightFisher_prob_last_last`: `0` and `M` are absorbing.
* `sum_matPow_mul_heterozygosity`: heterozygosity decays geometrically,
  `∑ j, P^t(i, j) H(j) = (1 - 1/M)^t H(i)` with `H(j) = 2 (j/M) (1 - j/M)`.
* `tendsto_matPow_last`, `tendsto_matPow_zero`: the fixation probability of `A` is its initial
  frequency, `P^t(i, M) → i / M`, and `P^t(i, 0) → 1 - i / M`.

Path-level statements, for any chain `X` with `IsFiniteMarkovChain X (wrightFisher M) ℱ μ`
started from `i` copies:

* `measure_exists_absorbed`: the chain is almost surely eventually absorbed in `0` or `M`.
* `measureReal_exists_eq_last`, `measureReal_exists_eq_zero`: it ever reaches `M` with
  probability `i / M` and ever reaches `0` with probability `1 - i / M`.

## Design

The transition matrix is the repository's `StochasticMatrix` (rather than a Mathlib kernel):
the moment identities are finite sums handled by `matPow`, and `IsFiniteMarkovChain` connects
the matrix to processes. The entries are Mathlib's Bernstein basis functions `bernstein M j`
at the grid points `bernstein.z i = i / M`, and the rows agree with Mathlib's
`ProbabilityTheory.binomial` (`wrightFisher_prob_eq_binomial`). Time is measured in
generations and `M` counts gene copies (`M = 2N` for a diploid population of size `N`).

## References

* W. J. Ewens, *Mathematical Population Genetics I*, 2nd ed., Springer (2004), ch. 3.
* R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Springer (2008), ch. 1.
-/

@[expose] public section

open Finset Filter Topology MeasureTheory
open MathlibExt.Probability.FiniteMarkovChain

namespace MathlibExt.Biology.PopulationGenetics.WrightFisherChain

/-! ### Binomial moments (from Mathlib's Bernstein polynomial identities) -/

/-- The binomial weights `(M choose j) x^j (1 - x)^(M - j)` sum to `1`. -/
private lemma sum_binomial (M : ℕ) (x : ℝ) :
    ∑ j ∈ range (M + 1), (M.choose j : ℝ) * x ^ j * (1 - x) ^ (M - j) = 1 := by
  have := congrArg (Polynomial.eval x) (bernsteinPolynomial.sum ℝ M)
  simpa [Polynomial.eval_finsetSum, bernsteinPolynomial] using this

/-- The binomial mean is `M x`. -/
private lemma sum_binomial_mul (M : ℕ) (x : ℝ) :
    ∑ j ∈ range (M + 1), (M.choose j : ℝ) * x ^ j * (1 - x) ^ (M - j) * j = M * x := by
  have h := congrArg (Polynomial.eval x) (bernsteinPolynomial.sum_smul ℝ M)
  simp only [Polynomial.eval_finsetSum, bernsteinPolynomial,
    Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_one, nsmul_eq_mul] at h
  rw [← h]
  exact sum_congr rfl fun j _ => by ring

/-- The binomial variance is `M x (1 - x)`. -/
private lemma sum_binomial_mul_sq (M : ℕ) (x : ℝ) :
    ∑ j ∈ range (M + 1), (M.choose j : ℝ) * x ^ j * (1 - x) ^ (M - j) * (M * x - j) ^ 2 =
      M * x * (1 - x) := by
  have h := congrArg (Polynomial.eval x) (bernsteinPolynomial.variance ℝ M)
  simp only [Polynomial.eval_finsetSum, bernsteinPolynomial,
    Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_one, nsmul_eq_mul] at h
  rw [← h]
  exact sum_congr rfl fun j _ => by ring

/-- The neutral Wright–Fisher transition matrix on `M` gene copies (Ewens 2004, ch. 3):
`P(i, j) = (M choose j) (i/M)^j (1 - i/M)^(M - j)`, the binomial law `Bin(M, i/M)` of the
number of `A` copies among `M` draws with replacement. The model needs `M ≥ 1`; for `M = 0`
(where `i / M` is Lean's junk value `0`) the matrix is the one-state chain, which is
`Bin(0, p) = δ₀` for every `p`. -/
noncomputable def wrightFisher (M : ℕ) : StochasticMatrix M where
  prob i j := bernstein M j (bernstein.z i)
  nonneg _ _ := bernstein_nonneg
  row_sum i := bernstein.probability M (bernstein.z i)

/-- The frequency of allele `A` in state `i` is `bernstein.z i = i / M` (for `M = 0` it is
Lean's junk value `i / 0 = 0`). -/
theorem coe_z (M : ℕ) (i : Fin (M + 1)) : (bernstein.z i : ℝ) = ((i : ℕ) : ℝ) / M :=
  rfl

/-- `M (i / M) = i` (also for `M = 0`, where `i = 0`). -/
private lemma mul_z (M : ℕ) (i : Fin (M + 1)) : (M : ℝ) * (bernstein.z i : ℝ) = (i : ℕ) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  · rw [coe_z]
    field_simp

/-- Entries of the Wright–Fisher matrix. -/
theorem wrightFisher_prob (M : ℕ) (i j : Fin (M + 1)) :
    (wrightFisher M).prob i j =
      (M.choose j : ℝ) * (bernstein.z i : ℝ) ^ (j : ℕ) * (1 - (bernstein.z i : ℝ)) ^ (M - j) :=
  bernstein_apply M j (bernstein.z i)

/-- The heterozygosity `H(j) = 2 (j/M) (1 - j/M)` of state `j`: the probability that two
gene copies drawn with replacement carry different alleles. -/
noncomputable def heterozygosity (M : ℕ) (j : Fin (M + 1)) : ℝ :=
  2 * (bernstein.z j : ℝ) * (1 - (bernstein.z j : ℝ))

/-- The rows of the Wright–Fisher matrix are Mathlib's binomial laws `Bin(M, i/M)`. -/
theorem wrightFisher_prob_eq_binomial (M : ℕ) (i j : Fin (M + 1)) :
    (wrightFisher M).prob i j =
      (ProbabilityTheory.binomial M (bernstein.z i)).real {(j : ℕ)} := by
  rw [ProbabilityTheory.binomial_real_singleton, wrightFisher_prob]

/-- Martingale property of the allele count (one step): `∑ j, P(i, j) j = i`. -/
theorem sum_prob_mul_wrightFisher (M : ℕ) (i : Fin (M + 1)) :
    ∑ j, (wrightFisher M).prob i j * ((j : ℕ) : ℝ) = (i : ℕ) := by
  simp only [wrightFisher_prob]
  rw [Fin.sum_univ_eq_sum_range (fun j => (M.choose j : ℝ) * (bernstein.z i : ℝ) ^ j *
    (1 - (bernstein.z i : ℝ)) ^ (M - j) * (j : ℝ)), sum_binomial_mul, mul_z]

/-- Martingale property of the allele count (`t` steps): `∑ j, P^t(i, j) j = i`. -/
theorem sum_matPow_mul_wrightFisher (M t : ℕ) (i : Fin (M + 1)) :
    ∑ j, (wrightFisher M).matPow t i j * ((j : ℕ) : ℝ) = (i : ℕ) := by
  induction t generalizing i with
  | zero => simp [StochasticMatrix.matPow]
  | succ t ih =>
    simp only [StochasticMatrix.matPow, sum_mul]
    rw [sum_comm]
    simp only [mul_assoc, ← mul_sum, ih]
    exact sum_prob_mul_wrightFisher M i

/-- The state `0` (allele `A` lost) is absorbing. -/
theorem wrightFisher_prob_zero_zero (M : ℕ) : (wrightFisher M).prob 0 0 = 1 := by
  simp [wrightFisher_prob]

/-- The state `M` (allele `A` fixed) is absorbing. -/
theorem wrightFisher_prob_last_last (M : ℕ) :
    (wrightFisher M).prob (Fin.last M) (Fin.last M) = 1 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [wrightFisher_prob]
  · have : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    simp [wrightFisher_prob, coe_z, this]

/-- Heterozygosity decays by the factor `1 - 1/M` per generation (one step). For `M = 0` both
sides are `0` because `H ≡ 0`. -/
theorem sum_prob_mul_heterozygosity (M : ℕ) (i : Fin (M + 1)) :
    ∑ j, (wrightFisher M).prob i j * heterozygosity M j =
      (1 - 1 / (M : ℝ)) * heterozygosity M i := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [heterozygosity, coe_z]
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  set x : ℝ := (bernstein.z i : ℝ) with hx
  have key : ∀ j : Fin (M + 1), (wrightFisher M).prob i j * heterozygosity M j =
      2 * x ^ 2 * ((M.choose j : ℝ) * x ^ (j : ℕ) * (1 - x) ^ (M - j)) +
      (2 / M - 4 * x / M) * ((M.choose j : ℝ) * x ^ (j : ℕ) * (1 - x) ^ (M - j) * (j : ℕ)) +
      (-2 / M ^ 2) * ((M.choose j : ℝ) * x ^ (j : ℕ) * (1 - x) ^ (M - j) *
        (M * x - (j : ℕ)) ^ 2) := by
    intro j
    simp only [wrightFisher_prob, heterozygosity, hx, coe_z]
    field_simp
    ring
  simp only [key, sum_add_distrib, ← mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j => (M.choose j : ℝ) * x ^ j * (1 - x) ^ (M - j)),
    Fin.sum_univ_eq_sum_range (fun j => (M.choose j : ℝ) * x ^ j * (1 - x) ^ (M - j) * j),
    Fin.sum_univ_eq_sum_range (fun j => (M.choose j : ℝ) * x ^ j * (1 - x) ^ (M - j) *
      (M * x - j) ^ 2), sum_binomial, sum_binomial_mul, sum_binomial_mul_sq, heterozygosity,
    ← hx, hx, coe_z]
  field_simp
  ring

/-- A right eigenvector of `P` is a right eigenvector of every power. -/
private lemma eigen_power {M : ℕ} (P : StochasticMatrix M)
    (f : Fin (M + 1) → ℝ) (a : ℝ)
    (h : ∀ i, ∑ j, P.prob i j * f j = a * f i) (t : ℕ)
    (i : Fin (M + 1)) : ∑ j, P.matPow t i j * f j = a ^ t * f i := by
  classical
  induction t generalizing i with
  | zero => simp [StochasticMatrix.matPow]
  | succ t ih =>
    simp only [StochasticMatrix.matPow, sum_mul, mul_assoc]
    rw [sum_comm]
    simp_rw [← mul_sum, ih]
    calc
      ∑ k, P.prob i k * (a ^ t * f k) = a ^ t * ∑ k, P.prob i k * f k := by
        rw [mul_sum]
        apply sum_congr rfl
        intro k _
        ring
      _ = a ^ (t + 1) * f i := by rw [h, pow_succ]; ring

/-- Heterozygosity decays geometrically (Ewens 2004, ch. 3):
`∑ j, P^t(i, j) H(j) = (1 - 1/M)^t H(i)`. For `M = 0` both sides are `0` because `H ≡ 0`
(the factor `1 - 1/0 = 1` is then irrelevant). -/
theorem sum_matPow_mul_heterozygosity (M t : ℕ) (i : Fin (M + 1)) :
    ∑ j, (wrightFisher M).matPow t i j * heterozygosity M j =
      (1 - 1 / (M : ℝ)) ^ t * heterozygosity M i := by
  exact eigen_power (wrightFisher M) (heterozygosity M) (1 - 1 / (M : ℝ))
    (sum_prob_mul_heterozygosity M) t i

/-- The probability of sitting in an interior state `0 < j < M` at time `t` tends to `0`. -/
theorem tendsto_matPow_interior {M : ℕ} (i j : Fin (M + 1)) (hj0 : j ≠ 0)
    (hjM : j ≠ Fin.last M) :
    Tendsto (fun t => (wrightFisher M).matPow t i j) atTop (𝓝 0) := by
  have hjpos : 0 < (j : ℕ) := by
    by_contra h
    apply hj0
    apply Fin.ext
    simp only [Fin.val_zero]
    omega
  have hjlt : (j : ℕ) < M := by
    by_contra h
    apply hjM
    apply Fin.ext
    simp only [Fin.val_last]
    omega
  have hM : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hMone : 1 ≤ (M : ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
  have hH : 0 < heterozygosity M j := by
    have hfreq : 0 < (bernstein.z j : ℝ) :=
      div_pos (Nat.cast_pos.mpr hjpos) hM
    have hfreq1 : (bernstein.z j : ℝ) < 1 :=
      (div_lt_one hM).mpr (Nat.cast_lt.mpr hjlt)
    exact mul_pos (mul_pos (by norm_num) hfreq) (sub_pos.mpr hfreq1)
  have hHnonneg : ∀ k, 0 ≤ heterozygosity M k := by
    intro k
    exact mul_nonneg (mul_nonneg (by norm_num) (bernstein.z k).2.1)
      (sub_nonneg.mpr (bernstein.z k).2.2)
  have hbound (t : ℕ) : (wrightFisher M).matPow t i j ≤
      (1 - 1 / (M : ℝ)) ^ t * heterozygosity M i / heterozygosity M j := by
    apply (le_div_iff₀ hH).mpr
    calc
      (wrightFisher M).matPow t i j * heterozygosity M j ≤
          ∑ k, (wrightFisher M).matPow t i k * heterozygosity M k :=
        single_le_sum (fun k _ => mul_nonneg (StochasticMatrix.matPow_nonneg _ t i k) (hHnonneg k))
          (mem_univ j)
      _ = _ := sum_matPow_mul_heterozygosity M t i
  have hc0 : 0 ≤ 1 - 1 / (M : ℝ) := by
    exact sub_nonneg.mpr ((div_le_one hM).mpr hMone)
  have hc1 : 1 - 1 / (M : ℝ) < 1 := by
    have : 0 < 1 / (M : ℝ) := by positivity
    linarith
  have hz := ((tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const
    (heterozygosity M i)).div_const (heterozygosity M j)
  exact squeeze_zero (fun t => StochasticMatrix.matPow_nonneg _ t i j) hbound (by simpa using hz)

/-- Split a sum over the states into the two absorbing states and the interior. -/
private lemma sum_split_endpoints {M : ℕ} (hM : 0 < M)
    (f : Fin (M + 1) → ℝ) :
    ∑ j, f j = f 0 + f (Fin.last M) + ∑ j ∈ (univ.erase 0).erase (Fin.last M), f j := by
  classical
  have hlast : (Fin.last M : Fin (M + 1)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_zero] at this
    omega
  have ha := sum_erase_add univ f (mem_univ (0 : Fin (M + 1)))
  have hb := sum_erase_add (univ.erase 0) f (mem_erase.mpr ⟨hlast, mem_univ _⟩)
  linarith

/-- Any weighted sum over the interior states tends to `0`. -/
private lemma tendsto_interior_sum {M : ℕ} (i : Fin (M + 1))
    (f : Fin (M + 1) → ℝ) :
    Tendsto (fun t => ∑ j ∈ (univ.erase 0).erase (Fin.last M),
      (wrightFisher M).matPow t i j * f j) atTop (𝓝 0) := by
  classical
  have h : Tendsto (fun t => ∑ j ∈ (univ.erase 0).erase (Fin.last M),
      (wrightFisher M).matPow t i j * f j) atTop
      (𝓝 (∑ j ∈ (univ.erase 0).erase (Fin.last M), (0 : ℝ))) := by
    apply tendsto_finsetSum
    intro j hj
    have hjM := (mem_erase.mp hj).1
    have hj0 := (mem_erase.mp (mem_erase.mp hj).2).1
    simpa using (tendsto_matPow_interior i j hj0 hjM).mul_const (f j)
  simpa using h

/-- Fixation probability (Ewens 2004, ch. 3): started from `i` copies, allele `A` is fixed with
limiting probability `i / M`, i.e. `P^t(i, M) → i / M`. -/
theorem tendsto_matPow_last {M : ℕ} (hM : 0 < M) (i : Fin (M + 1)) :
    Tendsto (fun t => (wrightFisher M).matPow t i (Fin.last M)) atTop
      (𝓝 (((i : ℕ) : ℝ) / M)) := by
  classical
  have hMne : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  have heq (t : ℕ) : (wrightFisher M).matPow t i (Fin.last M) =
      (((i : ℕ) : ℝ) - ∑ j ∈ (univ.erase 0).erase (Fin.last M),
        (wrightFisher M).matPow t i j * ((j : ℕ) : ℝ)) / M := by
    have h := sum_split_endpoints hM
      (fun j => (wrightFisher M).matPow t i j * ((j : ℕ) : ℝ))
    rw [sum_matPow_mul_wrightFisher] at h
    simp only [Fin.val_zero, Nat.cast_zero, mul_zero, zero_add, Fin.val_last] at h
    apply (eq_div_iff hMne).mpr
    linarith
  have hi : Tendsto (fun _ : ℕ => ((i : ℕ) : ℝ)) atTop (𝓝 ((i : ℕ) : ℝ)) :=
    tendsto_const_nhds
  have h := (hi.sub
    (tendsto_interior_sum i (fun j => ((j : ℕ) : ℝ)))).div_const (M : ℝ)
  simp only [sub_zero] at h
  exact h.congr' (Eventually.of_forall fun t => (heq t).symm)

/-- Loss probability: started from `i` copies, allele `A` is lost with limiting probability
`1 - i / M`, i.e. `P^t(i, 0) → 1 - i / M`. -/
theorem tendsto_matPow_zero {M : ℕ} (hM : 0 < M) (i : Fin (M + 1)) :
    Tendsto (fun t => (wrightFisher M).matPow t i 0) atTop
      (𝓝 (1 - ((i : ℕ) : ℝ) / M)) := by
  classical
  have heq (t : ℕ) : (wrightFisher M).matPow t i 0 =
      1 - (wrightFisher M).matPow t i (Fin.last M) -
        ∑ j ∈ (univ.erase 0).erase (Fin.last M), (wrightFisher M).matPow t i j := by
    have h := sum_split_endpoints hM ((wrightFisher M).matPow t i)
    rw [StochasticMatrix.matPow_row_sum] at h
    linarith
  have hs : Tendsto (fun t => ∑ j ∈ (univ.erase 0).erase (Fin.last M),
      (wrightFisher M).matPow t i j) atTop (𝓝 0) := by
    simpa using tendsto_interior_sum i (fun _ => 1)
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := (h1.sub (tendsto_matPow_last hM i)).sub hs
  simp only [sub_zero] at h
  exact h.congr' (Eventually.of_forall fun t => (heq t).symm)

/-- For a finite Markov chain started at `i`, the law of `X t` is row `i` of `P ^ t`. -/
private lemma map_singleton_eq_matPow {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M : ℕ} {P : StochasticMatrix M} {X : ℕ → Ω → Fin (M + 1)}
    {ℱ : MeasureTheory.Filtration ℕ m} (hX : IsFiniteMarkovChain X P ℱ μ) {i : Fin (M + 1)}
    (h0 : ∀ᵐ ω ∂μ, X 0 ω = i) (t : ℕ) (j : Fin (M + 1)) :
    μ.map (X t) {j} = ENNReal.ofReal (P.matPow t i j) := by
  have hmeas : ∀ n, Measurable (X n) := fun n => (hX.adapted n).mono (ℱ.le n) le_rfl
  induction t generalizing j with
  | zero =>
    rw [Measure.map_apply (hmeas 0) (measurableSet_singleton j)]
    by_cases hij : i = j
    · subst hij
      simp only [StochasticMatrix.matPow, ite_true, ENNReal.ofReal_one]
      rw [← prob_compl_eq_zero_iff (hmeas 0 (measurableSet_singleton _))]
      exact ae_iff.1 h0
    · simp only [StochasticMatrix.matPow, hij, ite_false, ENNReal.ofReal_zero]
      refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 h0)
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
      simp only [Set.mem_ofPred_eq, hω]
      exact Ne.symm hij
  | succ t ih =>
    rw [hX.map_succ_eq_bind t, Measure.bind_apply (measurableSet_singleton j)
      (finiteChainKernel P).measurable.aemeasurable, lintegral_fintype]
    have hk : ∀ k, finiteChainKernel P k {j} = ENNReal.ofReal (P.prob k j) := fun k => by
      have h := finiteChainKernel_apply P k {j}
      rwa [Finset.coe_singleton, Finset.sum_singleton] at h
    simp_rw [hk, ih, ← ENNReal.ofReal_mul (P.nonneg _ _)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (P.nonneg _ _)
      (StochasticMatrix.matPow_nonneg P _ _ _)), StochasticMatrix.matPow_add]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [StochasticMatrix.matPow_one, mul_comm]

private lemma measureReal_eq_matPow {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M : ℕ} {P : StochasticMatrix M} {X : ℕ → Ω → Fin (M + 1)}
    {ℱ : MeasureTheory.Filtration ℕ m} (hX : IsFiniteMarkovChain X P ℱ μ) {i : Fin (M + 1)}
    (h0 : ∀ᵐ ω ∂μ, X 0 ω = i) (t : ℕ) (j : Fin (M + 1)) :
    μ.real {ω | X t ω = j} = P.matPow t i j := by
  have hmeas : Measurable (X t) := (hX.adapted t).mono (ℱ.le t) le_rfl
  rw [measureReal_def, show {ω | X t ω = j} = X t ⁻¹' {j} from rfl,
    ← Measure.map_apply hmeas (measurableSet_singleton j), map_singleton_eq_matPow hX h0,
    ENNReal.toReal_ofReal (StochasticMatrix.matPow_nonneg P _ _ _)]

/-- Path-level fixation probability: if `X` is a Wright–Fisher chain (in the sense of
`IsFiniteMarkovChain`) started from `i` copies, then `P(X_t = M) → i / M`. -/
theorem tendsto_measureReal_eq_last {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M : ℕ} (hM : 0 < M) {X : ℕ → Ω → Fin (M + 1)}
    {ℱ : MeasureTheory.Filtration ℕ m} (hX : IsFiniteMarkovChain X (wrightFisher M) ℱ μ)
    {i : Fin (M + 1)} (h0 : ∀ᵐ ω ∂μ, X 0 ω = i) :
    Tendsto (fun t => μ.real {ω | X t ω = Fin.last M}) atTop (𝓝 (((i : ℕ) : ℝ) / M)) := by
  simp_rw [measureReal_eq_matPow hX h0]
  exact tendsto_matPow_last hM i

/-- Almost-sure absorption: a Wright–Fisher chain is almost surely eventually absorbed in `0`
or `M` (Ewens 2004, ch. 3). -/
theorem measure_exists_absorbed {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M : ℕ} {X : ℕ → Ω → Fin (M + 1)}
    {ℱ : MeasureTheory.Filtration ℕ m} (hX : IsFiniteMarkovChain X (wrightFisher M) ℱ μ)
    {i : Fin (M + 1)} (h0 : ∀ᵐ ω ∂μ, X 0 ω = i) :
    μ {ω | ∃ t, X t ω = 0 ∨ X t ω = Fin.last M} = 1 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · have : {ω | ∃ t, X t ω = 0 ∨ X t ω = Fin.last 0} = Set.univ :=
      Set.eq_univ_of_forall fun ω => ⟨0, Or.inl (Fin.ext (by have := (X 0 ω).isLt; simp))⟩
    rw [this, measure_univ]
  have hmeas : ∀ t, Measurable (X t) := fun t => (hX.adapted t).mono (ℱ.le t) le_rfl
  set S := {ω | ∃ t, X t ω = 0 ∨ X t ω = Fin.last M}
  have hne : (0 : Fin (M + 1)) ≠ Fin.last M := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at this
    omega
  have hlow : ∀ t, (wrightFisher M).matPow t i 0 + (wrightFisher M).matPow t i (Fin.last M) ≤
      μ.real S := fun t => by
    have hd : Disjoint {ω | X t ω = 0} {ω | X t ω = Fin.last M} :=
      Set.disjoint_left.2 fun ω h1 h2 => hne (h1.symm.trans h2)
    rw [← measureReal_eq_matPow hX h0, ← measureReal_eq_matPow hX h0,
      ← measureReal_union hd (hmeas t (measurableSet_singleton _))]
    exact measureReal_mono fun ω hω => ⟨t, hω⟩
  have hlim := (tendsto_matPow_zero hM i).add (tendsto_matPow_last hM i)
  rw [sub_add_cancel] at hlim
  have h1 : μ.real S = 1 :=
    le_antisymm measureReal_le_one (le_of_tendsto' hlim hlow)
  rw [← ofReal_measureReal, h1, ENNReal.ofReal_one]

private lemma ae_stay {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M : ℕ} {X : ℕ → Ω → Fin (M + 1)}
    {ℱ : MeasureTheory.Filtration ℕ m} (hX : IsFiniteMarkovChain X (wrightFisher M) ℱ μ)
    {a : Fin (M + 1)} (ha : (wrightFisher M).prob a a = 1) (t : ℕ) :
    ∀ᵐ ω ∂μ, X t ω = a → X (t + 1) ω = a := by
  have hmeas : ∀ n, Measurable (X n) := fun n => (hX.adapted n).mono (ℱ.le n) le_rfl
  set A := {ω | X t ω = a}
  set B := {ω | X (t + 1) ω = a}
  have hA : MeasurableSet[ℱ t] A := hX.adapted t (measurableSet_singleton _)
  have hA' : MeasurableSet A := ℱ.le t _ hA
  have hB : MeasurableSet B := hmeas (t + 1) (measurableSet_singleton _)
  have hf : (fun ω => if X (t + 1) ω = a then (1 : ℝ) else 0) = B.indicator 1 := by
    funext ω; by_cases h : X (t + 1) ω = a <;> simp [B, h]
  have hint : Integrable (B.indicator (1 : Ω → ℝ)) μ := (integrable_const 1).indicator hB
  have h1 := setIntegral_condExp (ℱ.le t) hint hA
  rw [← hf] at h1
  rw [setIntegral_congr_ae hA' ((hX.markov_prop t a).mono fun ω h _ => h)] at h1
  rw [setIntegral_congr_fun hA' (fun ω (hω : X t ω = a) => by
    rw [hω, ha])] at h1
  rw [hf, integral_indicator_one hB] at h1
  rw [integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ,
    measureReal_restrict_apply hB, Set.inter_comm] at h1
  have h2 := measureReal_inter_add_sdiff (μ := μ) (s := A) hB
  have h3 : μ.real (A \ B) = 0 := by linarith
  rw [ae_iff]
  refine (measureReal_eq_zero_iff (by finiteness)).1 ?_
  convert h3 using 2
  ext ω
  simp [A, B]

private lemma measureReal_exists_eq_of_tendsto {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M : ℕ} {X : ℕ → Ω → Fin (M + 1)}
    {ℱ : MeasureTheory.Filtration ℕ m} (hX : IsFiniteMarkovChain X (wrightFisher M) ℱ μ)
    {a : Fin (M + 1)} (ha : (wrightFisher M).prob a a = 1) {c : ℝ}
    (hc : Tendsto (fun t => μ.real {ω | X t ω = a}) atTop (𝓝 c)) :
    μ.real {ω | ∃ t, X t ω = a} = c := by
  set E : ℕ → Set Ω := fun t => {ω | X t ω = a}
  have hstay : ∀ᵐ ω ∂μ, ∀ t, X t ω = a → X (t + 1) ω = a :=
    ae_all_iff.2 (ae_stay hX ha)
  have hF : ∀ t, Set.accumulate E t =ᵐ[μ] E t := fun t => by
    filter_upwards [hstay] with ω h
    refine propext ⟨fun hω => ?_, fun hω => Set.mem_accumulate.2 ⟨t, le_rfl, hω⟩⟩
    obtain ⟨s, hst, hs⟩ := Set.mem_accumulate.1 hω
    induction t, hst using Nat.le_induction with
    | base => exact hs
    | succ t _ ih => exact h t (ih (Set.mem_accumulate.2 ⟨s, by omega, hs⟩))
  have hlim := tendsto_measure_iUnion_atTop (μ := μ) (Set.monotone_accumulate (s := E))
  rw [Set.iUnion_accumulate] at hlim
  have hlim' : Tendsto (fun t => μ.real (E t)) atTop (𝓝 (μ.real (⋃ t, E t))) := by
    have := (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp hlim
    refine this.congr fun t => ?_
    simp only [Function.comp_apply, measureReal_def, measure_congr (hF t)]
  have hset : {ω | ∃ t, X t ω = a} = ⋃ t, E t := by
    ext ω; simp [E]
  rw [hset]
  exact tendsto_nhds_unique hlim' hc

/-- Path-level fixation probability (Ewens 2004, ch. 3): a Wright–Fisher chain started from `i`
copies ever reaches `M` (fixation of `A`) with probability `i / M`. -/
theorem measureReal_exists_eq_last {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M : ℕ} (hM : 0 < M) {X : ℕ → Ω → Fin (M + 1)}
    {ℱ : MeasureTheory.Filtration ℕ m} (hX : IsFiniteMarkovChain X (wrightFisher M) ℱ μ)
    {i : Fin (M + 1)} (h0 : ∀ᵐ ω ∂μ, X 0 ω = i) :
    μ.real {ω | ∃ t, X t ω = Fin.last M} = ((i : ℕ) : ℝ) / M :=
  measureReal_exists_eq_of_tendsto hX (wrightFisher_prob_last_last M)
    (tendsto_measureReal_eq_last hM hX h0)

/-- Path-level loss probability: a Wright–Fisher chain started from `i` copies ever reaches `0`
(loss of `A`) with probability `1 - i / M`. -/
theorem measureReal_exists_eq_zero {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M : ℕ} (hM : 0 < M) {X : ℕ → Ω → Fin (M + 1)}
    {ℱ : MeasureTheory.Filtration ℕ m} (hX : IsFiniteMarkovChain X (wrightFisher M) ℱ μ)
    {i : Fin (M + 1)} (h0 : ∀ᵐ ω ∂μ, X 0 ω = i) :
    μ.real {ω | ∃ t, X t ω = 0} = 1 - ((i : ℕ) : ℝ) / M := by
  refine measureReal_exists_eq_of_tendsto hX (wrightFisher_prob_zero_zero M) ?_
  simp_rw [measureReal_eq_matPow hX h0]
  exact tendsto_matPow_zero hM i

end MathlibExt.Biology.PopulationGenetics.WrightFisherChain
