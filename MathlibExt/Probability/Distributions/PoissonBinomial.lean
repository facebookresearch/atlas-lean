/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BernoulliSumPmf
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The Poisson-binomial law: tail monotonicity and Le Cam's bound

The number of successes `S = X₁ + ⋯ + Xₘ` among independent Bernoulli trials with
probabilities `p₁, …, pₘ` has the *Poisson-binomial* mass function
`P(S = j) = ∑_{|A| = j} ∏_{i ∈ A} pᵢ ∏_{i ∉ A} (1 - pᵢ)` (`ProbabilityTheory.bernoulli_sum_pmf`).
This is the null law of a burden (mutation-count) test when each sample has its own background
rate `pᵢ`, as in cancer driver-gene tests with per-patient mutation rates (Lawrence et al. 2013
motivate per-sample heterogeneity; this file does not formalize their test).

* Tail monotonicity: the one-sided p-value `P(S ≥ k)` is nondecreasing in every `pᵢ`; exactly,
  adding a trial with probability `a` gives `P(S' ≥ k + 1) = P(S ≥ k + 1) + a · P(S = k)`.
  With all `pᵢ = p` this is the binomial law, so the binomial upper tail
  `∑_{j ≥ k} C(n, j) p^j (1 - p)^{n - j}` is nondecreasing in `p ∈ [0, 1]`.
* Le Cam's inequality: with `λ = ∑ pᵢ`,
  `∑_j |P(S = j) - e^{-λ} λ^j / j!| ≤ 2 ∑ pᵢ²` (Le Cam 1960), stated for every finite
  truncation of the sum and for the full (summable) series.

## Main results

* `ProbabilityTheory.poissonBinomialPMF`, `ProbabilityTheory.poissonBinomialTail`.
* `ProbabilityTheory.poissonBinomialPMF_cons_succ`,
  `ProbabilityTheory.poissonBinomialTail_cons_succ`: exact effect of one extra trial on the mass
  function and on the tail.
* `ProbabilityTheory.poissonBinomialTail_mono`: the tail is monotone in the probability vector.
* `ProbabilityTheory.binomialTail_mono`, `ProbabilityTheory.binomial_real_Ici_mono`: the
  binomial upper tail is nondecreasing in `p`.
* `ProbabilityTheory.measure_le_sum_eq_poissonBinomialTail`: `P(S ≥ k)` for independent
  Bernoulli variables is the Poisson-binomial tail.
* `ProbabilityTheory.sum_range_abs_poissonBinomialPMF_sub_poisson_le`,
  `ProbabilityTheory.tsum_abs_poissonBinomialPMF_sub_poisson_le`: Le Cam's bound.

## References

* L. Le Cam, *An approximation theorem for the Poisson binomial distribution*,
  Pacific J. Math. 10 (1960) 1181–1197.
* M. S. Lawrence et al., *Mutational heterogeneity in cancer and the search for new
  cancer-associated genes*, Nature 499 (2013) 214–218.
-/

@[expose] public section

open MeasureTheory Real Finset Polynomial
open scoped Nat

namespace ProbabilityTheory

/-- Poisson-binomial mass function of the number of successes among independent trials with
success probabilities `p : Fin m → ℝ`:
`∑_{A ⊆ [m], |A| = j} ∏_{i ∈ A} p i ∏_{i ∉ A} (1 - p i)`. A probability mass function when
every `p i ∈ [0, 1]`; the algebraic identities below hold for all real `p`. -/
noncomputable def poissonBinomialPMF {m : ℕ} (p : Fin m → ℝ) (j : ℕ) : ℝ :=
  ∑ A ∈ (univ : Finset (Fin m)).powersetCard j, (∏ i ∈ A, p i) * ∏ i ∈ univ \ A, (1 - p i)

/-- Upper tail `P(S ≥ k) = ∑_{k ≤ j ≤ m} P(S = j)` of the Poisson-binomial law (the mass
function vanishes above `m`). -/
noncomputable def poissonBinomialTail {m : ℕ} (p : Fin m → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Icc k m, poissonBinomialPMF p j

/-- Generating polynomial `∏ i, (p i X + (1 - p i))` (proof device). -/
private noncomputable def pbPoly {m : ℕ} (p : Fin m → ℝ) : ℝ[X] := ∏ i, (C (p i) * X + C (1 - p i))

private theorem coeff_pbPoly {m : ℕ} (p : Fin m → ℝ) (j : ℕ) :
    (pbPoly p).coeff j = poissonBinomialPMF p j := by
  classical
  unfold pbPoly poissonBinomialPMF
  rw [Finset.prod_add, finsetSum_coeff, powersetCard_eq_filter, sum_filter]
  refine sum_congr rfl fun t _ => ?_
  rw [prod_mul_distrib, prod_const, ← map_prod, ← map_prod, mul_comm (C _), mul_assoc,
    ← C_mul, coeff_X_pow_mul', coeff_C]
  split_ifs <;> first | rfl | omega

private theorem pbPoly_cons {m : ℕ} (a : ℝ) (q : Fin m → ℝ) :
    pbPoly (Fin.cons a q : Fin (m + 1) → ℝ) = (C a * X + C (1 - a)) * pbPoly q := by
  simp [pbPoly, Fin.prod_univ_succ]

/-- The Poisson-binomial mass function is nonnegative for probabilities in `[0, 1]`. -/
theorem poissonBinomialPMF_nonneg {m : ℕ} {p : Fin m → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (j : ℕ) :
    0 ≤ poissonBinomialPMF p j :=
  sum_nonneg fun _ _ => mul_nonneg (prod_nonneg fun i _ => (hp i).1)
    (prod_nonneg fun i _ => sub_nonneg.mpr (hp i).2)

/-- The Poisson-binomial mass function vanishes above the number of trials. -/
theorem poissonBinomialPMF_eq_zero_of_lt {m : ℕ} (p : Fin m → ℝ) {j : ℕ} (hj : m < j) :
    poissonBinomialPMF p j = 0 := by
  unfold poissonBinomialPMF
  rw [powersetCard_eq_empty.mpr (by simpa using hj), sum_empty]

/-- Adding a trial with probability `a`: no successes requires a failure of the new trial. -/
theorem poissonBinomialPMF_cons_zero {m : ℕ} (a : ℝ) (q : Fin m → ℝ) :
    poissonBinomialPMF (Fin.cons a q : Fin (m + 1) → ℝ) 0 = (1 - a) * poissonBinomialPMF q 0 := by
  rw [← coeff_pbPoly, ← coeff_pbPoly, pbPoly_cons, add_mul, coeff_add, mul_assoc, coeff_C_mul,
    coeff_X_mul_zero, mul_zero, zero_add, coeff_C_mul]

/-- Adding a trial with probability `a`: first-step decomposition of the mass function,
`P(S' = j + 1) = a P(S = j) + (1 - a) P(S = j + 1)`. -/
theorem poissonBinomialPMF_cons_succ {m : ℕ} (a : ℝ) (q : Fin m → ℝ) (j : ℕ) :
    poissonBinomialPMF (Fin.cons a q : Fin (m + 1) → ℝ) (j + 1) =
      a * poissonBinomialPMF q j + (1 - a) * poissonBinomialPMF q (j + 1) := by
  rw [← coeff_pbPoly, ← coeff_pbPoly, ← coeff_pbPoly, pbPoly_cons, add_mul, coeff_add, mul_assoc,
    coeff_C_mul, coeff_X_mul, coeff_C_mul]

/-- The Poisson-binomial masses sum to one (an identity for all real `p`; it is the expansion
of `∏ ((1 - p i) + p i) = 1`). -/
theorem sum_poissonBinomialPMF {m : ℕ} (p : Fin m → ℝ) :
    ∑ j ∈ range (m + 1), poissonBinomialPMF p j = 1 := by
  induction m with
  | zero => simp [poissonBinomialPMF]
  | succ m ih =>
    rw [← Fin.cons_self_tail p, sum_range_succ', poissonBinomialPMF_cons_zero]
    simp_rw [poissonBinomialPMF_cons_succ]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, ih (Fin.tail p)]
    have h : ∑ i ∈ range (m + 1), poissonBinomialPMF (Fin.tail p) (i + 1) +
        poissonBinomialPMF (Fin.tail p) 0 = 1 := by
      rw [← sum_range_succ' (fun j => poissonBinomialPMF (Fin.tail p) j) (m + 1), sum_range_succ,
        poissonBinomialPMF_eq_zero_of_lt _ (by omega : m < m + 1), add_zero, ih]
    linear_combination (1 - p 0) * h

/-- Peeling off the lowest term of the tail: `P(S ≥ k) = P(S = k) + P(S ≥ k + 1)`. -/
theorem poissonBinomialTail_eq_add {m : ℕ} (q : Fin m → ℝ) (k : ℕ) :
    poissonBinomialTail q k = poissonBinomialPMF q k + poissonBinomialTail q (k + 1) := by
  unfold poissonBinomialTail
  rcases le_or_gt k m with hk | hk
  · rw [← add_sum_Ioc_eq_sum_Icc hk, Icc_add_one_left_eq_Ioc]
  · rw [poissonBinomialPMF_eq_zero_of_lt _ hk, Icc_eq_empty (by omega), Icc_eq_empty (by omega)]
    simp

/-- Adding a trial with probability `a` raises the upper tail by exactly `a P(S = k)`:
`P(S' ≥ k + 1) = P(S ≥ k + 1) + a P(S = k)`. So the tail is affine in each trial's probability,
with nonnegative slope a point mass of the remaining trials. -/
theorem poissonBinomialTail_cons_succ {m : ℕ} (a : ℝ) (q : Fin m → ℝ) (k : ℕ) :
    poissonBinomialTail (Fin.cons a q : Fin (m + 1) → ℝ) (k + 1) =
      poissonBinomialTail q (k + 1) + a * poissonBinomialPMF q k := by
  have hshift : ∀ f : ℕ → ℝ, ∑ j ∈ Icc (k + 1) (m + 1), f j = ∑ i ∈ Icc k m, f (i + 1) := by
    intro f
    rw [← map_add_right_Icc, sum_map]
    rfl
  unfold poissonBinomialTail
  rw [hshift]
  simp_rw [poissonBinomialPMF_cons_succ]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have h1 : ∑ i ∈ Icc k m, poissonBinomialPMF q (i + 1) = poissonBinomialTail q (k + 1) := by
    rw [← hshift (poissonBinomialPMF q), poissonBinomialTail]
    rcases le_or_gt (k + 1) (m + 1) with hk | hk
    · rw [sum_Icc_succ_top hk, poissonBinomialPMF_eq_zero_of_lt _ (by omega), add_zero]
    · rw [Icc_eq_empty (by omega), Icc_eq_empty (by omega)]
  have h2 := poissonBinomialTail_eq_add q k
  unfold poissonBinomialTail at h2
  rw [h1, h2]
  unfold poissonBinomialTail
  ring

/-- **The burden-test p-value is monotone in every background rate**: if `p i ≤ q i` for all
`i`, with all probabilities in `[0, 1]`, then `P_p(S ≥ k) ≤ P_q(S ≥ k)`. -/
theorem poissonBinomialTail_mono {m : ℕ} {p q : Fin m → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1) (hpq : ∀ i, p i ≤ q i) (k : ℕ) :
    poissonBinomialTail p k ≤ poissonBinomialTail q k := by
  induction m generalizing k with
  | zero =>
    rw [Subsingleton.elim p q]
  | succ m ih =>
    have htot : ∀ r : Fin (m + 1) → ℝ, poissonBinomialTail r 0 = 1 := fun r => by
      rw [poissonBinomialTail, ← sum_poissonBinomialPMF r, Nat.range_succ_eq_Icc_zero]
    cases k with
    | zero => rw [htot, htot]
    | succ k =>
      rw [← Fin.cons_self_tail p, ← Fin.cons_self_tail q, poissonBinomialTail_cons_succ,
        poissonBinomialTail_cons_succ]
      have hp' : ∀ i, Fin.tail p i ∈ Set.Icc (0 : ℝ) 1 := fun i => hp i.succ
      have hq' : ∀ i, Fin.tail q i ∈ Set.Icc (0 : ℝ) 1 := fun i => hq i.succ
      have hpq' : ∀ i, Fin.tail p i ≤ Fin.tail q i := fun i => hpq i.succ
      have e1 := poissonBinomialTail_eq_add (Fin.tail p) k
      have e2 := poissonBinomialTail_eq_add (Fin.tail q) k
      have i1 := ih hp' hq' hpq' k
      have i2 := ih hp' hq' hpq' (k + 1)
      have hn := poissonBinomialPMF_nonneg hq' k
      have ha := hp 0
      have hb := hpq 0
      have ha1 : p 0 ≤ 1 := ha.2
      nlinarith [ha.1, mul_le_mul_of_nonneg_left i1 ha.1,
        mul_le_mul_of_nonneg_left i2 (sub_nonneg.mpr ha1), mul_le_mul_of_nonneg_right hb hn]

/-- With equal probabilities the Poisson-binomial law is the binomial law. -/
theorem poissonBinomialPMF_const {m : ℕ} (a : ℝ) (j : ℕ) :
    poissonBinomialPMF (fun _ : Fin m => a) j = (m.choose j : ℝ) * a ^ j * (1 - a) ^ (m - j) := by
  unfold poissonBinomialPMF
  calc _ = ∑ t ∈ powersetCard j (univ : Finset (Fin m)), a ^ j * (1 - a) ^ (m - j) :=
        sum_congr rfl fun t ht => by
          rw [mem_powersetCard] at ht
          rw [prod_const, prod_const, card_univ_sdiff, ht.2, Fintype.card_fin]
    _ = _ := by
      rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/-- **Binomial tail monotonicity**: for `0 ≤ p ≤ q ≤ 1`,
`∑_{k ≤ j ≤ n} C(n, j) p^j (1 - p)^{n - j} ≤ ∑_{k ≤ j ≤ n} C(n, j) q^j (1 - q)^{n - j}`. -/
theorem binomialTail_mono {n k : ℕ} {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) :
    ∑ j ∈ Icc k n, (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j) ≤
      ∑ j ∈ Icc k n, (n.choose j : ℝ) * q ^ j * (1 - q) ^ (n - j) := by
  have h : ∀ r : ℝ, ∑ j ∈ Icc k n, (n.choose j : ℝ) * r ^ j * (1 - r) ^ (n - j) =
      poissonBinomialTail (fun _ : Fin n => r) k := fun r => by
    unfold poissonBinomialTail
    simp_rw [poissonBinomialPMF_const]
  rw [h, h]
  exact poissonBinomialTail_mono (fun _ => ⟨hp, hpq.trans hq⟩) (fun _ => ⟨hp.trans hpq, hq⟩)
    (fun _ => hpq) k

/-- The upper tail `Bin(n, p)([k, ∞))` of Mathlib's binomial law is monotone in `p`. -/
theorem binomial_real_Ici_mono (n k : ℕ) :
    Monotone fun p : unitInterval => (binomial n p).real (Set.Ici k) := by
  have hreal : ∀ p : unitInterval, (binomial n p).real (Set.Ici k) =
      ∑ j ∈ Icc k n, (n.choose j : ℝ) * (p : ℝ) ^ j * (1 - (p : ℝ)) ^ (n - j) := by
    intro p
    have hae : ∀ᵐ j ∂(binomial n p), j ≤ n := ae_le_of_hasLaw_binomial (HasLaw.id)
    have hset : (Set.Ici k : Set ℕ) =ᵐ[binomial n p] (↑(Icc k n) : Set ℕ) := by
      filter_upwards [hae] with j hj
      simp [hj]
    rw [MeasureTheory.measureReal_congr hset, ← MeasureTheory.sum_measureReal_singleton]
    exact sum_congr rfl fun j _ => binomial_real_singleton n j p
  intro p q hpq
  simp only
  rw [hreal, hreal]
  exact binomialTail_mono p.2.1 hpq q.2.2

/-- For independent Bernoulli variables `X i` with parameters `p i`, the one-sided burden
p-value `P(∑ X i ≥ k)` is the Poisson-binomial tail. -/
theorem measure_le_sum_eq_poissonBinomialTail {m : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin m → Ω → ℕ} {p : Fin m → ℝ}
    (hBernoulli : ∀ i, IsBernoulliRV (X i) μ (p i)) (hIndep : iIndepFun X μ)
    (hMeas : ∀ i, Measurable (X i)) (k : ℕ) :
    (μ {ω | k ≤ ∑ i, X i ω}).toReal = poissonBinomialTail p k := by
  classical
  set S : Ω → ℕ := fun ω => ∑ i, X i ω with hSdef
  have hS : Measurable S := Finset.measurable_sum _ fun i _ => hMeas i
  have hpt : ∀ j : ℕ, μ.real (S ⁻¹' {j}) = poissonBinomialPMF p j := fun j => by
    have := bernoulli_sum_pmf hBernoulli hIndep hMeas j
    rw [measureReal_def]
    exact this
  have hunion : ∀ s : Finset ℕ, μ.real (⋃ j ∈ s, S ⁻¹' {j}) = ∑ j ∈ s, poissonBinomialPMF p j :=
    fun s => by
      rw [measureReal_biUnion_finset _ (fun j _ => hS (measurableSet_singleton j))]
      · exact sum_congr rfl fun j _ => hpt j
      · intro a _ b _ hab
        exact Set.disjoint_left.mpr fun ω h1 h2 => hab (h1.symm.trans h2)
  have hle : μ {ω | S ω ≤ m} = 1 := by
    have hset : {ω | S ω ≤ m} = ⋃ j ∈ range (m + 1), S ⁻¹' {j} := by
      ext ω; simp
    rw [← ENNReal.toReal_eq_one_iff, ← measureReal_def, hset, hunion, sum_poissonBinomialPMF]
  have hae : ∀ᵐ ω ∂μ, S ω ≤ m := by
    have hmeas : MeasurableSet {ω | S ω ≤ m} := hS measurableSet_Iic
    rw [ae_iff]
    have := (prob_compl_eq_zero_iff hmeas).mpr hle
    simpa [Set.compl_ofPred, not_le] using this
  have hcongr : {ω | k ≤ S ω} =ᵐ[μ] (⋃ j ∈ Icc k m, S ⁻¹' {j} : Set Ω) := by
    filter_upwards [hae] with ω hω
    simp only [eq_iff_iff]
    simp [hω]
  rw [← measureReal_def, measureReal_congr hcongr, hunion]
  rfl


/-- Poisson mass `e^{-l} l^j / j!` (proof device for Le Cam). -/
private noncomputable def pmass (l : ℝ) (j : ℕ) : ℝ := exp (-l) * l ^ j / (j ! : ℝ)

private lemma poi_nonneg {l : ℝ} (hl : 0 ≤ l) (j : ℕ) : 0 ≤ pmass l j := by
  unfold pmass; positivity

private lemma sum_poi_le {l : ℝ} (hl : 0 ≤ l) (N : ℕ) : ∑ j ∈ range N, pmass l j ≤ 1 := by
  unfold pmass
  simp_rw [mul_div_assoc]
  rw [← mul_sum]
  calc exp (-l) * ∑ i ∈ range N, l ^ i / (i ! : ℝ) ≤ exp (-l) * exp l :=
        mul_le_mul_of_nonneg_left (sum_le_exp_of_nonneg hl N) (exp_pos _).le
    _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]

private lemma poi_add (a l : ℝ) (j : ℕ) :
    pmass (a + l) j = ∑ i ∈ range (j + 1), pmass a i * pmass l (j - i) := by
  unfold pmass
  rw [add_pow, mul_div_assoc, sum_div, mul_sum, neg_add, exp_add]
  refine sum_congr rfl fun i hi => ?_
  have hij : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have h := Nat.choose_mul_factorial_mul_factorial hij
  have hf : ((j - i) ! : ℝ) ≠ 0 := by positivity
  have hf' : (i ! : ℝ) ≠ 0 := by positivity
  have hc : (j.choose i : ℝ) = (j ! : ℝ) / ((i ! : ℝ) * ((j - i) ! : ℝ)) := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast (by rw [← mul_assoc]; exact h)
  rw [hc]
  field_simp

/-- Bernoulli mass `(1 - a, a)` on `{0, 1}` (proof device for Le Cam). -/
private noncomputable def bmass (a : ℝ) : ℕ → ℝ
  | 0 => 1 - a
  | 1 => a
  | _ + 2 => 0

private lemma pmf_cons_eq_conv {m : ℕ} (a : ℝ) (q : Fin m → ℝ) (j : ℕ) :
    poissonBinomialPMF (Fin.cons a q : Fin (m + 1) → ℝ) j =
      ∑ i ∈ range (j + 1), bmass a i * poissonBinomialPMF q (j - i) := by
  cases j with
  | zero => simp [poissonBinomialPMF_cons_zero, bmass]
  | succ j =>
    rw [poissonBinomialPMF_cons_succ, sum_range_succ', sum_range_succ']
    have : ∀ i ∈ range j, bmass a (i + 1 + 1) * poissonBinomialPMF q (j + 1 - (i + 1 + 1)) = 0 :=
      fun i _ => by simp [bmass]
    rw [sum_eq_zero this]
    simp [bmass]

private lemma cauchy_le (f g : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ k, 0 ≤ g k) (N : ℕ) :
    ∑ j ∈ range N, ∑ i ∈ range (j + 1), f i * g (j - i) ≤
      (∑ i ∈ range N, f i) * ∑ k ∈ range N, g k := by
  rw [sum_comm' (t' := range N) (s' := fun i => Ico i N)]
  · rw [sum_mul]
    refine sum_le_sum fun i hi => ?_
    rw [← mul_sum, sum_Ico_eq_sum_range]
    refine mul_le_mul_of_nonneg_left ?_ (hf i)
    simp only [add_tsub_cancel_left]
    exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (Nat.sub_le _ _))
      fun k _ _ => hg k
  · intro j i
    simp only [mem_range, mem_Ico]
    omega

private lemma ber_nonneg {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (i : ℕ) : 0 ≤ bmass a i := by
  rcases i with _ | _ | i
  · simp [bmass, ha.2]
  · simp [bmass, ha.1]
  · simp [bmass]

private lemma sum_ber_le {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (N : ℕ) :
    ∑ i ∈ range N, bmass a i ≤ 1 := by
  calc ∑ i ∈ range N, bmass a i ≤ ∑ i ∈ range (N + 2), bmass a i :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
          fun i _ _ => ber_nonneg ha i
    _ = 1 := by
      induction N with
      | zero => simp [sum_range_succ, bmass]
      | succ N ih => rw [sum_range_succ, ih]; simp [bmass]

private lemma sum_abs_ber_sub_poi_le {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (N : ℕ) :
    ∑ i ∈ range N, |bmass a i - pmass a i| ≤ 2 * a ^ 2 := by
  have h0 : 1 - a ≤ exp (-a) := by linarith [add_one_le_exp (-a)]
  have h1 : 1 - exp (-a) ≤ a := by linarith [add_one_le_exp (-a)]
  have he : exp (-a) ≤ 1 := exp_le_one_iff.mpr (by linarith [ha.1])
  calc ∑ i ∈ range N, |bmass a i - pmass a i| ≤ ∑ i ∈ range (N + 2), |bmass a i - pmass a i| :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
          fun i _ _ => abs_nonneg _
    _ = |1 - a - exp (-a)| + |a - exp (-a) * a| + ∑ i ∈ range N, pmass a (i + 1 + 1) := by
        rw [sum_range_succ', sum_range_succ']
        have : ∀ i ∈ range N, |bmass a (i + 1 + 1) - pmass a (i + 1 + 1)| = pmass a (i + 1 + 1) :=
          fun i _ => by
            simp only [bmass, zero_sub, abs_neg]
            exact abs_of_nonneg (poi_nonneg ha.1 _)
        rw [sum_congr rfl this]
        simp [bmass, pmass]
        ring
    _ ≤ (exp (-a) - (1 - a)) + a * (1 - exp (-a)) + (1 - exp (-a) - a * exp (-a)) := by
        have hs := sum_poi_le ha.1 (N + 2)
        rw [sum_range_succ', sum_range_succ'] at hs
        have hp0 : pmass a 0 = exp (-a) := by simp [pmass]
        have hp1 : pmass a (0 + 1) = exp (-a) * a := by simp [pmass]
        gcongr
        · rw [abs_of_nonpos (by linarith)]; linarith
        · rw [abs_of_nonneg (by nlinarith)]; linarith
        · linarith
    _ = 2 * a * (1 - exp (-a)) := by ring
    _ ≤ 2 * a ^ 2 := by nlinarith [ha.1]

/-- **Le Cam's inequality, finite truncations**: for probabilities `p i ∈ [0, 1]` and
`λ = ∑ p i`, every partial sum of `∑_j |P(S = j) - e^{-λ} λ^j / j!|` is at most `2 ∑ (p i)²`. -/
theorem sum_range_abs_poissonBinomialPMF_sub_poisson_le {m : ℕ} {p : Fin m → ℝ}
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (N : ℕ) :
    ∑ j ∈ range N, |poissonBinomialPMF p j - exp (-∑ i, p i) * (∑ i, p i) ^ j / (j ! : ℝ)| ≤
      2 * ∑ i, p i ^ 2 := by
  induction m generalizing N with
  | zero =>
    have : ∀ j ∈ range N, |poissonBinomialPMF p j - exp (-∑ i, p i) * (∑ i, p i) ^ j /
        (j ! : ℝ)| = 0 := by
      intro j _
      rcases j with _ | j
      · simp [poissonBinomialPMF]
      · rw [poissonBinomialPMF_eq_zero_of_lt _ (Nat.succ_pos j)]
        simp
    rw [sum_congr rfl this]
    simp
  | succ m ih =>
    rw [← Fin.cons_self_tail p]
    set a := p 0
    set q := Fin.tail p
    have hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1 := fun i => hp i.succ
    have ha : a ∈ Set.Icc (0 : ℝ) 1 := hp 0
    have hl : 0 ≤ ∑ i, q i := sum_nonneg fun i _ => (hq i).1
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    change ∑ j ∈ range N, |poissonBinomialPMF (Fin.cons a q : Fin (m + 1) → ℝ) j -
        pmass (a + ∑ i, q i) j| ≤ 2 * (a ^ 2 + ∑ i, q i ^ 2)
    set l := ∑ i, q i
    set e : ℕ → ℝ := fun k => poissonBinomialPMF q k - pmass l k
    have hstep : ∀ j, |poissonBinomialPMF (Fin.cons a q : Fin (m + 1) → ℝ) j - pmass (a + l) j| ≤
        ∑ i ∈ range (j + 1), bmass a i * |e (j - i)| +
          ∑ i ∈ range (j + 1), |bmass a i - pmass a i| * pmass l (j - i) := by
      intro j
      rw [pmf_cons_eq_conv, poi_add, ← sum_sub_distrib, ← sum_add_distrib]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
      have hb := ber_nonneg ha i
      have hpl := poi_nonneg hl (j - i)
      calc |bmass a i * poissonBinomialPMF q (j - i) - pmass a i * pmass l (j - i)|
          = |bmass a i * e (j - i) + (bmass a i - pmass a i) * pmass l (j - i)| := by
            congr 1; simp only [e]; ring
        _ ≤ |bmass a i * e (j - i)| + |(bmass a i - pmass a i) * pmass l (j - i)| := abs_add_le _ _
        _ = bmass a i * |e (j - i)| + |bmass a i - pmass a i| * pmass l (j - i) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hb, abs_of_nonneg hpl]
    have ih' := ih hq N
    change ∑ j ∈ range N, |e j| ≤ 2 * ∑ i, q i ^ 2 at ih'
    calc ∑ j ∈ range N, |poissonBinomialPMF (Fin.cons a q : Fin (m + 1) → ℝ) j - pmass (a + l) j|
        ≤ ∑ j ∈ range N, (∑ i ∈ range (j + 1), bmass a i * |e (j - i)| +
          ∑ i ∈ range (j + 1), |bmass a i - pmass a i| * pmass l (j - i)) :=
            sum_le_sum fun j _ => hstep j
      _ = ∑ j ∈ range N, ∑ i ∈ range (j + 1), bmass a i * |e (j - i)| +
          ∑ j ∈ range N, ∑ i ∈ range (j + 1), |bmass a i - pmass a i| * pmass l (j - i) :=
            sum_add_distrib
      _ ≤ (∑ i ∈ range N, bmass a i) * ∑ k ∈ range N, |e k| +
          (∑ i ∈ range N, |bmass a i - pmass a i|) * ∑ k ∈ range N, pmass l k :=
            add_le_add (cauchy_le _ _ (ber_nonneg ha) (fun _ => abs_nonneg _) N)
              (cauchy_le _ _ (fun _ => abs_nonneg _) (poi_nonneg hl) N)
      _ ≤ 1 * (2 * ∑ i, q i ^ 2) + 2 * a ^ 2 * 1 := by
          have h1 := sum_ber_le ha N
          have h2 := sum_abs_ber_sub_poi_le ha N
          have h3 := sum_poi_le hl N
          have h4 : 0 ≤ ∑ k ∈ range N, |e k| := sum_nonneg fun _ _ => abs_nonneg _
          have h5 : 0 ≤ ∑ i ∈ range N, bmass a i := sum_nonneg fun i _ => ber_nonneg ha i
          have h6 : 0 ≤ ∑ i ∈ range N, |bmass a i - pmass a i| := sum_nonneg fun _ _ => abs_nonneg _
          have h7 : 0 ≤ ∑ k ∈ range N, pmass l k := sum_nonneg fun k _ => poi_nonneg hl k
          have h8 := mul_le_mul h1 ih' h4 zero_le_one
          have h9 := mul_le_mul h2 h3 h7 (by positivity)
          linarith
      _ = 2 * (a ^ 2 + ∑ i, q i ^ 2) := by ring

/-- **Le Cam's inequality** (Le Cam 1960): the series `∑_j |P(S = j) - e^{-λ} λ^j / j!|` is
summable and its sum is at most `2 ∑ (p i)²`, where `λ = ∑ p i`. -/
theorem tsum_abs_poissonBinomialPMF_sub_poisson_le {m : ℕ} {p : Fin m → ℝ}
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    Summable (fun j : ℕ =>
        |poissonBinomialPMF p j - exp (-∑ i, p i) * (∑ i, p i) ^ j / (j ! : ℝ)|) ∧
      ∑' j : ℕ, |poissonBinomialPMF p j - exp (-∑ i, p i) * (∑ i, p i) ^ j / (j ! : ℝ)| ≤
        2 * ∑ i, p i ^ 2 :=
  ⟨summable_of_sum_range_le (fun _ => abs_nonneg _)
      (sum_range_abs_poissonBinomialPMF_sub_poisson_le hp),
    Real.tsum_le_of_sum_range_le (fun _ => abs_nonneg _)
      (sum_range_abs_poissonBinomialPMF_sub_poisson_le hp)⟩

end ProbabilityTheory
