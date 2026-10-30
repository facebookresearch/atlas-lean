/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.ExponentialMoments
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.NumberTheory.Harmonic.Int
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Nat.Choose.Cast

/-!
# Kingman's coalescent: holding times, tree lengths, Watterson's estimator

We work with the standard (Kingman) coalescent for a sample of `n` gene copies. Time is
measured in units of `2N` generations for a diploid population of `N` individuals (`M = 2N`
gene copies); the scaled mutation rate is `θ = 4Nu`, where `u` is the per-generation,
per-copy mutation rate, so that mutations fall on each lineage at rate `θ / 2` per unit time.

While the genealogy has `k` lineages, each of the `k.choose 2` pairs coalesces at rate `1`, so
the holding time `T k` with exactly `k` lineages is exponential with rate `k.choose 2`, and the
holding times `T 2, …, T n` are independent (`KingmanTimes`). Then

* the time to the most recent common ancestor `T_MRCA = ∑_{k=2}^n T k` has mean
  `2 (1 - 1/n)` and variance `∑_{k=2}^n (k.choose 2)⁻² `;
* the total branch length `L = ∑_{k=2}^n k T k` has mean `2 H_{n-1}` (harmonic number);
* under infinite-sites mutation at rate `θ/2` per lineage, the number `S` of segregating sites
  has conditional mean `(θ/2) L` given the genealogy, so `E S = θ H_{n-1}` and Watterson's
  estimator `S / H_{n-1}` is unbiased for `θ`.

Finally we derive the coalescent rate from the Wright–Fisher model: in a population of `M`
gene copies, `k` lineages choosing parents independently and uniformly have distinct parents
with probability `noCoalProb M k = ∏_{i<k} (1 - i/M) = M^{(k)}/M^k` (falling factorial), and
`M (1 - noCoalProb M k) → k.choose 2` as `M → ∞`; after `⌊t M⌋` generations
(`t` coalescent time units when `M = 2N`), the probability of no coalescence tends to
`exp (-(k.choose 2) t)`, the survival function of `Exp (k.choose 2)`.

## Main results

* `KingmanTimes`: the holding-time model.
* `KingmanTimes.integral_tmrca`: `E[T_MRCA] = 2 (1 - 1/n)`.
* `KingmanTimes.variance_tmrca`: `Var[T_MRCA] = ∑_{k=2}^n ((k.choose 2)⁻¹)²`.
* `KingmanTimes.integral_totalLength`: `E[L] = 2 H_{n-1}`.
* `KingmanTimes.integral_segSites`, `KingmanTimes.watterson_unbiased`: Watterson (1975), for
  an integrable number of segregating sites; `KingmanTimes.integrable_watterson`.
* `KingmanTimes.ofPi`: a concrete model (product of exponential laws), so the structure is
  inhabited for every `n`.
* `noCoalProb_eq_descFactorial_div`, `tendsto_coalescence_rate`,
  `tendsto_noCoalProb_pow_floor`: the Wright–Fisher → Kingman limit.

## References

* J. F. C. Kingman, *The coalescent*, Stochastic Process. Appl. 13 (1982), 235–248.
* G. A. Watterson, *On the number of segregating sites in genetical models without
  recombination*, Theor. Popul. Biol. 7 (1975), 256–276.
* J. Wakeley, *Coalescent Theory: An Introduction* (2009), ch. 3.
* R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed. (2008), §1.2–1.4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent

/-! ### Elementary sums -/

/-- `∑_{k=2}^n (k.choose 2)⁻¹ = 2 (1 - 1/n)` for `n ≥ 1` (telescoping `2/(k(k-1))`). -/
theorem sum_inv_choose_two {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Icc 2 n, ((k.choose 2 : ℕ) : ℝ)⁻¹ = 2 * (1 - 1 / n) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [sum_Icc_succ_top (by omega), ih, Nat.cast_choose_two]
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring_nf
    rw [mul_inv_cancel₀ hn0]
    ring

/-- `∑_{k=2}^n k (k.choose 2)⁻¹ = 2 H_{n-1}`. -/
theorem sum_mul_inv_choose_two (n : ℕ) :
    ∑ k ∈ Icc 2 n, (k : ℝ) * ((k.choose 2 : ℕ) : ℝ)⁻¹ = 2 * (harmonic (n - 1) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [sum_Icc_succ_top (by omega), ih, Nat.cast_choose_two]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, harmonic_succ]
    push_cast
    field_simp
    ring

/-! ### The holding-time model -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Kingman's coalescent for a sample of size `n`, through its holding times: `T k` is the
time (in units of `2N` generations) during which the genealogy has exactly `k` lineages,
for `2 ≤ k ≤ n`. These are independent, and `T k` is exponential with rate `k.choose 2`.
The values of `T k` for `k ∉ [2, n]` are irrelevant. -/
structure KingmanTimes (μ : Measure Ω) (n : ℕ) where
  /-- `T k` is the holding time while the genealogy has `k` lineages. -/
  T : ℕ → Ω → ℝ
  /-- `T k` is exponential with rate `k.choose 2`, the number of pairs of lineages. -/
  hasLaw : ∀ k ∈ Icc 2 n, HasLaw (T k) (expMeasure (k.choose 2 : ℕ)) μ
  /-- The holding times are mutually independent. -/
  indep : iIndepFun (fun k : Icc 2 n => T k) μ

namespace KingmanTimes

variable {μ : Measure Ω} {n : ℕ} (K : KingmanTimes μ n)

/-- Time to the most recent common ancestor of the sample. -/
def tmrca : Ω → ℝ := fun ω => ∑ k ∈ Icc 2 n, K.T k ω

/-- Total branch length of the sample genealogy: `k` branches during `T k`. -/
def totalLength : Ω → ℝ := fun ω => ∑ k ∈ Icc 2 n, (k : ℝ) * K.T k ω

/-- The number of pairs `k.choose 2` is positive for `k ∈ [2, n]`. -/
lemma choose_two_pos {k : ℕ} (hk : k ∈ Icc 2 n) : (0 : ℝ) < ((k.choose 2 : ℕ) : ℝ) := by
  have : 2 ≤ k := (mem_Icc.1 hk).1
  exact_mod_cast Nat.choose_pos this

/-- Each holding time is integrable. -/
theorem integrable_T {k : ℕ} (hk : k ∈ Icc 2 n) : Integrable (K.T k) μ :=
  (K.hasLaw k hk).integrable_of_expMeasure (choose_two_pos hk)

/-- `E[T k] = (k.choose 2)⁻¹`. -/
theorem integral_T {k : ℕ} (hk : k ∈ Icc 2 n) : μ[K.T k] = ((k.choose 2 : ℕ) : ℝ)⁻¹ :=
  (K.hasLaw k hk).integral_eq_inv_of_expMeasure (choose_two_pos hk)

/-- The expected time to the most recent common ancestor is `2 (1 - 1/n)`. -/
theorem integral_tmrca (hn : 1 ≤ n) : μ[K.tmrca] = 2 * (1 - 1 / (n : ℝ)) := by
  unfold tmrca
  rw [ integral_finsetSum _ (fun k hk => K.integrable_T hk),
    sum_congr rfl (fun k hk => K.integral_T hk), sum_inv_choose_two hn]

/-- The total branch length is integrable. -/
theorem integrable_totalLength : Integrable K.totalLength μ :=
  integrable_finsetSum _ (fun _ hk => (K.integrable_T hk).const_mul _)

/-- The expected total branch length is `2 H_{n-1}`. -/
theorem integral_totalLength : μ[K.totalLength] = 2 * (harmonic (n - 1) : ℝ) := by
  unfold totalLength
  rw [integral_finsetSum _ (fun k hk => (K.integrable_T hk).const_mul _),
    sum_congr rfl (fun k hk => by rw [integral_const_mul, K.integral_T hk]),
    sum_mul_inv_choose_two]

/-- The variance of the time to the most recent common ancestor is
`∑_{k=2}^n ((k.choose 2)⁻¹)²` (this uses independence). -/
theorem variance_tmrca :
    Var[K.tmrca; μ] = ∑ k ∈ Icc 2 n, (((k.choose 2 : ℕ) : ℝ)⁻¹) ^ 2 := by
  have hmem : ∀ i ∈ (univ : Finset (Icc 2 n)), MemLp (K.T i) 2 μ := fun i _ =>
    (K.hasLaw i i.2).memLp_comp (f := id)
      ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
        (by simpa using integrable_pow_expMeasure (choose_two_pos i.2) 2))
  have hpair : Set.Pairwise ↑(univ : Finset (Icc 2 n)) fun i j : Icc 2 n => K.T i ⟂ᵢ[μ] K.T j :=
    fun i _ j _ hij => K.indep.indepFun (i := i) (j := j) hij
  have htm : K.tmrca = ∑ i ∈ (univ : Finset (Icc 2 n)), K.T i := by
    funext ω
    rw [tmrca, Finset.sum_apply, sum_coe_sort (Icc 2 n) (fun k => K.T k ω)]
  rw [htm, IndepFun.variance_sum hmem hpair,
    ← sum_coe_sort (Icc 2 n) (fun k => (((k.choose 2 : ℕ) : ℝ)⁻¹) ^ 2)]
  exact sum_congr rfl fun i _ =>
    (K.hasLaw i i.2).variance_eq_of_expMeasure (choose_two_pos i.2)

/-! ### Watterson's estimator -/

variable {m : MeasurableSpace Ω} {S : Ω → ℝ} {θ : ℝ}

/-- Infinite-sites mutation at rate `θ/2` per lineage per unit time: if the number of
segregating sites `S` is integrable and has conditional mean `(θ/2) L` given the genealogy
σ-algebra `m`, then `E S = θ H_{n-1}`. (Integrability matters: Mathlib's conditional
expectation of a non-integrable function is `0`.) -/
theorem integral_segSites (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)] (hSi : Integrable S μ)
    (hS : μ[S | m] =ᵐ[μ] fun ω => θ / 2 * K.totalLength ω) :
    μ[S] = θ * (harmonic (n - 1) : ℝ) := by
  have h := setIntegral_condExp hm hSi (MeasurableSet.univ : MeasurableSet[m] Set.univ)
  simp only [Measure.restrict_univ] at h
  rw [← h, integral_congr_ae hS, integral_const_mul, K.integral_totalLength]
  ring

/-- Watterson's estimator `S / H_{n-1}` is integrable when `S` is. -/
theorem integrable_watterson (hSi : Integrable S μ) :
    Integrable (fun ω => S ω / (harmonic (n - 1) : ℝ)) μ :=
  hSi.div_const _

/-- **Watterson's estimator is unbiased**: `E[S / H_{n-1}] = θ` for a sample of size
`n ≥ 2`. -/
theorem watterson_unbiased (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)] (hSi : Integrable S μ)
    (hS : μ[S | m] =ᵐ[μ] fun ω => θ / 2 * K.totalLength ω) (hn : 2 ≤ n) :
    μ[fun ω => S ω / (harmonic (n - 1) : ℝ)] = θ := by
  have hH : (harmonic (n - 1) : ℝ) ≠ 0 := by
    exact_mod_cast (harmonic_pos (by omega)).ne'
  rw [integral_div, K.integral_segSites hm hSi hS]
  field_simp

end KingmanTimes

/-! ### A concrete model -/

/-- The canonical probability space for the Kingman holding times of a sample of size `n`:
the product of the exponential laws `Exp (k.choose 2)`, `2 ≤ k ≤ n`. -/
def piMeasure (n : ℕ) : Measure (Icc 2 n → ℝ) :=
  Measure.pi fun k : Icc 2 n => expMeasure ((k : ℕ).choose 2 : ℕ)

/-- The exponential factors of `piMeasure n` are probability measures. -/
instance (n : ℕ) (k : Icc 2 n) :
    IsProbabilityMeasure (expMeasure (((k : ℕ).choose 2 : ℕ) : ℝ)) :=
  isProbabilityMeasure_expMeasure (KingmanTimes.choose_two_pos k.2)

/-- The coordinate projections of `piMeasure n` form a Kingman coalescent; in particular
`KingmanTimes` is inhabited for every sample size. -/
def KingmanTimes.ofPi (n : ℕ) : KingmanTimes (piMeasure n) n where
  T k ω := if h : k ∈ Icc 2 n then ω ⟨k, h⟩ else 0
  hasLaw k hk := by
    have hT : (fun ω : Icc 2 n → ℝ => if h : k ∈ Icc 2 n then ω ⟨k, h⟩ else 0)
        = fun ω => ω ⟨k, hk⟩ := by
      funext ω
      simp [hk]
    rw [hT]
    exact (measurePreserving_eval (fun i : Icc 2 n => expMeasure (((i : ℕ).choose 2 : ℕ) : ℝ))
      ⟨k, hk⟩).hasLaw
  indep := by
    have hT : (fun k : Icc 2 n => fun ω : Icc 2 n → ℝ =>
        if h : (k : ℕ) ∈ Icc 2 n then ω ⟨k, h⟩ else 0) = fun k ω => id (ω k) := by
      funext k ω
      simp [k.2]
    rw [hT]
    exact iIndepFun_pi (μ := fun i : Icc 2 n => expMeasure (((i : ℕ).choose 2 : ℕ) : ℝ))
      (fun _ => aemeasurable_id)

/-! ### Wright–Fisher → Kingman -/

/-- In a Wright–Fisher population of `M` gene copies, the probability that `k` lineages,
choosing their parents independently and uniformly, have `k` distinct parents. -/
def noCoalProb (M k : ℕ) : ℝ := ∏ i ∈ range k, (1 - (i : ℝ) / M)

/-- `noCoalProb M k` is the falling factorial `M (M-1) ⋯ (M-k+1)` divided by `M ^ k`. -/
theorem noCoalProb_eq_descFactorial_div {M : ℕ} (hM : 0 < M) (k : ℕ) :
    noCoalProb M k = (M.descFactorial k : ℝ) / (M : ℝ) ^ k := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  induction k with
  | zero => simp [noCoalProb]
  | succ k ih =>
    rw [noCoalProb, prod_range_succ, ← noCoalProb, ih, Nat.descFactorial_succ]
    by_cases hk : k ≤ M
    · rw [Nat.cast_mul, Nat.cast_sub hk]
      field_simp
      ring
    · have h0 : M.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
      simp [h0]

/-- `noCoalProb M k → 1` as `M → ∞`. -/
theorem tendsto_noCoalProb_one (k : ℕ) :
    Tendsto (fun M : ℕ => noCoalProb M k) atTop (𝓝 1) := by
  have h : Tendsto (fun M : ℕ => ∏ i ∈ range k, (1 - (i : ℝ) / M)) atTop
      (𝓝 (∏ _i ∈ range k, (1 - 0 : ℝ))) :=
    tendsto_finsetProd _ fun i _ =>
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (i : ℝ))
  simpa [noCoalProb] using h

/-- **Kingman's coalescence rate.** For `M` gene copies (`M = 2N`), the per-generation
probability that some of `k` lineages coalesce is `(k.choose 2) / M + o(1/M)`; i.e. in time
units of `M` generations, coalescences occur at rate `k.choose 2`. -/
theorem tendsto_coalescence_rate (k : ℕ) :
    Tendsto (fun M : ℕ => (M : ℝ) * (1 - noCoalProb M k)) atTop (𝓝 (k.choose 2 : ℕ)) := by
  induction k with
  | zero => simp [noCoalProb]
  | succ k ih =>
    have hlim : Tendsto (fun M : ℕ => (M : ℝ) * (1 - noCoalProb M k) + k * noCoalProb M k)
        atTop (𝓝 ((k.choose 2 : ℕ) + k * 1)) :=
      ih.add ((tendsto_noCoalProb_one k).const_mul _)
    have heq : ((k + 1).choose 2 : ℕ) = ((k.choose 2 : ℕ) : ℝ) + k * 1 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
      push_cast
      ring
    rw [heq]
    refine hlim.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with M hM
    have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM
    simp only [noCoalProb, prod_range_succ]
    field_simp
    ring

/-- After `⌊t M⌋` Wright–Fisher generations (`t ≥ 0` coalescent time units), the probability
that `k` lineages have not coalesced tends to `exp (-(k.choose 2) t)`, the survival function
of the exponential law with rate `k.choose 2`. -/
theorem tendsto_noCoalProb_pow_floor (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun M : ℕ => noCoalProb M k ^ ⌊t * M⌋₊) atTop
      (𝓝 (Real.exp (-((k.choose 2 : ℕ) : ℝ) * t))) := by
  have hg : Tendsto (fun M : ℕ => (M : ℝ) * (noCoalProb M k - 1)) atTop
      (𝓝 (-((k.choose 2 : ℕ) : ℝ))) := by
    refine (tendsto_coalescence_rate k).neg.congr fun M => ?_
    ring
  have hlog := Real.tendsto_nat_mul_log_one_add_of_tendsto hg
  have hfl : Tendsto (fun M : ℕ => (⌊t * M⌋₊ : ℝ) / M) atTop (𝓝 t) :=
    (tendsto_nat_floor_mul_div_atTop ht).comp tendsto_natCast_atTop_atTop
  have hprod := (hfl.mul hlog).rexp
  rw [mul_comm t] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ne_atTop 0,
    (tendsto_noCoalProb_one k).eventually (lt_mem_nhds one_pos)] with M hM hpos
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  simp only [add_sub_cancel]
  rw [show (⌊t * M⌋₊ : ℝ) / M * (M * Real.log (noCoalProb M k))
      = ⌊t * M⌋₊ * Real.log (noCoalProb M k) by field_simp,
    Real.exp_nat_mul, Real.exp_log hpos]

end MathlibExt.Biology.PopulationGenetics.Coalescent
