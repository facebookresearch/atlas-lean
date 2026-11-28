/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Streaming.MorrisCounter
public import MathlibExt.Probability.MedianOfMeans
public import MathlibExt.Probability.MonteCarloRate
public import Mathlib.Data.Nat.Log

/-!
# Bounded Morris counters and median-of-means amplification

A block contains `k` independent registers. We saturate each register at a level `h` with
`2 ^ h ≥ 2 k (m + 1)`. If the uncapped block mean is good, no register in it could have
exceeded `h`: that one nonnegative summand alone would have made the mean too high.
Thus clipping costs no extra failure probability. This is a block argument, not a union
bound over an unbounded number of copies. Independent blocks are combined by a median.

Source: A. Chakrabarti, *Data Stream Algorithms*, Dartmouth College, July 1, 2025,
Unit 4, Lemma 4.4.1 and Theorem 4.4.2 (p. 23). The notes discuss aborting beyond
`2 log m` and obtain an additive `o(1)` term. Here the cap depends on the block width;
when that width exceeds the horizon, one may instead count exactly.

Space bounds below count persistent register configurations, not temporary arithmetic,
the source of random bits, or workspace for computing the readout.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability MathlibExt.Probability.MedianOfMeans

namespace Cslib.Algorithms.Lean.MorrisCounter

/-- A bounded counter only uses its own finite state to process a token. At the upper
endpoint both branches coincide, making it absorbing. -/
noncomputable def boundedStep (h : ℕ) : Kernel (Fin (h + 1)) (Fin (h + 1)) :=
  Kernel.ofFunOfCountable fun x => bernoulliMeasure (Fin.clamp (x.val + 1) h) x (incrementProb x)

/-- The bounded law is coupled to the true register by saturation. -/
noncomputable def boundedLaw (h n : ℕ) : Measure (Fin (h + 1)) :=
  (law n).map fun x : Fin (n + 1) => Fin.clamp x h

instance (h n : ℕ) : IsProbabilityMeasure (boundedLaw h n) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_of_finite _).aemeasurable).mpr inferInstance

/-- The bounded implementation also starts at zero, for every cap (including zero). -/
theorem boundedLaw_zero (h : ℕ) : boundedLaw h 0 = Measure.dirac 0 := by
  rw [boundedLaw, law, Measure.map_dirac' (measurable_of_finite _)]
  congr 1

/-- Clipping is an online implementation: the clipped marginal evolves by `boundedStep`,
without access to the underlying unbounded register. -/
theorem boundedLaw_succ (h n : ℕ) : boundedLaw h (n + 1) = boundedStep h ∘ₘ boundedLaw h n := by
  unfold boundedLaw
  rw [law, Measure.map_bind (step n).aemeasurable (measurable_of_finite _).aemeasurable,
    Measure.bind_map (measurable_of_finite _).aemeasurable (boundedStep h).aemeasurable]
  congr 1
  funext x
  change (bernoulliMeasure x.succ x.castSucc _).map _ =
    bernoulliMeasure (Fin.clamp ((Fin.clamp x h).val + 1) h) (Fin.clamp x h) _
  rw [map_bernoulliMeasure]
  by_cases hx : x.val ≤ h
  · simp [min_eq_left hx]
  · have h₁ : Fin.clamp (x.val + 1) h = Fin.clamp x h := Fin.ext (by simp; omega)
    have h₂ : Fin.clamp ((Fin.clamp x h).val + 1) h = Fin.clamp x h := Fin.ext (by simp; omega)
    simp only [Fin.val_succ, Fin.val_castSucc, h₁, h₂, bernoulliMeasure_self_eq_dirac]

/-- The arithmetic mean of the estimates in one block. -/
noncomputable def blockMean {k l : ℕ} (x : Fin k → Fin l) : ℝ :=
  (∑ i, (value (x i) - 1)) / k

private noncomputable abbrev block (k : ℕ) {l : ℕ} (ν : Measure (Fin l)) :=
  Measure.pi fun _ : Fin k => ν

private abbrev target (n : ℕ) (ε : ℝ) := Set.Icc ((1 - ε) * n) ((1 + ε) * n)

private lemma block_failure {n k : ℕ} {ε : ℝ} (hε : 0 < ε) (hk : 4 / ε ^ 2 ≤ k) :
    (block k (law n)).real {x | blockMean x ∉ target n ε} ≤ 1 / 8 := by
  have hkR : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) hk
  have hkN : 0 < k := by exact_mod_cast hkR
  let : Nonempty (Fin k) := ⟨⟨0, hkN⟩⟩
  rcases n with _ | n
  · have hz (x : Fin k → Fin 1) : blockMean x = 0 := by simp [blockMean, value, Fin.val_eq_zero]
    simp [target, hz]
  let N := n + 1
  have hN : (0 : ℝ) < N := by dsimp [N]; positivity
  let X (i : Fin k) (x : Fin k → Fin (N + 1)) := value (x i) - 1
  let μ := block k (law N)
  have hL (i : Fin k) : HasLaw (Function.eval i) (law N) μ :=
    ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
  have hM (i : Fin k) : ∫ x, X i x ∂μ = N :=
    ((hL i).integral_comp (f := fun x => value x - 1)
      (measurable_of_finite _).aestronglyMeasurable).trans (integral_estimate N)
  have hV (i : Fin k) : Var[X i; μ] = N * ((N : ℝ) - 1) / 2 := by
    calc Var[X i; μ] = Var[fun y => value y - 1; law N] :=
           (measurePreserving_eval (fun _ : Fin k => law N) i).variance_fun_comp
             (f := fun y : Fin (N + 1) => value y - 1) (measurable_of_finite _).aemeasurable
      _ = _ := by
        rw [variance_sub_const (measurable_of_finite _).aestronglyMeasurable, variance_value]
  have hI : iIndepFun X μ := iIndepFun_pi (X := fun _ x => value x - 1)
    fun _ => (measurable_of_finite _).aemeasurable
  have hMean : ∫ x, blockMean x ∂μ = N := by
    change (∫ x, (∑ i, X i x) / (k : ℝ) ∂μ) = _
    simpa only [Fintype.card_fin] using integral_sample_mean
      (fun i => (Integrable.of_finite : Integrable (X i) μ)) hM
  have hVar : Var[blockMean; μ] = N * ((N : ℝ) - 1) / 2 / k := by
    change Var[fun x => (∑ i, X i x) / (k : ℝ); μ] = _
    simpa only [Fintype.card_fin] using variance_sample_mean (fun i =>
      (memLp_two_iff_integrable_sq (measurable_of_finite (X i)).aestronglyMeasurable).2
        Integrable.of_finite) hI hV
  have hCheb := meas_ge_le_variance_div_sq (μ := μ) (X := blockMean)
    ((memLp_two_iff_integrable_sq (measurable_of_finite _).aestronglyMeasurable).2
      Integrable.of_finite) (mul_pos hε hN)
  rw [hMean, hVar] at hCheb
  have hsub : {x : Fin k → Fin (N + 1) | blockMean x ∉ target N ε} ⊆
      {x | ε * N ≤ |blockMean x - N|} := by
    intro x hx
    change ε * N ≤ |blockMean x - N|
    by_contra! hh
    rcases abs_lt.mp hh with ⟨h₁, h₂⟩
    exact hx ⟨by linarith, by linarith⟩
  refine (measureReal_mono (μ := μ) hsub).trans ((ENNReal.toReal_le_of_le_ofReal ?_ hCheb).trans ?_)
  · rw [← hVar]; exact div_nonneg (variance_nonneg _ _) (sq_nonneg _)
  · rw [div_le_iff₀ (by positivity), div_le_iff₀ hkR]
    have hscale := (div_le_iff₀ (sq_pos_of_pos hε)).mp hk
    nlinarith [mul_le_mul_of_nonneg_right hscale (sq_nonneg (N : ℝ))]

/-- A cap chosen for a whole block, not just for a single copy. -/
def cap (k m : ℕ) : ℕ := 1 + Nat.clog 2 k + Nat.clog 2 (m + 1)

private lemma le_pow_cap (k m : ℕ) : 2 * k * (m + 1) ≤ 2 ^ cap k m := by
  simp only [cap, pow_add, pow_one]
  gcongr <;> exact Nat.le_pow_clog (by decide) _

private lemma good_not_clipped {k n m : ℕ} (hn : n ≤ m) {ε : ℝ} (hε : ε ≤ 1)
    (x : Fin k → Fin (n + 1)) (hg : blockMean x ∈ target n ε) (i : Fin k) :
    (x i).val ≤ cap k m := by
  by_contra! hx
  have hs := Finset.single_le_sum (f := fun j => value (x j) - 1)
    (fun j _ => sub_nonneg.mpr (one_le_pow₀ (by norm_num))) (Finset.mem_univ i)
  have hk : (0 : ℝ) < k := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hsum := (div_le_iff₀ hk).mp hg.2
  have hpow : (2 : ℝ) ^ cap k m < value (x i) := pow_lt_pow_right₀ (by norm_num) hx
  have hcap : 2 * (k : ℝ) * (m + 1) ≤ (2 : ℝ) ^ cap k m := by exact_mod_cast le_pow_cap k m
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.succ_le_of_lt (Nat.zero_lt_of_lt i.isLt)
  have hnR : (n : ℝ) ≤ m := by exact_mod_cast hn
  nlinarith [mul_nonneg (sub_nonneg.mpr hε) (mul_nonneg (Nat.cast_nonneg n) hk.le),
    mul_nonneg (sub_nonneg.mpr hnR) hk.le]

private lemma bounded_block_failure {k n m : ℕ} (hn : n ≤ m) {ε : ℝ} (hε : 0 < ε)
    (hε' : ε ≤ 1) (hk : 4 / ε ^ 2 ≤ k) :
    (block k (boundedLaw (cap k m) n)).real {x | blockMean x ∉ target n ε} ≤ 1 / 8 := by
  let c : Fin (n + 1) → Fin (cap k m + 1) := fun x => Fin.clamp x (cap k m)
  have hm := Measure.pi_map_pi (μ := fun _ : Fin k => law n) (f := fun _ => c)
    (fun _ => (measurable_of_finite c).aemeasurable)
  change (Measure.pi fun _ : Fin k => (law n).map c).real _ ≤ _
  rw [← hm, map_measureReal_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
  refine (measureReal_mono ?_).trans (block_failure hε hk (n := n))
  intro x hx hg
  apply hx
  have heq (i : Fin k) : value (c (x i)) = value (x i) := by
    simp [value, c, min_eq_left (good_not_clipped hn hε' x hg i)]
  simpa only [blockMean, heq] using hg

/-- Number of independent counters in each block. -/
noncomputable def width (ε : ℝ) : ℕ := ⌈4 / ε ^ 2⌉₊

/-- Number of independent blocks. Ceilings allow arbitrary `0 < δ < 1`. -/
noncomputable def groups (δ : ℝ) : ℕ := ⌈32 / 9 * Real.log δ⁻¹⌉₊

/-- Fix a stream length `n ≤ m`, a relative error `0 < ε ≤ 1`, and `0 < δ`. Use
`k = ⌈4 / ε²⌉₊` counters per block and `s = ⌈(32/9) ln(1/δ)⌉₊` blocks, where `⌈·⌉₊` rounds
up to a nonnegative integer. Each register saturates at `h = 1 + ⌈log₂ k⌉ + ⌈log₂ (m + 1)⌉`.
Under the product law of `s` independent blocks, each with `k` independent registers of law
`boundedLaw h n`, the probability that the median of the block means of `2 ^ x - 1` lies
outside the closed interval `[(1 - ε)n, (1 + ε)n]` is at most `δ`. -/
theorem median_failure {m n : ℕ} (hn : n ≤ m) {ε δ : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1)
    (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin (groups δ) => Measure.pi fun _ : Fin (width ε) =>
      boundedLaw (cap (width ε) m) n).real
      {x | sampleMedian (fun j => blockMean (x j)) ∉ Set.Icc ((1 - ε) * n) ((1 + ε) * n)} ≤ δ := by
  let ν := block (width ε) (boundedLaw (cap (width ε) m) n)
  have h := measureReal_sampleMedian_notMem_Icc_le
    (iIndepFun_pi (μ := fun _ : Fin (groups δ) => ν) (X := fun _ => blockMean)
      fun _ => (measurable_of_finite _).aemeasurable)
    (fun _ => measurable_of_finite _)
    (fun i => ((show HasLaw (Function.eval i) ν (Measure.pi fun _ : Fin (groups δ) => ν) from
      ⟨(measurable_pi_apply _).aemeasurable, (measurePreserving_eval _ _).map_eq⟩).measureReal_eq
        (p := fun x => blockMean x ∉ target n ε) (Set.toFinite _).measurableSet).le.trans
          (bounded_block_failure hn hε hε' (Nat.le_ceil _)))
  refine h.trans ((Real.le_log_iff_exp_le hδ).mp ?_)
  have hg : 32 / 9 * Real.log δ⁻¹ ≤ groups δ := Nat.le_ceil _
  rw [Real.log_inv] at hg
  linarith

/-- For `0 < ε` and `0 < δ < 1`, both the block width `k = ⌈4 / ε²⌉₊` and the number of
blocks `s = ⌈(32/9) ln(1/δ)⌉₊` are positive. Rounding up adds less than one in each case:
`k < 4 / ε² + 1` and `s < (32/9) ln(1/δ) + 1`. -/
theorem repetition_counts {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ' : δ < 1) :
    0 < width ε ∧ (width ε : ℝ) < 4 / ε ^ 2 + 1 ∧
    0 < groups δ ∧ (groups δ : ℝ) < 32 / 9 * Real.log δ⁻¹ + 1 := by
  have h₁ : 0 < 4 / ε ^ 2 := by positivity
  have h₂ : 0 < 32 / 9 * Real.log δ⁻¹ := by
    have := Real.log_pos (one_lt_inv_iff₀.mpr ⟨hδ, hδ'⟩)
    positivity
  exact ⟨Nat.one_le_ceil_iff.mpr h₁, Nat.ceil_lt_add_one h₁.le,
    Nat.one_le_ceil_iff.mpr h₂, Nat.ceil_lt_add_one h₂.le⟩

/-- A padded, double-logarithmic number of bits for one register when `k ≤ m + 1`.
In particular it is defined and positive even for `m = 0`. -/
def registerBits (m : ℕ) : ℕ := 1 + Nat.clog 2 (Nat.clog 2 (m + 1) + 1)

/-- When the block width is at most `m + 1`, all persistent bounded register arrays fit
in `s * k * registerBits m` bits: their number is at most two to that power. -/
theorem registerArray_card_le {k m : ℕ} (hk : k ≤ m + 1) (s : ℕ) :
    Fintype.card (Fin s → Fin k → Fin (cap k m + 1)) ≤ 2 ^ (s * k * registerBits m) := by
  have hc := Nat.clog_mono_right 2 hk
  have hb := Nat.le_pow_clog (b := 2) (by decide) (Nat.clog 2 (m + 1) + 1)
  have h : cap k m + 1 ≤ 2 ^ registerBits m := by
    simp only [cap, registerBits, pow_add, pow_one]
    omega
  simp only [Fintype.card_fun, Fintype.card_fin, ← pow_mul]
  calc (cap k m + 1) ^ (k * s) ≤ (2 ^ registerBits m) ^ (k * s) := Nat.pow_le_pow_left h _
    _ = 2 ^ (s * k * registerBits m) := by rw [← pow_mul]; congr 1; ring

/-- For a short horizon relative to the requested precision, an exact counter is cheaper.
It starts at zero and saturates at the promised upper bound. -/
def exactCounter (m : ℕ) : ℕ → Fin (m + 1)
  | 0 => 0
  | n + 1 => Fin.clamp ((exactCounter m n).val + 1) m

/-- The short-horizon fallback is exact throughout the promised range. -/
theorem exactCounter_val {n m : ℕ} (hn : n ≤ m) : (exactCounter m n).val = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [exactCounter, ih (by omega), min_eq_left hn]

/-- Suppose `m + 1 < k` and there are `s > 0` blocks of `k` counters each. The exact fallback
counter has `m + 1` possible states, and their number is at most `2 ^ (s * k * registerBits m)`.
Here `registerBits m = 1 + ⌈log₂ (1 + ⌈log₂ (m + 1)⌉)⌉` is the padded bit allowance per
scheduled register. The bound counts persistent states, not temporary or readout storage. -/
theorem exactCounter_card_le {k m s : ℕ} (hk : m + 1 < k) (hs : 0 < s) :
    Fintype.card (Fin (m + 1)) ≤ 2 ^ (s * k * registerBits m) := by
  have h₁ : k ≤ s * k := by simpa using Nat.mul_le_mul_right k hs
  have h₂ : s * k ≤ s * k * registerBits m := by
    simpa using Nat.mul_le_mul_left (s * k) (show 1 ≤ registerBits m by unfold registerBits; omega)
  rw [Fintype.card_fin]
  exact (hk.le.trans (h₁.trans h₂)).trans Nat.lt_two_pow_self.le

end Cslib.Algorithms.Lean.MorrisCounter
