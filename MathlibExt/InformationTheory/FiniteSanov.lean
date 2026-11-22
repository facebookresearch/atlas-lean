/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.MethodOfTypes
public import MathlibExt.InformationTheory.FiniteEntropy
public import MathlibExt.Probability.SampleEmpiricalMeasure

/-!
# Sanov's theorem for finite alphabets, via types

Csiszár, "The method of types", IEEE Trans. Inform. Theory 44 (1998), Theorem III.3: for a set
`Γ` of distributions on a finite alphabet and an i.i.d. sample from `Q`, the probability that the
empirical distribution lies in `Γ` is at most `(n + 1)^{|α|} exp(-n D(Γ ‖ Q))`, and it is at least
`(n + 1)^{-|α|} exp(-n D(P ‖ Q))` for every `n`-type `P ∈ Γ`. Hence `(1/n) log Pr → -D(Γ ‖ Q)`
under condition (III.21), `D(Γ ∩ 𝒫ₙ ‖ Q) → D(Γ ‖ Q)`, a condition on large `n` only.

* `iidProb_empirical_mem_eq_sum`: the event is the union of the type classes of the types in `Γ`
  (equation (III.24));
* `iidProb_empirical_mem_le`, `exp_le_pow_mul_iidProb_empirical_mem`: the two bounds of (III.25);
* `eventually_iidProb_empirical_mem_le`: the upper bound (III.20), in exponential form;
* `tendsto_log_iidProb_empirical_mem_div`: the limit (III.22).

The divergence bound is passed as a number `r` with `r ≤ D(P ‖ Q)` for every probability vector
`P ∈ Γ` with `P ≪ Q`; this is `r ≤ D(Γ ‖ Q) = inf_{P ∈ Γ} D(P ‖ Q)` over the distributions in `Γ`,
with the source's convention `D = ∞` off `P ≪ Q`, and avoids an infimum of real-valued junk
divergences. Condition (III.21) is passed as a sequence of `n`-types `s n`, eventually in `Γ`
with `P̂_{s n} ≪ Q`, whose divergences tend to `r`. When `D(Γ ‖ Q) < ∞` this is equivalent to
(III.21): each `Γ ∩ 𝒫ₙ` is finite, so a minimiser can be chosen for every large `n`. The case
`D(Γ ‖ Q) = ∞` is covered by the upper bound only.

The last section relates the types of this file to the repository's empirical measure
(`sampleEmpiricalMeasure`, used by the general Sanov theorem) and to its entropy in bits.
-/

@[expose] public section

namespace MathlibExt.InformationTheory.MethodOfTypes

open Finset Real Filter Topology

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

/-- **The Sanov event as a union of type classes** (Csiszár, "The method of types", IEEE Trans.
Inform. Theory 44 (1998), equation (III.24)). The probability that the empirical distribution of
`n` draws lies in `Γ` is the sum of `Qⁿ(T_s)` over the `n`-types `s` whose empirical distribution
lies in `Γ`. -/
theorem iidProb_empirical_mem_eq_sum (Q : α → ℝ) (Γ : Set (α → ℝ)) [DecidablePred (· ∈ Γ)] :
    iidProb Q (univ.filter fun x : Fin n → α => empirical (seqType x) ∈ Γ) =
      ∑ s ∈ univ.filter (fun s : Sym α n => empirical s ∈ Γ), iidProb Q (typeClass s) := by
  unfold iidProb
  rw [← Finset.sum_fiberwise_of_maps_to (g := seqType)
    (t := univ.filter fun s : Sym α n => empirical s ∈ Γ) (fun x hx => by simpa using hx)]
  refine Finset.sum_congr rfl fun s hs => ?_
  congr 1
  ext x
  simp only [typeClass, mem_filter, mem_univ, true_and] at hs ⊢
  exact ⟨fun h => h.2, fun h => ⟨h ▸ hs, h⟩⟩

/-- **Sanov's upper bound, non-asymptotic** (Csiszár, "The method of types", IEEE Trans. Inform.
Theory 44 (1998), right half of (III.25), with Lemma II.1). Let `Q ≥ 0` on a finite alphabet, `Γ`
any set of functions `α → ℝ`, and `r` a number with `r ≤ ∑ₐ P(a) log (P(a) / Q(a))` for every
probability vector `P ∈ Γ` such that `Q(a) > 0` wherever `P(a) > 0` (that is, `r` is at most the
divergence from `Q` of the distributions in `Γ`). Then for `n ≥ 1`, the
probability that the empirical distribution of `n` independent draws from `Q` lies in `Γ` is at
most `(n + 1)^{|α|} exp(-n r)`. No topological hypothesis on `Γ` is needed. -/
theorem iidProb_empirical_mem_le (hn : n ≠ 0) {Q : α → ℝ} (hQ : ∀ a, 0 ≤ Q a)
    (Γ : Set (α → ℝ)) [DecidablePred (· ∈ Γ)] {r : ℝ}
    (hr : ∀ P ∈ Γ, (∀ a, 0 ≤ P a) → ∑ a, P a = 1 → (∀ a, 0 < P a → 0 < Q a) →
      r ≤ ∑ a, P a * log (P a / Q a)) :
    iidProb Q (univ.filter fun x : Fin n → α => empirical (seqType x) ∈ Γ) ≤
      ((n : ℝ) + 1) ^ Fintype.card α * exp (-(n : ℝ) * r) := by
  rw [iidProb_empirical_mem_eq_sum]
  have hterm : ∀ s : Sym α n, empirical s ∈ Γ → iidProb Q (typeClass s) ≤ exp (-(n : ℝ) * r) := by
    intro s hs
    by_cases hsupp : ∀ a, 0 < empirical s a → 0 < Q a
    · refine (iidProb_typeClass_le_exp hn s hQ).trans (exp_le_exp.mpr ?_)
      have := hr _ hs (empirical_nonneg s) (sum_empirical hn s) hsupp
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    · push Not at hsupp
      obtain ⟨a, ha, hQa⟩ := hsupp
      rw [iidProb_typeClass_eq_zero s ((empirical_pos_iff hn s a).mp ha)
        (le_antisymm hQa (hQ a))]
      exact (exp_pos _).le
  calc ∑ s ∈ univ.filter (fun s : Sym α n => empirical s ∈ Γ), iidProb Q (typeClass s)
      ≤ ∑ _s ∈ univ.filter (fun s : Sym α n => empirical s ∈ Γ), exp (-(n : ℝ) * r) :=
        Finset.sum_le_sum fun s hs => hterm s (by simpa using hs)
    _ ≤ ∑ _s : Sym α n, exp (-(n : ℝ) * r) :=
        Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => (exp_pos _).le
    _ = Fintype.card (Sym α n) * exp (-(n : ℝ) * r) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ((n : ℝ) + 1) ^ Fintype.card α * exp (-(n : ℝ) * r) := by
        refine mul_le_mul_of_nonneg_right ?_ (exp_pos _).le
        exact_mod_cast card_sym_le_pow

/-- **Sanov's lower bound, non-asymptotic** (Csiszár, "The method of types", IEEE Trans. Inform.
Theory 44 (1998), left half of (III.25), with Lemma II.1). If the empirical distribution `P` of an
`n`-type `s` (`n ≥ 1`) lies in `Γ` and `Q(a) > 0` wherever `P(a) > 0`, then
`exp(-n D(P ‖ Q)) ≤ (n + 1)^{|α|} · Pr(empirical distribution ∈ Γ)`. -/
theorem exp_le_pow_mul_iidProb_empirical_mem (hn : n ≠ 0) {Q : α → ℝ} (hQ0 : ∀ a, 0 ≤ Q a)
    {Γ : Set (α → ℝ)} [DecidablePred (· ∈ Γ)] (s : Sym α n) (hs : empirical s ∈ Γ)
    (hQ : ∀ a, 0 < empirical s a → 0 < Q a) :
    exp (-(n : ℝ) * ∑ a, empirical s a * log (empirical s a / Q a)) ≤
      ((n : ℝ) + 1) ^ Fintype.card α *
        iidProb Q (univ.filter fun x : Fin n → α => empirical (seqType x) ∈ Γ) := by
  refine (exp_le_pow_mul_iidProb_typeClass hn s hQ0 hQ).trans
    (mul_le_mul_of_nonneg_left (iidProb_mono hQ0 fun x hx => ?_) (by positivity))
  rw [mem_typeClass] at hx
  simpa [hx] using hs

omit [DecidableEq α] in
/-- **The number of types is subexponential.** For `ε > 0`, eventually `(n + 1)^{|α|} ≤ exp(n ε)`,
the step that makes the polynomial factors of Lemma II.1 negligible in Theorem III.3 (Csiszár,
"The method of types", IEEE Trans. Inform. Theory 44 (1998), Section III). -/
theorem eventually_pow_card_le_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) ^ Fintype.card α ≤ exp (n * ε) := by
  set k := Fintype.card α
  rcases Nat.eq_zero_or_pos k with hk | hk
  · refine Eventually.of_forall fun n => ?_
    rw [hk, pow_zero]
    exact one_le_exp (by positivity)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlim : Tendsto (fun x : ℝ => log x ^ 1 / (1 * x + (-1))) atTop (𝓝 0) :=
    tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
  have hseq : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hev := (hlim.comp hseq).eventually (gt_mem_nhds (div_pos hε hkR))
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  simp only [Function.comp_apply, pow_one, one_mul] at hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hden : (n : ℝ) + 1 + -1 = n := by ring
  rw [hden, div_lt_div_iff₀ hnR hkR] at hn
  rw [← exp_log (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ k), log_pow]
  exact exp_le_exp.mpr (by linarith)

/-- **Sanov's upper bound, asymptotic form** (Csiszár, "The method of types", IEEE Trans. Inform.
Theory 44 (1998), Theorem III.3, (III.20)). Under the hypotheses of `iidProb_empirical_mem_le`, for
every `ε > 0`, eventually `Pr(empirical distribution of n draws ∈ Γ) ≤ exp(-n (r - ε))`. This is
`limsup (1/n) log Pr ≤ -r` stated without the junk value `log 0 = 0`. -/
theorem eventually_iidProb_empirical_mem_le {Q : α → ℝ} (hQ : ∀ a, 0 ≤ Q a)
    (Γ : Set (α → ℝ)) [DecidablePred (· ∈ Γ)] {r : ℝ}
    (hr : ∀ P ∈ Γ, (∀ a, 0 ≤ P a) → ∑ a, P a = 1 → (∀ a, 0 < P a → 0 < Q a) →
      r ≤ ∑ a, P a * log (P a / Q a))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      iidProb Q (univ.filter fun x : Fin n → α => empirical (seqType x) ∈ Γ) ≤
        exp (-(n : ℝ) * (r - ε)) := by
  filter_upwards [eventually_pow_card_le_exp (α := α) hε, eventually_gt_atTop 0] with n hpow hn
  refine (iidProb_empirical_mem_le hn.ne' hQ Γ hr).trans ?_
  calc ((n : ℝ) + 1) ^ Fintype.card α * exp (-(n : ℝ) * r)
      ≤ exp (n * ε) * exp (-(n : ℝ) * r) := mul_le_mul_of_nonneg_right hpow (exp_pos _).le
    _ = exp (-(n : ℝ) * (r - ε)) := by rw [← exp_add]; ring_nf

/-- **Sanov's lower bound, asymptotic form** (Csiszár, "The method of types", IEEE Trans. Inform.
Theory 44 (1998), Theorem III.3, lower half of (III.22)). Let `s n` be an `n`-type, and suppose
that for all large `n` it lies in `Γ` with `Q(a) > 0` wherever its empirical distribution is
positive, and that `D(P̂_{s n} ‖ Q) → r`. Then for every `ε > 0`, eventually
`exp(-n (r + ε)) ≤ Pr(empirical distribution of n draws ∈ Γ)`. -/
theorem eventually_exp_le_iidProb_empirical_mem {Q : α → ℝ} (hQ0 : ∀ a, 0 ≤ Q a)
    {Γ : Set (α → ℝ)} [DecidablePred (· ∈ Γ)] {r : ℝ} (s : ∀ n : ℕ, Sym α n)
    (hs : ∀ᶠ n in atTop, empirical (s n) ∈ Γ)
    (hQ : ∀ᶠ n in atTop, ∀ a, 0 < empirical (s n) a → 0 < Q a)
    (hlim : Tendsto (fun n => ∑ a, empirical (s n) a * log (empirical (s n) a / Q a))
      atTop (𝓝 r)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      exp (-(n : ℝ) * (r + ε)) ≤
        iidProb Q (univ.filter fun x : Fin n → α => empirical (seqType x) ∈ Γ) := by
  have hε2 : 0 < ε / 2 := half_pos hε
  filter_upwards [eventually_pow_card_le_exp (α := α) hε2, eventually_gt_atTop 0,
    hlim.eventually (gt_mem_nhds (show r < r + ε / 2 by linarith)), hs, hQ]
    with n hpow hn hD hsn hQn
  have hlow := exp_le_pow_mul_iidProb_empirical_mem hn.ne' hQ0 (s n) hsn hQn
  set D := ∑ a, empirical (s n) a * log (empirical (s n) a / Q a)
  set p := iidProb Q (univ.filter fun x : Fin n → α => empirical (seqType x) ∈ Γ)
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : 0 ≤ p := iidProb_nonneg hQ0 _
  have h1 : exp (-(n : ℝ) * (r + ε)) * exp (n * (ε / 2)) ≤ exp (-(n : ℝ) * D) := by
    rw [← exp_add]; exact exp_le_exp.mpr (by nlinarith)
  have h2 : exp (-(n : ℝ) * (r + ε)) * exp (n * (ε / 2)) ≤ exp (n * (ε / 2)) * p :=
    h1.trans (hlow.trans (mul_le_mul_of_nonneg_right hpow hp))
  rw [mul_comm] at h2
  exact le_of_mul_le_mul_left h2 (exp_pos _)

/-- **Sanov's theorem for finite alphabets** (Csiszár, "The method of types", IEEE Trans. Inform.
Theory 44 (1998), Theorem III.3, (III.22); Csiszár–Shields, *Information Theory and Statistics: A
Tutorial*, 2004, Theorem 2.1). Let `Q ≥ 0` on a finite alphabet and `Γ` a set of functions `α → ℝ`.
Suppose `r ≤ D(P ‖ Q)` for every probability vector `P ∈ Γ` with `P ≪ Q`, and that there are
`n`-types `s n`, in `Γ` with `P̂_{s n} ≪ Q` for all large `n`, such that `D(P̂_{s n} ‖ Q) → r`. Then
`r = D(Γ ‖ Q)` over the distributions in `Γ`, and the hypothesis is condition (III.21) (equivalent
to it when `D(Γ ‖ Q) < ∞`). Then `(1/n) log Pr(empirical distribution of n draws ∈ Γ) → -r`, natural
logarithm. -/
theorem tendsto_log_iidProb_empirical_mem_div {Q : α → ℝ} (hQ0 : ∀ a, 0 ≤ Q a)
    {Γ : Set (α → ℝ)} [DecidablePred (· ∈ Γ)] {r : ℝ}
    (hr : ∀ P ∈ Γ, (∀ a, 0 ≤ P a) → ∑ a, P a = 1 → (∀ a, 0 < P a → 0 < Q a) →
      r ≤ ∑ a, P a * log (P a / Q a))
    (s : ∀ n : ℕ, Sym α n) (hs : ∀ᶠ n in atTop, empirical (s n) ∈ Γ)
    (hQ : ∀ᶠ n in atTop, ∀ a, 0 < empirical (s n) a → 0 < Q a)
    (hlim : Tendsto (fun n => ∑ a, empirical (s n) a * log (empirical (s n) a / Q a))
      atTop (𝓝 r)) :
    Tendsto (fun n : ℕ =>
      log (iidProb Q (univ.filter fun x : Fin n → α => empirical (seqType x) ∈ Γ)) / n)
      atTop (𝓝 (-r)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (((eventually_iidProb_empirical_mem_le hQ0 Γ hr hε2).and
      (eventually_exp_le_iidProb_empirical_mem hQ0 s hs hQ hlim hε2)).and
        (eventually_gt_atTop 0))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨⟨hup, hlo⟩, hn0⟩ := hN n hn
  set p := iidProb Q (univ.filter fun x : Fin n → α => empirical (seqType x) ∈ Γ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hp : 0 < p := (exp_pos _).trans_le hlo
  have hlog_up : log p ≤ -(n : ℝ) * (r - ε / 2) := by
    rw [← log_exp (-(n : ℝ) * (r - ε / 2))]; exact log_le_log hp hup
  have hlog_lo : -(n : ℝ) * (r + ε / 2) ≤ log p := by
    rw [← log_exp (-(n : ℝ) * (r + ε / 2))]; exact log_le_log (exp_pos _) hlo
  rw [Real.dist_eq, abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hnR]; nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hnR]; nlinarith

/-! ### Bridges to the repository's empirical measure and entropy -/

omit [Fintype α] in
/-- **Empirical distribution of a type agrees with the empirical measure.** For a sample
`x₀, x₁, …` in a finite alphabet with measurable singletons and `n ≥ 1`, the empirical
distribution of the type of `(x₀, …, x_{n-1})` gives `a` the same mass as the repository's
`sampleEmpiricalMeasure x n` (Varadhan, *Large Deviations*, NYU lecture notes, 2010, Section 3;
Csiszár, "The method of types", IEEE Trans. Inform. Theory 44 (1998), Section II). -/
theorem empirical_seqType_eq_sampleEmpiricalMeasure [MeasurableSpace α]
    [MeasurableSingletonClass α] (x : ℕ → α) (hn : n ≠ 0) (a : α) :
    empirical (seqType fun i : Fin n => x i) a =
      ((MathlibExt.Probability.SampleEmpiricalMeasure.sampleEmpiricalMeasure x n :
        MeasureTheory.ProbabilityMeasure α) : MeasureTheory.Measure α).real {a} := by
  classical
  rw [MeasureTheory.measureReal_def,
    MathlibExt.Probability.SampleEmpiricalMeasure.sampleEmpiricalMeasure_apply x hn
      (measurableSet_singleton a)]
  have hcard : Fintype.card {i : Fin n // x i = a} =
      ((range n).filter fun i => x i ∈ ({a} : Set α)).card := by
    rw [Fintype.card_subtype]
    refine Finset.card_bij (fun (i : Fin n) _ => (i : ℕ)) (fun i hi => ?_) (fun i _ j _ h =>
      Fin.ext h) (fun j hj => ?_)
    · simp only [mem_filter, mem_univ, true_and] at hi
      simp [hi]
    · simp only [mem_filter, mem_range, Set.mem_singleton_iff] at hj
      exact ⟨⟨j, hj.1⟩, by simpa using hj.2, rfl⟩
  rw [empirical, count_seqType, hcard, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, inv_mul_eq_div]
  congr

omit [DecidableEq α] in
/-- **Entropy in nats and the repository's entropy in bits.** For a probability mass function `p`
on a finite alphabet, `∑ₐ -p(a) log p(a) = shannonEntropy p · log 2`: the natural-log entropy used
in this file is the repository's base-two `shannonEntropy` times `log 2` (Csiszár, "The method of
types", IEEE Trans. Inform. Theory 44 (1998), Section II, allows any base). -/
theorem sum_negMulLog_eq_shannonEntropy_mul_log_two (p : PMF α) :
    ∑ a, negMulLog (p a).toReal = _root_.InformationTheory.shannonEntropy p * log 2 := by
  rw [_root_.InformationTheory.shannonEntropy,
    div_mul_cancel₀ _ (log_pos one_lt_two).ne']

end MathlibExt.InformationTheory.MethodOfTypes
