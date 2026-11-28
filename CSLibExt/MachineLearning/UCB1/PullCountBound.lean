/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.MachineLearning.UCB1.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic
import Mathlib.NumberTheory.ZetaValues
import MathlibExt.Probability.HoeffdingBounded

/-!
# The pull-count bound for UCB1

This module proves the bound on the number of plays of a suboptimal arm by UCB1
(`CSLibExt.MachineLearning.UCB1.Basic`) of Theorem 1 of P. Auer, N. Cesa-Bianchi and
P. Fischer, *Finite-time analysis of the multiarmed bandit problem*, Machine Learning 47 (2002)
235–256, for the expectation of the number of plays when the run's plays are measurable, and
extends it, with the same constant, to the lower Lebesgue integral of that number for every run.
The rewards come from reward stacks: the `m`-th play of arm `j` (counted from `0`) yields the
reward `X j m`.

## Main results

* `integral_count_le`: if the stack entries are independent and those of arm `j` have law `ν j`
  supported in `[0, 1]`, then for every run of UCB1 whose plays are measurable, such as
  `ucb1Arm`, every arm `i` with gap `Δ_i > 0` and every `n`, the expected number `T_i(n)` of
  plays of `i` among the first `n` plays is at most `8 ln n / Δ_i² + 1 + π² / 3`. This is
  Theorem 1 of the paper, in the form its proof gives for each arm.
* `lintegral_count_le`: an extension proved here with the same constant. For every run of UCB1,
  measurable or not, the lower Lebesgue integral of `T_i(n)` is at most the same bound;
  `integral_count_le` follows from it.

## Proof outline

Following the paper, let `c_{t,s} = √(2 ln t / s)`, let `x̄_{j,s}` be the mean of the first `s`
entries of arm `j`'s stack, let `a` be an arm of largest mean and `ℓ = max 1 ⌈8 ln n / Δ_i²⌉`.

* On every path, arm `i` is played at most `ℓ` times, plus once for each play of `i` made after
  `t ≥ K` plays of which at least `ℓ` were plays of `i`. Such a play maximizes the index, so
  `x̄_{a,s} + c_{t,s} ≤ x̄_{i,s'} + c_{t,s'}` with `s ∈ [1, t]` and `s' ∈ [ℓ, t]` the play counts
  of `a` and `i`. The count of `i` is therefore at most `ℓ` plus the number of triples
  `(t, s, s')` with `t < n` satisfying this inequality.
* For `s' ≥ ℓ` and `t < n`, `2 c_{t,s'} ≤ Δ_i`, so the inequality implies
  `x̄_{a,s} ≤ μ_a - c_{t,s}` or `x̄_{i,s'} ≥ μ_i + c_{t,s'}`. By Hoeffding's inequality
  (`measureReal_avg_sub_le_neg_le` and `measureReal_avg_sub_ge_le`), each has probability at most
  `exp (-4 ln t) = t⁻⁴`.
* Summing, the integral of this pathwise bound is at most
  `ℓ + ∑_{t < n} t² · 2 t⁻⁴ ≤ ℓ + 2 ζ(2) = ℓ + π² / 3`, and `ℓ ≤ 8 ln n / Δ_i² + 1`. The lower
  integral of the count is at most the integral of the pathwise bound, by monotonicity.

## Implementation notes

* The sums over `t` stop at `n - 1`, where `ln t ≤ ln n`, so that the paper's third event
  `μ* < μ_i + 2 c_{t,s'}` fails for `s' ≥ ℓ`; the paper's display (6) writes the sum over all
  `t ≥ 1`.
* The theorems assume the paper's model: independent rewards, identically distributed for each
  arm, with values in `[0, 1]`. Of these assumptions the proof uses the range, the independence of
  the rewards of each arm and their common mean, not the independence across arms or the
  identical distribution.
* A positive gap needs `K ≥ 2` arms, and the bound holds for every `n`, so neither is a
  hypothesis.
* `lintegral_count_le` uses the lower Lebesgue integral `∫⁻`, which is defined for every function
  into `[0, ∞]` and is monotone without measurability, so it holds for every run, including runs
  whose initial order or tie-breaking depends on the outcome in a non-measurable way. When the
  plays are measurable, as for `ucb1Arm` (`measurable_ucb1Arm`), `T_i(n)` is a random variable
  and `integral_count_le` states the bound for its expectation, the Bochner integral.
-/

@[expose] public section

namespace Cslib.MachineLearning.UCB1

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

variable {K : ℕ}

/-! ### A path of a UCB1 run -/

/-- The empirical mean of the first `s` rewards of arm `j`. -/
private noncomputable def empMean (x : Fin K → ℕ → ℝ) (j : Fin K) (s : ℕ) : ℝ :=
  (∑ m ∈ range s, x j m) / s

/-- The exploration bonus `√(2 ln t / s)`. -/
private noncomputable def bonus (t s : ℕ) : ℝ := √(2 * log t / s)

private lemma ucb1Index_eq (x : Fin K → ℕ → ℝ) (t : ℕ) (c : Fin K → ℕ) (j : Fin K) :
    ucb1Index x t c j = empMean x j (c j) + bonus t (c j) := rfl

variable {x : Fin K → ℕ → ℝ} {A : ℕ → Fin K}

private lemma IsUCB1Run.count_le_one (hA : IsUCB1Run x A) (j : Fin K) {t : ℕ} (ht : t ≤ K) :
    Nat.count (A · = j) t ≤ 1 :=
  (Nat.count_monotone _ ht).trans (hA.1 j).le

private lemma IsUCB1Run.one_le_count (hA : IsUCB1Run x A) (j : Fin K) {t : ℕ} (ht : K ≤ t) :
    1 ≤ Nat.count (A · = j) t :=
  (hA.1 j).ge.trans (Nat.count_monotone _ ht)

/-- The first step of the proof: arm `i` is played at most `ℓ` times, plus once for each play of
`i` made after `t ≥ K` plays of which at least `ℓ` were plays of `i`. -/
private lemma IsUCB1Run.count_le (hA : IsUCB1Run x A) (i : Fin K) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (n : ℕ) :
    Nat.count (A · = i) n ≤
      ℓ + ∑ t ∈ range n, if K ≤ t ∧ A t = i ∧ ℓ ≤ Nat.count (A · = i) t then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.count_succ, sum_range_succ]
    by_cases hn : A n = i
    · by_cases hK : K ≤ n
      · by_cases hl : ℓ ≤ Nat.count (A · = i) n
        · simp only [hn, hK, hl, and_self, ite_true]
          omega
        · simp only [hn, hl, and_false, ite_true, ite_false]
          omega
      · have h1 := hA.count_le_one i (t := n + 1) (by omega)
        rw [Nat.count_succ] at h1
        simp only [hn, ite_true] at h1 ⊢
        omega
    · simp only [hn, false_and, and_false, ite_false]
      omega

/-- On a path, the pull count of arm `i` after `n` plays is at most `ℓ` plus the number of
triples `(t, s, s')`, with `t < n`, `1 ≤ s ≤ t` and `ℓ ≤ s' ≤ t`, for which the empirical mean of
the first `s` rewards of a reference arm `a` lies at least `bonus t s` below `μa`, or that of the
first `s'` rewards of `i` lies at least `bonus t s'` above `μi`, provided `2 bonus t s' ≤ μa - μi`
for all such triples. -/
private lemma IsUCB1Run.count_le_sum (hA : IsUCB1Run x A) (a i : Fin K) {μa μi : ℝ} {ℓ n : ℕ}
    (hℓ : 1 ≤ ℓ) (hgap : ∀ t ∈ range n, ∀ s ∈ Icc ℓ t, 2 * bonus t s ≤ μa - μi) :
    (Nat.count (A · = i) n : ℝ) ≤ ℓ + ∑ t ∈ range n, ∑ s ∈ Icc 1 t, ∑ s' ∈ Icc ℓ t,
      ((if empMean x a s ≤ μa - bonus t s then 1 else 0) +
        (if μi + bonus t s' ≤ empMean x i s' then 1 else 0) : ℝ) := by
  have key := hA.count_le i hℓ n
  have hcast : (Nat.count (A · = i) n : ℝ) ≤ ℓ + ∑ t ∈ range n,
      ((if K ≤ t ∧ A t = i ∧ ℓ ≤ Nat.count (A · = i) t then 1 else 0 : ℕ) : ℝ) := by
    exact_mod_cast key
  refine hcast.trans (add_le_add_right (sum_le_sum fun t ht ↦ ?_) _)
  split_ifs with hcond
  swap
  · simp only [Nat.cast_zero]
    refine sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ add_nonneg ?_ ?_ <;> split_ifs <;> norm_num
  obtain ⟨hK, hAt, hl⟩ := hcond
  set s₀ := Nat.count (A · = a) t
  set s₁ := Nat.count (A · = i) t
  have hs₀ : s₀ ∈ Icc 1 t := mem_Icc.mpr ⟨hA.one_le_count a hK, Nat.count_le _⟩
  have hs₁ : s₁ ∈ Icc ℓ t := mem_Icc.mpr ⟨hl, Nat.count_le _⟩
  have hidx := hA.2 t hK a
  rw [hAt, ucb1Index_eq, ucb1Index_eq] at hidx
  have hterm : (1 : ℝ) ≤ (if empMean x a s₀ ≤ μa - bonus t s₀ then 1 else 0) +
      (if μi + bonus t s₁ ≤ empMean x i s₁ then 1 else 0) := by
    have hg := hgap t ht s₁ hs₁
    by_cases h7 : empMean x a s₀ ≤ μa - bonus t s₀
    · rw [ite_eq_left h7]
      split_ifs <;> norm_num
    · by_cases h8 : μi + bonus t s₁ ≤ empMean x i s₁
      · simp [h7, h8]
      · exfalso
        linarith [not_le.mp h7, not_le.mp h8]
  have hnn : ∀ s s', (0 : ℝ) ≤ (if empMean x a s ≤ μa - bonus t s then 1 else 0) +
      (if μi + bonus t s' ≤ empMean x i s' then 1 else 0) := fun s s' ↦ by
    split_ifs <;> norm_num
  calc ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
    _ ≤ _ := hterm
    _ ≤ ∑ s' ∈ Icc ℓ t, ((if empMean x a s₀ ≤ μa - bonus t s₀ then 1 else 0) +
        (if μi + bonus t s' ≤ empMean x i s' then 1 else 0) : ℝ) :=
      single_le_sum (f := fun s' ↦ ((if empMean x a s₀ ≤ μa - bonus t s₀ then 1 else 0) +
        (if μi + bonus t s' ≤ empMean x i s' then 1 else 0) : ℝ)) (fun s' _ ↦ hnn _ _) hs₁
    _ ≤ _ := single_le_sum (f := fun s ↦ ∑ s' ∈ Icc ℓ t,
        ((if empMean x a s ≤ μa - bonus t s then 1 else 0) +
          (if μi + bonus t s' ≤ empMean x i s' then 1 else 0) : ℝ))
        (fun s _ ↦ sum_nonneg fun s' _ ↦ hnn _ _) hs₀

/-! ### Concentration of the empirical means -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
private lemma avg_eq {Y : ℕ → Ω → ℝ} {μ : ℝ} (hmean : ∀ m, P[Y m] = μ) {s : ℕ} (hs : 1 ≤ s)
    (ω : Ω) : (1 / s : ℝ) * ∑ k : Fin s, Y k ω - (1 / s : ℝ) * ∑ k : Fin s, P[Y k] =
      (∑ m ∈ range s, Y m ω) / s - μ := by
  have hs' : (s : ℝ) ≠ 0 := by positivity
  simp only [hmean, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.sum_range (fun m ↦ Y m ω)]
  field_simp

/-- Hoeffding's lower tail for the empirical mean of the first `s` terms of an independent
sequence with values in `[0, 1]` and common mean `μ`. -/
private lemma measureReal_empMean_le {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y P)
    (hmeas : ∀ m, Measurable (Y m)) (hrange : ∀ m, ∀ᵐ ω ∂P, Y m ω ∈ Set.Icc (0 : ℝ) 1) {μ : ℝ}
    (hmean : ∀ m, P[Y m] = μ) {s : ℕ} (hs : 1 ≤ s) {c : ℝ} (hc : 0 ≤ c) :
    P.real {ω | (∑ m ∈ range s, Y m ω) / s ≤ μ - c} ≤ exp (-2 * s * c ^ 2) := by
  have h := MathlibExt.Probability.HoeffdingBounded.measureReal_avg_sub_le_neg_le
    (Z := fun k : Fin s ↦ Y k) (hind.precomp Fin.val_injective)
    (fun k ↦ (hmeas k).aemeasurable) (fun k ↦ hrange k) hc
  simp only [avg_eq hmean hs, sub_zero, one_pow, div_one] at h
  refine le_of_eq_of_le (congrArg P.real (Set.ext fun ω ↦ ?_)) h
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

/-- Hoeffding's upper tail for the empirical mean of the first `s` terms of an independent
sequence with values in `[0, 1]` and common mean `μ`. -/
private lemma measureReal_le_empMean {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y P)
    (hmeas : ∀ m, Measurable (Y m)) (hrange : ∀ m, ∀ᵐ ω ∂P, Y m ω ∈ Set.Icc (0 : ℝ) 1) {μ : ℝ}
    (hmean : ∀ m, P[Y m] = μ) {s : ℕ} (hs : 1 ≤ s) {c : ℝ} (hc : 0 ≤ c) :
    P.real {ω | μ + c ≤ (∑ m ∈ range s, Y m ω) / s} ≤ exp (-2 * s * c ^ 2) := by
  have h := MathlibExt.Probability.HoeffdingBounded.measureReal_avg_sub_ge_le
    (Z := fun k : Fin s ↦ Y k) (hind.precomp Fin.val_injective)
    (fun k ↦ (hmeas k).aemeasurable) (fun k ↦ hrange k) hc
  simp only [avg_eq hmean hs, sub_zero, one_pow, div_one] at h
  refine le_of_eq_of_le (congrArg P.real (Set.ext fun ω ↦ ?_)) h
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

/-- With the bonus `√(2 ln t / s)`, Hoeffding's bound `exp (-2 s c²)` is `t⁻⁴`. -/
private lemma exp_bonus {t s : ℕ} (ht : 1 ≤ t) (hs : 1 ≤ s) :
    exp (-2 * s * bonus t s ^ 2) = 1 / (t : ℝ) ^ 4 := by
  have hs' : (s : ℝ) ≠ 0 := by positivity
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  rw [bonus, sq_sqrt (by positivity)]
  have : -2 * (s : ℝ) * (2 * log t / s) = -((4 : ℕ) * log t) := by
    field_simp
    push_cast
    ring
  rw [this, exp_neg, exp_nat_mul, exp_log ht', one_div]

/-! ### The pull-count bound -/

/-- **Pull-count bound for every run of UCB1**: the bound of Theorem 1 of Auer, Cesa-Bianchi and
Fischer, with the same constant, for the lower Lebesgue integral of the number of plays, which
extends it to runs that need not be measurable. Let the rewards form reward stacks: the `m`-th
play of arm `j` (counted from `0`) yields `X j m`, the rewards `X j m` are independent, and those
of arm `j` have a law `ν j` supported in `[0, 1]`, with mean `μ j = ∫ r, r ∂ν j`; let
`μ* = ⨆ j, μ j`. Let `A` be a run of UCB1 on these stacks (`IsUCB1Run`: its first `K` plays may
come in any order, and ties may be broken in any way, which may also depend on the outcome `ω`),
and let `T_i(n)` be the number of plays of an arm `i` among the first `n` plays. If the gap
`Δ i = μ* - μ i` is positive, which needs `K ≥ 2` arms, then for every `n` the lower Lebesgue
integral of `T_i(n)`, the supremum of the integrals of the measurable simple functions below it,
is at most `8 ln n / Δ i ^ 2 + 1 + π ^ 2 / 3` (for `n = 0`, with `log 0 = 0`).

The lower integral needs no measurability of the run, and it is the expectation of `T_i(n)` when
`T_i(n)` is measurable (`integral_count_le`). Runs need not be measurable: with two arms paying
the constant rewards `1` and `0`, a run may play arm `1` first on a non-measurable event and arm
`0` first elsewhere, then the other arm, and then always the least maximizer; the number of plays
of arm `1` in the first play is then the indicator of that event, and only this form of the
bound applies to it.

Source: P. Auer, N. Cesa-Bianchi and P. Fischer, *Finite-time analysis of the multiarmed bandit
problem*, Machine Learning 47 (2002) 235–256, Figure 1 and the proof of Theorem 1. -/
theorem lintegral_count_le {X : Fin K → ℕ → Ω → ℝ} {ν : Fin K → Measure ℝ}
    (hmeas : ∀ j m, Measurable (X j m)) (hindep : iIndepFun (fun p : Fin K × ℕ ↦ X p.1 p.2) P)
    (hlaw : ∀ j m, P.map (X j m) = ν j) (hsupp : ∀ j, ∀ᵐ r ∂ν j, r ∈ Set.Icc (0 : ℝ) 1)
    {A : Ω → ℕ → Fin K} (hA : ∀ ω, IsUCB1Run (fun j m ↦ X j m ω) (A ω)) {i : Fin K}
    (hΔ : 0 < (⨆ j, ∫ r, r ∂ν j) - ∫ r, r ∂ν i) (n : ℕ) :
    ∫⁻ ω, (Nat.count (A ω · = i) n : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal (8 * log n / ((⨆ j, ∫ r, r ∂ν j) - ∫ r, r ∂ν i) ^ 2 + 1 + π ^ 2 / 3) := by
  set μ : Fin K → ℝ := fun j ↦ ∫ r, r ∂ν j with hμ
  set Δ := (⨆ j, μ j) - μ i with hΔdef
  have : Nonempty (Fin K) := ⟨i⟩
  obtain ⟨a, ha⟩ := exists_eq_ciSup_of_finite (f := μ)
  -- The model's facts about one arm.
  have hind : ∀ j, iIndepFun (X j) P := fun j ↦
    hindep.precomp (g := fun m : ℕ ↦ (j, m)) fun m m' h ↦ (Prod.mk.inj h).2
  have hrange : ∀ j m, ∀ᵐ ω ∂P, X j m ω ∈ Set.Icc (0 : ℝ) 1 := fun j m ↦
    (ae_map_iff (hmeas j m).aemeasurable measurableSet_Icc).mp (hlaw j m ▸ hsupp j)
  have hmean : ∀ j m, P[X j m] = μ j := fun j m ↦ by
    change ∫ ω, X j m ω ∂P = ∫ r, r ∂ν j
    rw [← hlaw j m, integral_map (f := fun r : ℝ ↦ r) (hmeas j m).aemeasurable
      aestronglyMeasurable_id]
  -- The threshold `ℓ`.
  set ℓ : ℕ := max 1 ⌈8 * log n / Δ ^ 2⌉₊ with hℓdef
  have hlogn : 0 ≤ log n := log_natCast_nonneg n
  have hℓ1 : 1 ≤ ℓ := le_max_left _ _
  have hℓge : 8 * log n / Δ ^ 2 ≤ ℓ :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  have h8 : 0 ≤ 8 * log n / Δ ^ 2 := by positivity
  have hℓle : (ℓ : ℝ) ≤ 8 * log n / Δ ^ 2 + 1 := by
    rw [hℓdef, Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith) (Nat.ceil_lt_add_one h8).le
  -- Condition (9) of the paper fails beyond the threshold.
  have hgap : ∀ t ∈ range n, ∀ s ∈ Icc ℓ t, 2 * bonus t s ≤ μ a - μ i := by
    intro t ht s hs
    rw [mem_range] at ht
    obtain ⟨hs1, hst⟩ := mem_Icc.mp hs
    have hspos : (0 : ℝ) < s := by exact_mod_cast hℓ1.trans hs1
    have htpos : (0 : ℝ) < t := by exact_mod_cast (hℓ1.trans hs1).trans hst
    have hlogt : log t ≤ log n := log_le_log htpos (by exact_mod_cast ht.le)
    have hsΔ : 8 * log n ≤ s * Δ ^ 2 := by
      have := hℓge.trans (by exact_mod_cast hs1 : (ℓ : ℝ) ≤ s)
      rwa [div_le_iff₀ (by positivity)] at this
    rw [ha, ← hΔdef]
    have h2 : 2 * bonus t s = √(8 * log t / s) := by
      rw [bonus, show (8 : ℝ) * log t / s = 2 ^ 2 * (2 * log t / s) by ring,
        sqrt_mul (by positivity), sqrt_sq (by norm_num)]
    rw [h2, ← sqrt_sq hΔ.le]
    refine sqrt_le_sqrt ?_
    rw [div_le_iff₀ hspos]
    nlinarith
  -- The events of the paper's (7) and (8).
  set E₇ : ℕ → ℕ → Set Ω := fun t s ↦
    {ω | (∑ m ∈ range s, X a m ω) / s ≤ μ a - bonus t s} with hE₇
  set E₈ : ℕ → ℕ → Set Ω := fun t s ↦
    {ω | μ i + bonus t s ≤ (∑ m ∈ range s, X i m ω) / s} with hE₈
  have hmeasSum : ∀ j s, Measurable fun ω ↦ (∑ m ∈ range s, X j m ω) / s := fun j s ↦
    (Finset.measurable_fun_sum _ fun m _ ↦ hmeas j m).div_const _
  have hE₇m : ∀ t s, MeasurableSet (E₇ t s) := fun t s ↦
    measurableSet_le (hmeasSum a s) measurable_const
  have hE₈m : ∀ t s, MeasurableSet (E₈ t s) := fun t s ↦
    measurableSet_le measurable_const (hmeasSum i s)
  set F : Ω → ℝ := fun ω ↦ ℓ + ∑ t ∈ range n, ∑ s ∈ Icc 1 t, ∑ s' ∈ Icc ℓ t,
    ((E₇ t s).indicator 1 ω + (E₈ t s').indicator 1 ω) with hF
  have hI₇ : ∀ t s, Integrable ((E₇ t s).indicator (1 : Ω → ℝ)) P := fun t s ↦
    (integrable_const (1 : ℝ)).indicator (hE₇m t s)
  have hI₈ : ∀ t s, Integrable ((E₈ t s).indicator (1 : Ω → ℝ)) P := fun t s ↦
    (integrable_const (1 : ℝ)).indicator (hE₈m t s)
  have hint : ∀ t s s', Integrable (fun ω ↦ (E₇ t s).indicator (1 : Ω → ℝ) ω +
      (E₈ t s').indicator 1 ω) P := fun t s s' ↦ (hI₇ t s).add (hI₈ t s')
  have hFint : Integrable F P :=
    (integrable_const _).add (integrable_finsetSum _ fun t _ ↦ integrable_finsetSum _ fun s _ ↦
      integrable_finsetSum _ fun s' _ ↦ hint t s s')
  -- The pathwise bound.
  have hpath : ∀ ω, (Nat.count (A ω · = i) n : ℝ) ≤ F ω := by
    intro ω
    refine ((hA ω).count_le_sum a i (μa := μ a) (μi := μ i) hℓ1 hgap).trans_eq ?_
    simp only [hF, empMean, Set.indicator_apply, Pi.one_apply, hE₇, hE₈, Set.mem_ofPred_eq]
  have hFeq : ∫ ω, F ω ∂P = ℓ + ∑ t ∈ range n, ∑ s ∈ Icc 1 t, ∑ s' ∈ Icc ℓ t,
      (P.real (E₇ t s) + P.real (E₈ t s')) := by
    rw [hF, integral_add (integrable_const _) (integrable_finsetSum _ fun t _ ↦
      integrable_finsetSum _ fun s _ ↦ integrable_finsetSum _ fun s' _ ↦ hint t s s'),
      integral_const, probReal_univ, one_smul]
    congr 1
    rw [integral_finsetSum _ fun t _ ↦ integrable_finsetSum _ fun s _ ↦
      integrable_finsetSum _ fun s' _ ↦ hint t s s']
    refine sum_congr rfl fun t _ ↦ ?_
    rw [integral_finsetSum _ fun s _ ↦ integrable_finsetSum _ fun s' _ ↦ hint t s s']
    refine sum_congr rfl fun s _ ↦ ?_
    rw [integral_finsetSum _ fun s' _ ↦ hint t s s']
    refine sum_congr rfl fun s' _ ↦ ?_
    rw [integral_add (hI₇ t s) (hI₈ t s'), integral_indicator_one (hE₇m t s),
      integral_indicator_one (hE₈m t s')]
  -- Each event has probability at most `t⁻⁴`.
  have hprob : ∀ t ∈ range n, ∀ s ∈ Icc 1 t, ∀ s' ∈ Icc ℓ t,
      P.real (E₇ t s) + P.real (E₈ t s') ≤ 2 * (1 / (t : ℝ) ^ 4) := by
    intro t _ s hs s' hs'
    obtain ⟨hs1, hst⟩ := mem_Icc.mp hs
    obtain ⟨hs'1, hs't⟩ := mem_Icc.mp hs'
    have ht1 : 1 ≤ t := hs1.trans hst
    have h7 := measureReal_empMean_le (hind a) (hmeas a) (hrange a) (hmean a) hs1
      (c := bonus t s) (sqrt_nonneg _)
    have h8 := measureReal_le_empMean (hind i) (hmeas i) (hrange i) (hmean i) (hℓ1.trans hs'1)
      (c := bonus t s') (sqrt_nonneg _)
    rw [exp_bonus ht1 hs1] at h7
    rw [exp_bonus ht1 (hℓ1.trans hs'1)] at h8
    linarith
  -- Summing: at most `t² · 2 t⁻⁴ = 2 t⁻²` for each `t`.
  have hsum : ∑ t ∈ range n, ∑ s ∈ Icc 1 t, ∑ s' ∈ Icc ℓ t,
      (P.real (E₇ t s) + P.real (E₈ t s')) ≤ π ^ 2 / 3 := by
    calc _ ≤ ∑ t ∈ range n, ∑ s ∈ Icc 1 t, ∑ s' ∈ Icc ℓ t, 2 * (1 / (t : ℝ) ^ 4) :=
          sum_le_sum fun t ht ↦ sum_le_sum fun s hs ↦ sum_le_sum fun s' hs' ↦
            hprob t ht s hs s' hs'
      _ ≤ ∑ t ∈ range n, 2 * (1 / (t : ℝ) ^ 2) := by
          refine sum_le_sum fun t _ ↦ ?_
          simp only [sum_const, Nat.card_Icc, nsmul_eq_mul]
          rcases Nat.eq_zero_or_pos t with rfl | ht
          · simp
          have htR : (0 : ℝ) < t := by exact_mod_cast ht
          have hc : ((t + 1 - ℓ : ℕ) : ℝ) ≤ t := by exact_mod_cast (by omega : t + 1 - ℓ ≤ t)
          have hc' : ((t + 1 - 1 : ℕ) : ℝ) = t := by simp
          rw [hc']
          calc (t : ℝ) * (((t + 1 - ℓ : ℕ) : ℝ) * (2 * (1 / (t : ℝ) ^ 4)))
              ≤ t * (t * (2 * (1 / (t : ℝ) ^ 4))) := by gcongr
            _ = 2 * (1 / (t : ℝ) ^ 2) := by field_simp
      _ = 2 * ∑ t ∈ range n, 1 / (t : ℝ) ^ 2 := by rw [mul_sum]
      _ ≤ 2 * (π ^ 2 / 6) := by
          gcongr
          exact sum_le_hasSum _ (fun t _ ↦ by positivity) hasSum_zeta_two
      _ = π ^ 2 / 3 := by ring
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω ↦ (Nat.cast_nonneg _).trans (hpath ω)
  calc ∫⁻ ω, (Nat.count (A ω · = i) n : ℝ≥0∞) ∂P ≤ ∫⁻ ω, ENNReal.ofReal (F ω) ∂P :=
        lintegral_mono fun ω ↦ by
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal (hpath ω)
    _ = ENNReal.ofReal (∫ ω, F ω ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hFint (Filter.Eventually.of_forall hF0)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by rw [hFeq]; linarith [hℓle, hsum])

/-- **Pull-count bound for UCB1** (P. Auer, N. Cesa-Bianchi and P. Fischer, *Finite-time analysis
of the multiarmed bandit problem*, Machine Learning 47 (2002), Theorem 1 and its proof). Let the
rewards form reward stacks: the `m`-th play of arm `j` (counted from `0`) yields `X j m`, the
rewards `X j m` are independent, and those of arm `j` have a law `ν j` supported in `[0, 1]`, with
mean `μ j = ∫ r, r ∂ν j`; let `μ* = ⨆ j, μ j`. Let `A` be a run of UCB1 on these stacks
(`IsUCB1Run`: its first `K` plays may come in any order, and ties may be broken in any way) whose
plays `A · t` are measurable, and let `T_i(n)` be the number of plays of an arm `i` among the
first `n` plays, a random variable. If the gap `Δ i = μ* - μ i` is positive, which needs `K ≥ 2`
arms, then for every `n` the expectation of `T_i(n)` is at most `8 ln n / Δ i ^ 2 + 1 + π ^ 2 / 3`
(for `n = 0`, with `log 0 = 0`). The plays are measurable for instance for `ucb1Arm`, which plays
the arms in index order first and then the least maximizer, on measurable reward stacks
(`measurable_ucb1Arm`). -/
theorem integral_count_le {X : Fin K → ℕ → Ω → ℝ} {ν : Fin K → Measure ℝ}
    (hmeas : ∀ j m, Measurable (X j m)) (hindep : iIndepFun (fun p : Fin K × ℕ ↦ X p.1 p.2) P)
    (hlaw : ∀ j m, P.map (X j m) = ν j) (hsupp : ∀ j, ∀ᵐ r ∂ν j, r ∈ Set.Icc (0 : ℝ) 1)
    {A : Ω → ℕ → Fin K} (hA : ∀ ω, IsUCB1Run (fun j m ↦ X j m ω) (A ω))
    (hAm : ∀ t, Measurable fun ω ↦ A ω t) {i : Fin K}
    (hΔ : 0 < (⨆ j, ∫ r, r ∂ν j) - ∫ r, r ∂ν i) (n : ℕ) :
    ∫ ω, (Nat.count (A ω · = i) n : ℝ) ∂P ≤
      8 * log n / ((⨆ j, ∫ r, r ∂ν j) - ∫ r, r ∂ν i) ^ 2 + 1 + π ^ 2 / 3 := by
  have hcount : Measurable fun ω ↦ Nat.count (A ω · = i) n := by
    simp only [Nat.count_eq_card_filter_range, card_filter]
    exact Finset.measurable_sum _ fun u _ ↦
      Measurable.ite (measurableSet_eq_fun (hAm u) measurable_const) measurable_const
        measurable_const
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω ↦ Nat.cast_nonneg _)
    (measurable_from_top.comp hcount).aestronglyMeasurable]
  simp only [ENNReal.ofReal_natCast]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity)
    (lintegral_count_le hmeas hindep hlaw hsupp hA hΔ n)

end Cslib.MachineLearning.UCB1
