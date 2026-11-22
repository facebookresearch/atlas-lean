/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence

/-! This file constructs bisection sequences on real intervals and proves that their midpoints
converge to a bracketed root with the standard geometric error bound. -/

@[expose] public section

namespace MetaMathlibExt

/-- `u` and `v` are the bracketing endpoints produced by the bisection algorithm:
at each step their midpoint replaces the endpoint having the same sign. -/
def IsBisectionSequence (f : ℝ → ℝ) (a b : ℝ) (u v : ℕ → ℝ) : Prop :=
  u 0 = a ∧ v 0 = b ∧ ∀ n,
    let m := (u n + v n) / 2
    (f m ≤ 0 ∧ u (n + 1) = m ∧ v (n + 1) = v n) ∨
      (0 ≤ f m ∧ u (n + 1) = u n ∧ v (n + 1) = m)

private theorem bisection_step_order
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (huv : IsBisectionSequence f a b u v) (n : ℕ) (huvn : u n ≤ v n) :
    u n ≤ u (n + 1) ∧ u (n + 1) ≤ v (n + 1) ∧ v (n + 1) ≤ v n := by
  rcases huv.2.2 n with h | h
  · rcases h with ⟨-, hu, hv⟩
    rw [hu, hv]
    exact ⟨by linarith, by linarith, le_rfl⟩
  · rcases h with ⟨-, hu, hv⟩
    rw [hu, hv]
    exact ⟨le_rfl, by linarith, by linarith⟩

private theorem bisection_le_and_le
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (hab : a ≤ b) (huv : IsBisectionSequence f a b u v) :
    ∀ n, a ≤ u n ∧ u n ≤ v n ∧ v n ≤ b := by
  intro n
  induction n with
  | zero =>
      simp only [huv.1, huv.2.1]
      exact ⟨le_rfl, hab, le_rfl⟩
  | succ n ih =>
      obtain ⟨huu, huv', hvv⟩ := bisection_step_order huv n ih.2.1
      exact ⟨ih.1.trans huu, huv', hvv.trans ih.2.2⟩

private theorem bisection_step_signs
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (huv : IsBisectionSequence f a b u v) (n : ℕ)
    (hfu : f (u n) ≤ 0) (hfv : 0 ≤ f (v n)) :
    f (u (n + 1)) ≤ 0 ∧ 0 ≤ f (v (n + 1)) := by
  rcases huv.2.2 n with h | h
  · rcases h with ⟨hfm, hu, hv⟩
    rw [hu, hv]
    exact ⟨hfm, hfv⟩
  · rcases h with ⟨hfm, hu, hv⟩
    rw [hu, hv]
    exact ⟨hfu, hfm⟩

private theorem bisection_invariants
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (hab : a ≤ b) (ha : f a ≤ 0) (hb : 0 ≤ f b)
    (huv : IsBisectionSequence f a b u v) :
    ∀ n, a ≤ u n ∧ u n ≤ v n ∧ v n ≤ b ∧ f (u n) ≤ 0 ∧ 0 ≤ f (v n) := by
  intro n
  induction n with
  | zero =>
      simp only [huv.1, huv.2.1]
      exact ⟨le_rfl, hab, le_rfl, ha, hb⟩
  | succ n ih =>
      obtain ⟨huu, huv', hvv⟩ := bisection_step_order huv n ih.2.1
      obtain ⟨hfu, hfv⟩ := bisection_step_signs huv n ih.2.2.2.1 ih.2.2.2.2
      exact ⟨ih.1.trans huu, huv', hvv.trans ih.2.2.1, hfu, hfv⟩

private theorem bisection_nesting
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (hab : a ≤ b) (huv : IsBisectionSequence f a b u v) :
    ∀ n, u n ≤ u (n + 1) ∧ u (n + 1) ≤ v (n + 1) ∧ v (n + 1) ≤ v n := by
  intro n
  exact bisection_step_order huv n (bisection_le_and_le hab huv n).2.1

private theorem bisection_interval_length
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (huv : IsBisectionSequence f a b u v) :
    ∀ n, v n - u n = (b - a) / (2 : ℝ) ^ n := by
  intro n
  induction n with
  | zero => simp only [huv.1, huv.2.1, pow_zero, div_one]
  | succ n ih =>
      rcases huv.2.2 n with h | h
      · rcases h with ⟨-, hu, hv⟩
        rw [hu, hv]
        calc
          v n - (u n + v n) / 2 = (v n - u n) / 2 := by ring
          _ = ((b - a) / (2 : ℝ) ^ n) / 2 := by rw [ih]
          _ = (b - a) / (2 : ℝ) ^ (n + 1) := by
            rw [pow_succ]
            ring
      · rcases h with ⟨-, hu, hv⟩
        rw [hu, hv]
        calc
          (u n + v n) / 2 - u n = (v n - u n) / 2 := by ring
          _ = ((b - a) / (2 : ℝ) ^ n) / 2 := by rw [ih]
          _ = (b - a) / (2 : ℝ) ^ (n + 1) := by
            rw [pow_succ]
            ring

namespace IsBisectionSequence

/-- Every bisection interval stays ordered and inside the initial interval. -/
theorem le_and_le
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (huv : IsBisectionSequence f a b u v) (hab : a ≤ b) (n : ℕ) :
    a ≤ u n ∧ u n ≤ v n ∧ v n ≤ b :=
  bisection_le_and_le hab huv n

/-- Every bisection interval stays ordered, inside the initial interval, and preserves signs. -/
theorem invariants
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (huv : IsBisectionSequence f a b u v) (hab : a ≤ b)
    (ha : f a ≤ 0) (hb : 0 ≤ f b) (n : ℕ) :
    a ≤ u n ∧ u n ≤ v n ∧ v n ≤ b ∧ f (u n) ≤ 0 ∧ 0 ≤ f (v n) :=
  bisection_invariants hab ha hb huv n

/-- Consecutive bisection intervals are nested. -/
theorem nested
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (huv : IsBisectionSequence f a b u v) (hab : a ≤ b) (n : ℕ) :
    u n ≤ u (n + 1) ∧ u (n + 1) ≤ v (n + 1) ∧ v (n + 1) ≤ v n :=
  bisection_nesting hab huv n

/-- The length of the `n`th bisection interval is the initial length divided by `2 ^ n`. -/
theorem sub_eq
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (huv : IsBisectionSequence f a b u v) (n : ℕ) :
    v n - u n = (b - a) / (2 : ℝ) ^ n :=
  bisection_interval_length huv n

end IsBisectionSequence

private noncomputable def bisection_pairs (f : ℝ → ℝ) (a b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a, b)
  | n + 1 =>
      let p := bisection_pairs f a b n
      let m := (p.1 + p.2) / 2
      if f m ≤ 0 then (m, p.2) else (p.1, m)

private theorem bisection_pairs_is_sequence (f : ℝ → ℝ) (a b : ℝ) :
    IsBisectionSequence f a b
      (fun n => (bisection_pairs f a b n).1)
      (fun n => (bisection_pairs f a b n).2) := by
  refine ⟨rfl, rfl, ?_⟩
  intro n
  dsimp only
  by_cases h : f (((bisection_pairs f a b n).1 + (bisection_pairs f a b n).2) / 2) ≤ 0
  · left
    exact ⟨h, by simp [bisection_pairs, h], by simp [bisection_pairs, h]⟩
  · right
    exact ⟨le_of_not_ge h, by simp [bisection_pairs, h], by simp [bisection_pairs, h]⟩

/-- A bisection sequence exists for every function and pair of endpoints. -/
theorem exists_isBisectionSequence (f : ℝ → ℝ) (a b : ℝ) :
    ∃ u v, IsBisectionSequence f a b u v :=
  ⟨fun n => (bisection_pairs f a b n).1,
    fun n => (bisection_pairs f a b n).2,
    bisection_pairs_is_sequence f a b⟩

private theorem bisection_geometric_tendsto_zero (a b : ℝ) :
    Filter.Tendsto (fun n : ℕ => (b - a) / (2 : ℝ) ^ n)
      Filter.atTop (nhds 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hm := hp.const_mul (b - a)
  simpa [div_eq_mul_inv] using hm

private theorem bisection_endpoint_limits
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (hab : a ≤ b) (huv : IsBisectionSequence f a b u v) :
    ∃ c ∈ Set.Icc a b,
      Filter.Tendsto u Filter.atTop (nhds c) ∧
      Filter.Tendsto v Filter.atTop (nhds c) ∧
      ∀ n, u n ≤ c ∧ c ≤ v n := by
  have hinv := bisection_le_and_le hab huv
  have hnest := bisection_nesting hab huv
  have hmono : Monotone u := monotone_nat_of_le_succ fun n => (hnest n).1
  have hanti : Antitone v := antitone_nat_of_succ_le fun n => (hnest n).2.2
  have hbdd : BddAbove (Set.range u) := by
    refine ⟨b, ?_⟩
    rintro x ⟨n, rfl⟩
    exact (hinv n).2.1.trans (hinv n).2.2
  let c := ⨆ n, u n
  have hu : Filter.Tendsto u Filter.atTop (nhds c) := by
    simpa only [c] using tendsto_atTop_ciSup hmono hbdd
  have hv_eq : ∀ n, v n = u n + (b - a) / (2 : ℝ) ^ n := by
    intro n
    linarith [bisection_interval_length huv n]
  have hv : Filter.Tendsto v Filter.atTop (nhds c) := by
    have hadd := hu.add (bisection_geometric_tendsto_zero a b)
    convert hadd using 1
    · ext n
      exact hv_eq n
    · simp
  have hac : a ≤ c := by
    simpa only [c, huv.1] using le_ciSup hbdd 0
  have hcb : c ≤ b := by
    simpa only [c] using ciSup_le (fun n => (hinv n).2.1.trans (hinv n).2.2)
  refine ⟨c, ⟨hac, hcb⟩, hu, hv, ?_⟩
  intro n
  constructor
  · simpa only [c] using le_ciSup hbdd n
  · apply le_of_tendsto hv
    exact Filter.eventually_atTop.2 ⟨n, fun k hnk => hanti hnk⟩

private theorem bisection_limit_root
    {f : ℝ → ℝ} {a b c : ℝ} {u v : ℕ → ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (ha : f a ≤ 0) (hb : 0 ≤ f b) (huv : IsBisectionSequence f a b u v)
    (hc : c ∈ Set.Icc a b)
    (hu : Filter.Tendsto u Filter.atTop (nhds c))
    (hv : Filter.Tendsto v Filter.atTop (nhds c)) : f c = 0 := by
  have hinv := bisection_invariants hab ha hb huv
  have hu_mem : ∀ n, u n ∈ Set.Icc a b := fun n =>
    ⟨(hinv n).1, (hinv n).2.1.trans (hinv n).2.2.1⟩
  have hv_mem : ∀ n, v n ∈ Set.Icc a b := fun n =>
    ⟨(hinv n).1.trans (hinv n).2.1, (hinv n).2.2.1⟩
  have hu' : Filter.Tendsto u Filter.atTop (nhdsWithin c (Set.Icc a b)) :=
    tendsto_nhdsWithin_iff.2 ⟨hu, Filter.Eventually.of_forall hu_mem⟩
  have hv' : Filter.Tendsto v Filter.atTop (nhdsWithin c (Set.Icc a b)) :=
    tendsto_nhdsWithin_iff.2 ⟨hv, Filter.Eventually.of_forall hv_mem⟩
  have hfu : Filter.Tendsto (fun n => f (u n)) Filter.atTop (nhds (f c)) :=
    (hf c hc).tendsto.comp hu'
  have hfv : Filter.Tendsto (fun n => f (v n)) Filter.atTop (nhds (f c)) :=
    (hf c hc).tendsto.comp hv'
  have hfc_nonpos : f c ≤ 0 :=
    le_of_tendsto hfu (Filter.Eventually.of_forall fun n => (hinv n).2.2.2.1)
  have hfc_nonneg : 0 ≤ f c := by
    have hneg := hfv.neg
    have : -f c ≤ 0 := le_of_tendsto hneg <|
      Filter.Eventually.of_forall fun n => neg_nonpos.mpr (hinv n).2.2.2.2
    linarith
  exact le_antisymm hfc_nonpos hfc_nonneg

private theorem bisection_midpoint_tendsto
    {c : ℝ} {u v : ℕ → ℝ}
    (hu : Filter.Tendsto u Filter.atTop (nhds c))
    (hv : Filter.Tendsto v Filter.atTop (nhds c)) :
    Filter.Tendsto (fun n => (u n + v n) / 2) Filter.atTop (nhds c) := by
  simpa only [add_self_div_two] using (hu.add hv).div_const 2

private theorem bisection_midpoint_error
    {f : ℝ → ℝ} {a b c : ℝ} {u v : ℕ → ℝ}
    (huv : IsBisectionSequence f a b u v)
    (hc : ∀ n, u n ≤ c ∧ c ≤ v n) :
    ∀ n, |(u n + v n) / 2 - c| ≤ (b - a) / (2 : ℝ) ^ (n + 1) := by
  intro n
  calc
    |(u n + v n) / 2 - c| ≤ (v n - u n) / 2 := by
      rw [abs_le]
      constructor <;> linarith [(hc n).1, (hc n).2]
    _ = ((b - a) / (2 : ℝ) ^ n) / 2 := by rw [bisection_interval_length huv n]
    _ = (b - a) / (2 : ℝ) ^ (n + 1) := by
      rw [pow_succ]
      ring

/-- A sign bracket admits nested bisection intervals with exact geometric length. -/
theorem exists_isBisectionSequence_nested
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (ha : f a ≤ 0) (hb : 0 ≤ f b) :
    ∃ u v : ℕ → ℝ, IsBisectionSequence f a b u v ∧
      (∀ n, u n ≤ u (n + 1) ∧ u (n + 1) ≤ v (n + 1) ∧ v (n + 1) ≤ v n) ∧
      (∀ n, v n - u n = (b - a) / (2 : ℝ) ^ n) ∧
      ∀ n, f (u n) * f (v n) ≤ 0 := by
  obtain ⟨u, v, hseq⟩ := exists_isBisectionSequence f a b
  refine ⟨u, v, hseq, hseq.nested hab, hseq.sub_eq, ?_⟩
  intro n
  have h := hseq.invariants hab ha hb n
  exact mul_nonpos_of_nonpos_of_nonneg h.2.2.2.1 h.2.2.2.2

set_option linter.unusedVariables false in
/-- Bisection method: nested bracketing intervals halving in length at each
step while keeping a sign change.
Sources: `Mathlib/docs/undergrad.yaml`, section `Numerical Analysis` /
`Iterative methods of solving systems of real and vector-valued equations`,
entry `bisection method` (unmapped);
R. L. Burden and J. D. Faires, Numerical Analysis, 10th ed., Section 2.1;
stable ref https://en.wikipedia.org/wiki/Bisection_method.

Proves `Wanted` entry `bisection_nested_intervals`.

Proof: The endpoint pairs are defined recursively by the sign of each midpoint, and induction
proves the nesting, sign, and exact halving invariants from Burden and Faires, Section 2.1.
-/
@[nolint unusedArguments] -- `hf` keeps the stated hypothesis
theorem bisection_nested_intervals
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (ha : f a ≤ 0) (hb : 0 ≤ f b) :
    ∃ u v : ℕ → ℝ, IsBisectionSequence f a b u v ∧
      (∀ n, u n ≤ u (n + 1) ∧ u (n + 1) ≤ v (n + 1) ∧ v (n + 1) ≤ v n) ∧
      (∀ n, v n - u n = (b - a) / (2 : ℝ) ^ n) ∧
      ∀ n, f (u n) * f (v n) ≤ 0 := exists_isBisectionSequence_nested hab ha hb

/-- Bisection correctness with linear rate: the midpoints converge to a root
with error at most `(b - a) / 2 ^ (n + 1)`.
Sources: `Mathlib/docs/undergrad.yaml`, section `Numerical Analysis` /
`Iterative methods of solving systems of real and vector-valued equations`,
entries `bisection method` and `rate of convergence and estimation of error`
(unmapped); R. L. Burden and J. D. Faires, Numerical Analysis, 10th ed.,
Theorem 2.1.

Proves `Wanted` entry `bisection_approximate_root_with_rate`.

Proof: Monotone convergence gives the common endpoint limit, continuity makes it a root, and the
halved interval length gives the midpoint error bound, following Burden and Faires, Theorem 2.1.
-/
theorem bisection_approximate_root_with_rate
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (ha : f a ≤ 0) (hb : 0 ≤ f b)
    (u v : ℕ → ℝ) (huv : IsBisectionSequence f a b u v) :
    ∃ c ∈ Set.Icc a b, f c = 0 ∧
      Filter.Tendsto (fun n => (u n + v n) / 2) Filter.atTop (nhds c) ∧
      ∀ n, |(u n + v n) / 2 - c| ≤ (b - a) / (2 : ℝ) ^ (n + 1) := by
  obtain ⟨c, hc, hu, hv, hbracket⟩ := bisection_endpoint_limits hab huv
  exact ⟨c, hc, bisection_limit_root hab hf ha hb huv hc hu hv,
    bisection_midpoint_tendsto hu hv, bisection_midpoint_error huv hbracket⟩

end MetaMathlibExt
