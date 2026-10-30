/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Probability.Process.Kolmogorov

/-!
# Kolmogorov continuity theorem

If a real-valued process `X` on a probability space satisfies the moment
bound `E |X_s - X_t|^β ≤ K |s - t|^{1+α}` for some `α, β > 0`, then for
every `γ < α / β` with `γ > 0` the original process `X` has a common
almost-sure `γ`-Hölder bound on the dyadic rationals of `[0, 1]`. The
original modification statement is retained as a corollary, choosing `Y = X`.
The canonical `ProbabilityTheory.IsKolmogorovProcess` adapter derives the
moment hypotheses from its measurable-pair and lintegral fields.

## Source

This formalizes the target "Theorem (Kolmogorov continuity theorem)"
(Lecture 37) in `v1/Atlas/TheoryOfProbability/targets.yaml`, whose v1
formalization is `v1/Atlas/TheoryOfProbability/code/KolmogorovContinuity.lean`
(left unproved there).

## Correction to the v1 statement (please read)

The v1 statement is **false as written**: it imposes the moment bound in
the form of a Bochner-integral inequality, but in Lean the Bochner
integral of a non-integrable function is `0` by convention, so the bound
holds vacuously for processes whose increments are not integrable.
Counterexample (for `β > 0`): let `(Ω, μ) = ([0, 1], Lebesgue)`, let
`A ⊆ [0, 1]` be a set whose indicator is not almost-everywhere strongly
measurable (e.g. a Vitali-type set, which exists by choice), and set
`X_t = h(t) · 1_A` with `h(0) = 0` and `h(t) = 1` for `t ≠ 0`. For
every `s, t`, since `β > 0`, the function `|X_s - X_t|^β` is either the
zero function (when `h(s) = h(t)`) or `1_A` (when `h(s) ≠ h(t)`). The
zero increments are integrable with integral `0`, while the nonzero
increments are not integrable, so their Bochner integral is `0` by
convention. Hence the Bochner integral is `0` in both cases and the
moment bound holds for any `α, K ≥ 0` (with the fixed `β > 0`; at
`β = 0` the integrand is identically `1`, so this does not apply). But
no Hölder modification exists: for any `γ > 0`, a
modification `Y` would have to satisfy `Y_t ω = h(t)` for all dyadic `t`
simultaneously on a set of `ω ∈ A` of positive outer measure (a countable
intersection of full-measure sets), and then `|Y_{2^{-m}} ω - Y_0 ω| = 1`
cannot be bounded by `C (2^{-m})^γ → 0`.

This file therefore adds the hypothesis that the moments genuinely exist:

  `hX_int : ∀ s t, Integrable (fun ω => |X s ω - X t ω| ^ β) μ`.

With it, the Bochner-integral bound is a genuine expectation bound and
the classical proof goes through: a Borel–Cantelli estimate on dyadic
increments (Markov's inequality plus the moment bound), followed by a
chaining argument along dyadic approximations.

## Proof outline

* `badDyadicSet X γ m` is the event that some adjacent dyadic increment
  at level `m` exceeds `2^{-mγ}`. Markov's inequality plus the moment
  bound give `μ (badDyadicSet X γ m) ≤ K * 2^{-m(α - γβ)}`, which is
  summable since `γβ < α`. The first Borel–Cantelli lemma gives a set of
  full measure on which all sufficiently fine dyadic increments are
  `≤ 2^{-mγ}`.
* On such a good `ω`, define `D(ω)` from the finitely many coarse
  increments; then every dyadic increment at every level is bounded by
  `D * 2^{-mγ}`.
* The deterministic chaining lemma `dyadic_holder_of_increment_bound`
  turns the increment bound into a Hölder bound: approximate `q` and `r`
  from below by dyadic grid points at levels `k → ∞` (each step moves by
  at most one grid step), sum the geometric series of increment bounds
  for the two tails, and bound the middle piece by at most four grid
  steps.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MathlibExt.Probability.KolmogorovContinuity

/-- The set of **dyadic rationals**: real numbers of the form `k / 2 ^ n`
for some integer `k` and natural number `n`. -/
def dyadicRationals : Set ℝ :=
  {x : ℝ | ∃ k : ℤ, ∃ n : ℕ, x = k / (2 : ℝ) ^ n}

/-! ### Dyadic approximations -/

/-- The dyadic approximation of `q` at level `k`: `⌊q * 2^k⌋ / 2^k`, the
largest dyadic rational of denominator `2^k` that is `≤ q`. -/
private noncomputable def approxPt (q : ℝ) (k : ℕ) : ℝ :=
  ((⌊q * (2 : ℝ) ^ k⌋ : ℤ) : ℝ) / (2 : ℝ) ^ k

/-- The dyadic approximation lies in `[0, 1]` whenever `q` does. -/
private lemma approxPt_mem {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (k : ℕ) :
    0 ≤ approxPt q k ∧ approxPt q k ≤ 1 := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  constructor
  · apply div_nonneg _ hpos.le
    exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg hq0 hpos.le)
  · rw [approxPt, div_le_one hpos]
    calc ((⌊q * (2 : ℝ) ^ k⌋ : ℤ) : ℝ) ≤ q * (2 : ℝ) ^ k := Int.floor_le _
      _ ≤ (2 : ℝ) ^ k := mul_le_of_le_one_left hpos.le hq1

/-- The approximation error is at most one grid step. -/
private lemma approxPt_sub_le {q : ℝ} (k : ℕ) :
    0 ≤ q - approxPt q k ∧ q - approxPt q k ≤ 1 / (2 : ℝ) ^ k := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have h1 : ((⌊q * (2 : ℝ) ^ k⌋ : ℤ) : ℝ) ≤ q * (2 : ℝ) ^ k := Int.floor_le _
  have h2 : q * (2 : ℝ) ^ k - ((⌊q * (2 : ℝ) ^ k⌋ : ℤ) : ℝ) < 1 := by
    have h := Int.lt_floor_add_one (q * (2 : ℝ) ^ k)
    linarith
  constructor
  · have : approxPt q k ≤ q := by
      rw [approxPt, div_le_iff₀ hpos]
      calc ((⌊q * (2 : ℝ) ^ k⌋ : ℤ) : ℝ) ≤ q * (2 : ℝ) ^ k := h1
        _ = q * (2 : ℝ) ^ k := by ring
    linarith
  · rw [approxPt, sub_div' (by positivity : (2 : ℝ) ^ k ≠ 0)]
    exact (div_lt_div_of_pos_right h2 hpos).le

/-- Consecutive approximations agree or differ by exactly one grid step
at the finer level, and in the latter case the finer floor is
`2 * ⌊q * 2^k⌋ + 1`. -/
private lemma approxPt_step {q : ℝ} (k : ℕ) :
    approxPt q (k + 1) = approxPt q k ∨
      (⌊q * (2 : ℝ) ^ (k + 1)⌋ = 2 * ⌊q * (2 : ℝ) ^ k⌋ + 1 ∧
        approxPt q (k + 1) = approxPt q k + 1 / (2 : ℝ) ^ (k + 1)) := by
  have h2 : q * (2 : ℝ) ^ (k + 1) = 2 * (q * (2 : ℝ) ^ k) := by
    rw [pow_succ]; ring
  have hle : ((⌊q * (2 : ℝ) ^ k⌋ : ℤ) : ℝ) ≤ q * (2 : ℝ) ^ k := Int.floor_le _
  have hlt : q * (2 : ℝ) ^ k < ((⌊q * (2 : ℝ) ^ k⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  by_cases hcase : q * (2 : ℝ) ^ (k + 1) < ((2 * ⌊q * (2 : ℝ) ^ k⌋ + 1 : ℤ) : ℝ)
  · left
    have hfloor : ⌊q * (2 : ℝ) ^ (k + 1)⌋ = 2 * ⌊q * (2 : ℝ) ^ k⌋ := by
      rw [Int.floor_eq_iff]
      push_cast at hcase ⊢
      constructor
      · linarith [hle, h2]
      · linarith [hcase]
    rw [approxPt, approxPt, hfloor]
    push_cast
    rw [pow_succ]
    field_simp
  · right
    have hfloor : ⌊q * (2 : ℝ) ^ (k + 1)⌋ = 2 * ⌊q * (2 : ℝ) ^ k⌋ + 1 := by
      rw [Int.floor_eq_iff]
      push_cast at hcase ⊢
      constructor
      · linarith [hcase]
      · linarith [hlt, h2]
    refine ⟨hfloor, ?_⟩
    rw [approxPt, approxPt, hfloor]
    push_cast
    rw [pow_succ]
    field_simp

/-- A dyadic rational is eventually fixed by the approximation: if
`q = a / 2^n` and `n ≤ k`, then the level-`k` approximation of `q` is `q`. -/
private lemma approxPt_eq_of_dyadic {q : ℝ} {a : ℤ} {n : ℕ} (hq : q = a / (2 : ℝ) ^ n)
    {k : ℕ} (hk : n ≤ k) : approxPt q k = q := by
  have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
  have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
  have h2kn : (2 : ℝ) ^ (k - n) ≠ 0 := by positivity
  have hsplit : (2 : ℝ) ^ k = (2 : ℝ) ^ n * (2 : ℝ) ^ (k - n) := by
    rw [← pow_add, Nat.add_sub_cancel' hk]
  have h1 : q * (2 : ℝ) ^ k = ((a * (2 : ℤ) ^ (k - n) : ℤ) : ℝ) := by
    rw [hq, hsplit]
    field_simp
    push_cast
    ring
  rw [approxPt, h1, Int.floor_intCast, hq, hsplit]
  field_simp
  push_cast
  ring

/-! ### Telescoping -/

/-- Telescoping sum over an interval of naturals. -/
private lemma sum_Ico_sub (g : ℕ → ℝ) {m N : ℕ} (h : m ≤ N) :
    ∑ k ∈ Finset.Ico m N, (g (k + 1) - g k) = g N - g m := by
  induction N, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top hn, ih]
      ring

/-- One grid step at level `m` from `a / 2^m` to `b / 2^m` can be
decomposed into `b - a` adjacent steps. -/
private lemma gridPath_bound {f : ℝ → ℝ} {γ D : ℝ}
    (hf : ∀ m : ℕ, ∀ k : ℕ, k < 2 ^ m →
      |f ((k + 1 : ℝ) / (2 : ℝ) ^ m) - f ((k : ℝ) / (2 : ℝ) ^ m)| ≤
        D * (2 : ℝ) ^ (-(m : ℝ) * γ))
    (m : ℕ) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 2 ^ m) :
    |f ((b : ℝ) / (2 : ℝ) ^ m) - f ((a : ℝ) / (2 : ℝ) ^ m)| ≤
      ((b : ℝ) - a) * D * (2 : ℝ) ^ (-(m : ℝ) * γ) := by
  have htel : f ((b : ℝ) / (2 : ℝ) ^ m) - f ((a : ℝ) / (2 : ℝ) ^ m)
      = ∑ k ∈ Finset.Ico a b,
        (f (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m) - f ((k : ℝ) / (2 : ℝ) ^ m)) := by
    have h := sum_Ico_sub (fun k => f ((k : ℝ) / (2 : ℝ) ^ m)) hab
    rw [← h]
  rw [htel]
  calc |∑ k ∈ Finset.Ico a b,
        (f (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m) - f ((k : ℝ) / (2 : ℝ) ^ m))|
      ≤ ∑ k ∈ Finset.Ico a b,
        |f (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m) - f ((k : ℝ) / (2 : ℝ) ^ m)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Ico a b, D * (2 : ℝ) ^ (-(m : ℝ) * γ) := by
        apply Finset.sum_le_sum
        intro k hk
        have hklt : k < 2 ^ m := lt_of_lt_of_le (Finset.mem_Ico.mp hk).2 hb
        have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        exact hf m k hklt
    _ = ((b : ℝ) - a) * D * (2 : ℝ) ^ (-(m : ℝ) * γ) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        rw [Nat.cast_sub hab]
        ring

/-! ### Chaining -/

/-- One step of the approximation moves by at most one grid step, hence
its increment is bounded by the increment bound at the finer level
(the step is the adjacent grid increment at index `2 * j.toNat`). -/
private lemma approx_step_bound_of_step {f : ℝ → ℝ} {γ D : ℝ}
    (hf : ∀ m : ℕ, ∀ k : ℕ, k < 2 ^ m →
      |f ((k + 1 : ℝ) / (2 : ℝ) ^ m) - f ((k : ℝ) / (2 : ℝ) ^ m)| ≤
        D * (2 : ℝ) ^ (-(m : ℝ) * γ))
    {q : ℝ} (k : ℕ) (j : ℤ) (hj0 : 0 ≤ j) (hjlt : j < (2 : ℤ) ^ k)
    (hA1 : approxPt q (k + 1) = ((2 * j.toNat + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1))
    (hA0 : approxPt q k = ((2 * j.toNat : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1)) :
    |f (approxPt q (k + 1)) - f (approxPt q k)| ≤
      D * (2 : ℝ) ^ (-((k + 1 : ℕ) : ℝ) * γ) := by
  have h2j : 2 * j.toNat < 2 ^ (k + 1) := by
    have h3 : (2 : ℤ) * (j.toNat : ℤ) < (2 : ℤ) ^ (k + 1) := by
      rw [Int.toNat_of_nonneg hj0, pow_succ]
      linarith [hjlt]
    exact_mod_cast h3
  rw [hA1, hA0]
  have hcast : ((2 * j.toNat + 1 : ℕ) : ℝ) = ((2 * j.toNat : ℕ) : ℝ) + 1 := by
    push_cast; ring
  rw [hcast]
  exact hf (k + 1) (2 * j.toNat) h2j

/-- One step of the approximation moves by at most one grid step, hence
its increment is bounded by the increment bound at the finer level. -/
private lemma approx_step_bound {f : ℝ → ℝ} {γ D : ℝ} (hD : 0 < D)
    (hf : ∀ m : ℕ, ∀ k : ℕ, k < 2 ^ m →
      |f ((k + 1 : ℝ) / (2 : ℝ) ^ m) - f ((k : ℝ) / (2 : ℝ) ^ m)| ≤
        D * (2 : ℝ) ^ (-(m : ℝ) * γ))
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (k : ℕ) :
    |f (approxPt q (k + 1)) - f (approxPt q k)| ≤
      D * (2 : ℝ) ^ (-((k + 1 : ℕ) : ℝ) * γ) := by
  rcases approxPt_step (q := q) (k := k) with h0 | ⟨hJ, hstep⟩
  · rw [h0, sub_self, abs_zero]
    exact mul_nonneg hD.le (Real.rpow_pos_of_pos (by norm_num) _).le
  · have hj0 : 0 ≤ ⌊q * (2 : ℝ) ^ k⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg hq0 (by positivity))
    have hcast : (((⌊q * (2 : ℝ) ^ k⌋).toNat : ℕ) : ℝ)
        = ((⌊q * (2 : ℝ) ^ k⌋ : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hj0]
    have hle1 : approxPt q k < 1 := by
      have hlt : approxPt q (k + 1) ≤ 1 := (approxPt_mem hq0 hq1 (k + 1)).2
      rw [hstep] at hlt
      have hpos : (0:ℝ) < 1 / (2 : ℝ) ^ (k + 1) := by positivity
      linarith
    have hjlt : ⌊q * (2 : ℝ) ^ k⌋ < (2 : ℤ) ^ k := by
      rw [approxPt, div_lt_one (by positivity : (0:ℝ) < (2 : ℝ) ^ k)] at hle1
      have hcast2 : ((2 : ℤ) ^ k : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
      rw [← hcast2] at hle1
      exact_mod_cast hle1
    have hA1 : approxPt q (k + 1)
        = ((2 * (⌊q * (2 : ℝ) ^ k⌋).toNat + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1) := by
      rw [approxPt, hJ]
      rw [show ((2 * (⌊q * (2 : ℝ) ^ k⌋).toNat + 1 : ℕ) : ℝ)
          = ((2 * ⌊q * (2 : ℝ) ^ k⌋ + 1 : ℤ) : ℝ) by
        push_cast; rw [hcast]]
    have hA0 : approxPt q k
        = ((2 * (⌊q * (2 : ℝ) ^ k⌋).toNat : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1) := by
      rw [approxPt, pow_succ]
      have hpos : (0:ℝ) < (2 : ℝ) ^ k := by positivity
      field_simp [hpos.ne']
      push_cast
      rw [hcast]
      ring
    exact approx_step_bound_of_step hf k _ hj0 hjlt hA1 hA0

/-- Tail estimate: the approximation at level `m` is close to `q`, with
error controlled by the geometric series of increment bounds. -/
private lemma tail_bound {f : ℝ → ℝ} {γ D : ℝ} (hγ : 0 < γ) (hD : 0 < D)
    (hf : ∀ m : ℕ, ∀ k : ℕ, k < 2 ^ m →
      |f ((k + 1 : ℝ) / (2 : ℝ) ^ m) - f ((k : ℝ) / (2 : ℝ) ^ m)| ≤
        D * (2 : ℝ) ^ (-(m : ℝ) * γ))
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hq : ∃ a : ℤ, ∃ n : ℕ, q = a / (2 : ℝ) ^ n) (m : ℕ) :
    |f q - f (approxPt q m)| ≤
      (D * (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ))) * (2 : ℝ) ^ (-(m : ℝ) * γ) := by
  obtain ⟨a, n, hqeq⟩ := hq
  set N := max m n with hN
  have hNn : n ≤ N := le_max_right _ _
  have hNm : m ≤ N := le_max_left _ _
  have hA : approxPt q N = q := approxPt_eq_of_dyadic hqeq hNn
  have htel : f q - f (approxPt q m)
      = ∑ k ∈ Finset.Ico m N, (f (approxPt q (k + 1)) - f (approxPt q k)) := by
    have h := sum_Ico_sub (fun k => f (approxPt q k)) hNm
    rw [hA] at h
    exact h.symm
  have hρ0 : (0:ℝ) ≤ (2 : ℝ) ^ (-γ) := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hρ1 : (2 : ℝ) ^ (-γ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  -- The tail terms reindex as a geometric series.
  have hgeq : ∀ j : ℕ, D * (2 : ℝ) ^ (-((m + j + 1 : ℕ) : ℝ) * γ)
      = (D * (2 : ℝ) ^ (-(m : ℝ) * γ) * (2 : ℝ) ^ (-γ)) * ((2 : ℝ) ^ (-γ)) ^ j := by
    intro j
    have e1 : (-((m + j + 1 : ℕ) : ℝ)) * γ
        = -(m : ℝ) * γ + (-γ) + (j : ℝ) * (-γ) := by
      push_cast; ring
    have e2 : ((2 : ℝ) ^ (-γ)) ^ j = (2 : ℝ) ^ ((j : ℝ) * (-γ)) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (-γ)) j, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1; ring
    rw [e1, Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_add (by norm_num : (0:ℝ) < 2),
      e2]
    ring
  have hsum : Summable (fun j : ℕ => D * (2 : ℝ) ^ (-((m + j + 1 : ℕ) : ℝ) * γ)) := by
    rw [show (fun j : ℕ => D * (2 : ℝ) ^ (-((m + j + 1 : ℕ) : ℝ) * γ))
        = fun j => (D * (2 : ℝ) ^ (-(m : ℝ) * γ) * (2 : ℝ) ^ (-γ)) * ((2 : ℝ) ^ (-γ)) ^ j
      from funext hgeq]
    exact (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  have htsum : ∑' j : ℕ, D * (2 : ℝ) ^ (-((m + j + 1 : ℕ) : ℝ) * γ)
      = (D * (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ))) * (2 : ℝ) ^ (-(m : ℝ) * γ) := by
    rw [tsum_congr hgeq, tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1, div_eq_mul_inv]
    ring
  rw [htel]
  calc |∑ k ∈ Finset.Ico m N, (f (approxPt q (k + 1)) - f (approxPt q k))|
      ≤ ∑ k ∈ Finset.Ico m N, |f (approxPt q (k + 1)) - f (approxPt q k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Ico m N, D * (2 : ℝ) ^ (-((k + 1 : ℕ) : ℝ) * γ) := by
        apply Finset.sum_le_sum
        intro k _
        exact approx_step_bound hD hf hq0 hq1 k
    _ = ∑ j ∈ Finset.range (N - m),
        D * (2 : ℝ) ^ (-((m + j + 1 : ℕ) : ℝ) * γ) := by
        rw [Finset.sum_Ico_eq_sum_range]
    _ ≤ ∑' j : ℕ, D * (2 : ℝ) ^ (-((m + j + 1 : ℕ) : ℝ) * γ) :=
        hsum.sum_le_tsum (Finset.range (N - m)) (fun j _ =>
          mul_nonneg hD.le (Real.rpow_pos_of_pos (by norm_num) _).le)
    _ = (D * (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ))) * (2 : ℝ) ^ (-(m : ℝ) * γ) := htsum

/-- Deterministic chaining for `q ≤ r`: if every adjacent dyadic
increment at level `m` is at most `D * 2^{-mγ}`, then `f` is Hölder
continuous on the dyadic rationals of `[0, 1]`. -/
private lemma dyadic_holder_of_le {f : ℝ → ℝ} {γ D : ℝ} (hγ : 0 < γ) (hD : 0 < D)
    (hf : ∀ m : ℕ, ∀ k : ℕ, k < 2 ^ m →
      |f ((k + 1 : ℝ) / (2 : ℝ) ^ m) - f ((k : ℝ) / (2 : ℝ) ^ m)| ≤
        D * (2 : ℝ) ^ (-(m : ℝ) * γ))
    {q r : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hq : ∃ a : ℤ, ∃ n : ℕ, q = a / (2 : ℝ) ^ n)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hr : ∃ b : ℤ, ∃ n : ℕ, r = b / (2 : ℝ) ^ n) (hqr : q ≤ r) :
    |f q - f r| ≤ D * (4 + 2 * (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ))) * |q - r| ^ γ := by
  by_cases hqr_eq : q = r
  · subst hqr_eq
    simp [abs_zero, Real.zero_rpow (ne_of_gt hγ)]
  have hd : 0 < r - q := sub_pos.mpr (lt_of_le_of_ne hqr hqr_eq)
  have hex : ∃ m : ℕ, (2 : ℝ) ^ (-(m : ℝ)) ≤ r - q := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (r - q)⁻¹ (by norm_num : (1 : ℝ) < 2)
    refine ⟨N, ?_⟩
    have h1 : (2 : ℝ) ^ (-(N : ℝ)) = 1 / (2 : ℝ) ^ N := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast, one_div]
    rw [h1]
    have hlt : 1 / (2 : ℝ) ^ N < r - q :=
      (one_div_lt (by positivity : (0:ℝ) < (2:ℝ) ^ N) hd).mpr (by rwa [inv_eq_one_div] at hN)
    exact hlt.le
  set m := Nat.find hex with hmdef
  have hm : (2 : ℝ) ^ (-(m : ℝ)) ≤ r - q := Nat.find_spec hex
  have hm_lt : m = 0 ∨ r - q < (2 : ℝ) ^ (-(((m - 1 : ℕ)) : ℝ)) := by
    by_cases hm0 : m = 0
    · exact Or.inl hm0
    · right
      have hnot := Nat.find_min hex (show m - 1 < m from Nat.pred_lt (by omega))
      exact not_le.mp hnot
  have htail_q := tail_bound hγ hD hf hq0 hq1 hq m
  have htail_r := tail_bound hγ hD hf hr0 hr1 hr m
  have hmid : |f (approxPt r m) - f (approxPt q m)| ≤ 4 * D * (2 : ℝ) ^ (-(m : ℝ) * γ) := by
    have hja0 : 0 ≤ ⌊q * (2 : ℝ) ^ m⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg hq0 (by positivity))
    have hjb0 : 0 ≤ ⌊r * (2 : ℝ) ^ m⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg hr0 (by positivity))
    have hcastA : (((⌊q * (2 : ℝ) ^ m⌋).toNat : ℕ) : ℝ)
        = ((⌊q * (2 : ℝ) ^ m⌋ : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hja0]
    have hcastB : (((⌊r * (2 : ℝ) ^ m⌋).toNat : ℕ) : ℝ)
        = ((⌊r * (2 : ℝ) ^ m⌋ : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hjb0]
    have hle : ⌊q * (2 : ℝ) ^ m⌋ ≤ ⌊r * (2 : ℝ) ^ m⌋ := Int.floor_mono (by
      have hpos : (0:ℝ) ≤ (2 : ℝ) ^ m := by positivity
      nlinarith [hqr, hpos])
    have hA : approxPt q m
        = ((⌊q * (2 : ℝ) ^ m⌋).toNat : ℝ) / (2 : ℝ) ^ m := by
      rw [approxPt]; congr 1; exact hcastA.symm
    have hB : approxPt r m
        = ((⌊r * (2 : ℝ) ^ m⌋).toNat : ℝ) / (2 : ℝ) ^ m := by
      rw [approxPt]; congr 1; exact hcastB.symm
    have hle' : (⌊q * (2 : ℝ) ^ m⌋).toNat ≤ (⌊r * (2 : ℝ) ^ m⌋).toNat := by omega
    have hub : (⌊r * (2 : ℝ) ^ m⌋).toNat ≤ 2 ^ m := by
      have hmem := (approxPt_mem hr0 hr1 m).2
      rw [hB, div_le_one (by positivity : (0:ℝ) < (2 : ℝ) ^ m)] at hmem
      exact_mod_cast hmem
    have hgrid := gridPath_bound hf m hle' hub
    have hdiff : (((⌊r * (2 : ℝ) ^ m⌋).toNat : ℝ) - (⌊q * (2 : ℝ) ^ m⌋).toNat) ≤ 4 := by
      have hbound : approxPt r m - approxPt q m ≤ (r - q) + 1 / (2 : ℝ) ^ m := by
        have hr1 := (approxPt_sub_le (q := r) m).1
        have hq2 := (approxPt_sub_le (q := q) m).2
        linarith
      by_cases hm0 : m = 0
      · rw [hm0] at hA hB ⊢
        have hja1 : ((⌊q * (2 : ℝ) ^ 0⌋).toNat : ℝ) ≤ 1 := by
          have hmem := (approxPt_mem hq0 hq1 0).2
          rw [hA] at hmem
          simpa using hmem
        have hjb1 : ((⌊r * (2 : ℝ) ^ 0⌋).toNat : ℝ) ≤ 1 := by
          have hmem := (approxPt_mem hr0 hr1 0).2
          rw [hB] at hmem
          simpa using hmem
        have h2 : (0:ℝ) ≤ ((⌊q * (2 : ℝ) ^ 0⌋).toNat : ℝ) := by positivity
        linarith
      · have hlt : r - q < (2 : ℝ) ^ (-(((m - 1 : ℕ)) : ℝ)) :=
          hm_lt.resolve_left hm0
        have h2 : (2 : ℝ) ^ (-(((m - 1 : ℕ)) : ℝ)) = 2 / (2 : ℝ) ^ m := by
          have hcast : (((m - 1 : ℕ)) : ℝ) = (m : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ m)]; simp
          rw [hcast, show -((m : ℝ) - 1) = -(m : ℝ) + 1 by ring,
            Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one,
            Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast,
            mul_comm (((2 : ℝ) ^ m)⁻¹) 2, div_eq_mul_inv]
        have hpos : (0:ℝ) < (2 : ℝ) ^ m := by positivity
        have hEq : (((⌊r * (2 : ℝ) ^ m⌋).toNat : ℝ) - (⌊q * (2 : ℝ) ^ m⌋).toNat)
            = (approxPt r m - approxPt q m) * (2 : ℝ) ^ m := by
          rw [hA, hB]
          field_simp [hpos.ne']
        rw [hEq]
        have h1 : (approxPt r m - approxPt q m) * (2 : ℝ) ^ m
            ≤ ((r - q) + 1 / (2 : ℝ) ^ m) * (2 : ℝ) ^ m :=
          mul_le_mul_of_nonneg_right hbound hpos.le
        have h4 : (r - q) * (2 : ℝ) ^ m < 2 := by
          rw [h2] at hlt
          rw [lt_div_iff₀ hpos] at hlt
          exact hlt
        have h3 : ((r - q) + 1 / (2 : ℝ) ^ m) * (2 : ℝ) ^ m < 3 := by
          have e : ((r - q) + 1 / (2 : ℝ) ^ m) * (2 : ℝ) ^ m
              = (r - q) * (2 : ℝ) ^ m + 1 := by
            field_simp [hpos.ne']
          rw [e]
          linarith [h4]
        linarith [h1, h3]
    rw [hA, hB]
    calc |f ((⌊r * (2 : ℝ) ^ m⌋).toNat / (2 : ℝ) ^ m)
          - f ((⌊q * (2 : ℝ) ^ m⌋).toNat / (2 : ℝ) ^ m)|
        ≤ (((⌊r * (2 : ℝ) ^ m⌋).toNat : ℝ) - (⌊q * (2 : ℝ) ^ m⌋).toNat)
          * D * (2 : ℝ) ^ (-(m : ℝ) * γ) := hgrid
      _ ≤ 4 * D * (2 : ℝ) ^ (-(m : ℝ) * γ) := by
          have hnn : 0 ≤ D * (2 : ℝ) ^ (-(m : ℝ) * γ) :=
            mul_nonneg hD.le (Real.rpow_pos_of_pos (by norm_num) _).le
          calc (((⌊r * (2 : ℝ) ^ m⌋).toNat : ℝ) - (⌊q * (2 : ℝ) ^ m⌋).toNat)
                * D * (2 : ℝ) ^ (-(m : ℝ) * γ)
              = (((⌊r * (2 : ℝ) ^ m⌋).toNat : ℝ) - (⌊q * (2 : ℝ) ^ m⌋).toNat)
                * (D * (2 : ℝ) ^ (-(m : ℝ) * γ)) := by ring
            _ ≤ 4 * (D * (2 : ℝ) ^ (-(m : ℝ) * γ)) :=
                mul_le_mul_of_nonneg_right hdiff hnn
            _ = 4 * D * (2 : ℝ) ^ (-(m : ℝ) * γ) := by ring
  have htri : |f q - f r|
      ≤ |f q - f (approxPt q m)| + |f (approxPt r m) - f (approxPt q m)|
        + |f (approxPt r m) - f r| := by
    have heq : f q - f r
        = (f q - f (approxPt q m)) + (f (approxPt q m) - f (approxPt r m))
          + (f (approxPt r m) - f r) := by ring
    have habs : |f (approxPt q m) - f (approxPt r m)|
        = |f (approxPt r m) - f (approxPt q m)| := abs_sub_comm _ _
    rw [heq]
    calc |(f q - f (approxPt q m)) + (f (approxPt q m) - f (approxPt r m))
          + (f (approxPt r m) - f r)|
        ≤ |(f q - f (approxPt q m)) + (f (approxPt q m) - f (approxPt r m))|
          + |f (approxPt r m) - f r| := abs_add_le _ _
      _ ≤ (|f q - f (approxPt q m)| + |f (approxPt q m) - f (approxPt r m)|)
          + |f (approxPt r m) - f r| := by
          gcongr
          exact abs_add_le _ _
      _ = |f q - f (approxPt q m)| + |f (approxPt r m) - f (approxPt q m)|
          + |f (approxPt r m) - f r| := by
          rw [habs]
  have hpow : (2 : ℝ) ^ (-(m : ℝ) * γ) ≤ (r - q) ^ γ := by
    have h1 : (2 : ℝ) ^ (-(m : ℝ) * γ) = ((2 : ℝ) ^ (-(m : ℝ))) ^ γ := by
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [h1]
    exact Real.rpow_le_rpow (Real.rpow_pos_of_pos (by norm_num) _).le hm hγ.le
  have hfin : |f q - f r|
      ≤ D * (4 + 2 * (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ))) * (r - q) ^ γ := by
    have h1 : |f (approxPt r m) - f r| = |f r - f (approxPt r m)| :=
      abs_sub_comm _ _
    have htail : |f q - f (approxPt q m)| + |f (approxPt r m) - f (approxPt q m)|
        + |f (approxPt r m) - f r|
        ≤ 2 * ((D * (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ))) * (2 : ℝ) ^ (-(m : ℝ) * γ))
          + 4 * D * (2 : ℝ) ^ (-(m : ℝ) * γ) := by linarith [htail_q, htail_r, hmid, h1]
    have h2 : 2 * ((D * (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ))) * (2 : ℝ) ^ (-(m : ℝ) * γ))
        + 4 * D * (2 : ℝ) ^ (-(m : ℝ) * γ)
        ≤ D * (4 + 2 * (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ))) * (r - q) ^ γ := by
      have hle1 : (2 : ℝ) ^ (-(m : ℝ) * γ) ≤ (r - q) ^ γ := hpow
      have hnn1 : 0 ≤ D * (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ)) := by
        have hρ1 : (2 : ℝ) ^ (-γ) < 1 :=
          Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
        apply div_nonneg _ (by linarith)
        have : 0 < (2 : ℝ) ^ (-γ) := Real.rpow_pos_of_pos (by norm_num) _
        exact mul_nonneg hD.le this.le
      have hnn2 : 0 ≤ 4 * D := by linarith
      have e1 := mul_le_mul_of_nonneg_left hle1 hnn1
      have e2 := mul_le_mul_of_nonneg_left hle1 hnn2
      calc 2 * ((D * (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ))) * (2 : ℝ) ^ (-(m : ℝ) * γ))
          + 4 * D * (2 : ℝ) ^ (-(m : ℝ) * γ)
          ≤ 2 * ((D * (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ))) * (r - q) ^ γ)
          + (4 * D) * (r - q) ^ γ := by
            exact add_le_add (mul_le_mul_of_nonneg_left e1 (by norm_num : (0:ℝ) ≤ 2)) e2
        _ = D * (4 + 2 * (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ))) * (r - q) ^ γ := by ring
    linarith [htri, htail, h2]
  rw [abs_sub_comm q r, abs_of_nonneg (sub_nonneg.mpr hqr)]
  exact hfin

/-- **Deterministic chaining**: if every adjacent dyadic increment at level
`m` is at most `D * 2^{-mγ}`, then `f` is `γ`-Hölder on the dyadic
rationals of `[0, 1]`, with an explicit constant. -/
theorem dyadic_holder_of_increment_bound {f : ℝ → ℝ} {γ D : ℝ} (hγ : 0 < γ) (hD : 0 < D)
    (hf : ∀ m : ℕ, ∀ k : ℕ, k < 2 ^ m →
      |f ((k + 1 : ℝ) / (2 : ℝ) ^ m) - f ((k : ℝ) / (2 : ℝ) ^ m)| ≤
        D * (2 : ℝ) ^ (-(m : ℝ) * γ))
    {q r : ℝ} (hq : q ∈ dyadicRationals ∩ Set.Icc 0 1)
    (hr : r ∈ dyadicRationals ∩ Set.Icc 0 1) :
    |f q - f r| ≤ D * (4 + 2 * (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ))) * |q - r| ^ γ := by
  obtain ⟨hqD, hq0, hq1⟩ := hq
  obtain ⟨hrD, hr0, hr1⟩ := hr
  simp only [dyadicRationals, Set.mem_ofPred_eq] at hqD hrD
  rcases le_total q r with hqr | hqr
  · exact dyadic_holder_of_le hγ hD hf hq0 hq1 hqD hr0 hr1 hrD hqr
  · rw [abs_sub_comm q r, abs_sub_comm (f q) (f r)]
    exact dyadic_holder_of_le hγ hD hf hr0 hr1 hrD hq0 hq1 hqD hqr

/-! ### Borel–Cantelli estimate for dyadic increments -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The event that some adjacent dyadic increment at level `m` exceeds
`2^{-mγ}`. -/
private noncomputable def badDyadicSet (X : ℝ → Ω → ℝ) (γ : ℝ) (m : ℕ) : Set Ω :=
  ⋃ k ∈ Finset.range (2 ^ m),
    {ω | (2 : ℝ) ^ (-(m : ℝ) * γ)
      < |X ((k + 1 : ℝ) / (2 : ℝ) ^ m) ω - X ((k : ℝ) / (2 : ℝ) ^ m) ω|}

/-- The set of `ω` for which all sufficiently fine dyadic increments are
bounded by `2^{-mγ}`. -/
private def goodSet (X : ℝ → Ω → ℝ) (γ : ℝ) : Set Ω :=
  {ω | ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ k : ℕ, k < 2 ^ m →
    |X ((k + 1 : ℝ) / (2 : ℝ) ^ m) ω - X ((k : ℝ) / (2 : ℝ) ^ m) ω|
      ≤ (2 : ℝ) ^ (-(m : ℝ) * γ)}

/-- The exact power-counting identity behind the Borel–Cantelli estimate:
summing the level-`m` bound `K * 2^{-m(1+α)} / 2^{-mγβ}` over the `2^m`
dyadic intervals leaves `K * 2^{-m(α - γβ)}`. -/
private lemma two_pow_mul_rpow_identity (m : ℕ) (α β γ : ℝ) :
    (2 : ℝ) ^ m * (((2 : ℝ) ^ (-(m : ℝ))) ^ (1 + α)
      / ((2 : ℝ) ^ (-(m : ℝ) * γ)) ^ β)
      = (2 : ℝ) ^ (-(m : ℝ) * (α - γ * β)) := by
  set u := (2 : ℝ) ^ (-(m : ℝ)) with hu_def
  have hu : (0 : ℝ) < u := Real.rpow_pos_of_pos (by norm_num) _
  have h2m : (2 : ℝ) ^ m = u⁻¹ := by
    rw [hu_def, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv, Real.rpow_natCast]
  have hc : (2 : ℝ) ^ (-(m : ℝ) * γ) = u ^ γ := by
    rw [hu_def, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hcb : ((2 : ℝ) ^ (-(m : ℝ) * γ)) ^ β = u ^ (γ * β) := by
    rw [hc, ← Real.rpow_mul hu.le]
  have hpow : (2 : ℝ) ^ (-(m : ℝ) * (α - γ * β)) = u ^ (α - γ * β) := by
    rw [hu_def, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hpow, hcb, h2m, ← Real.rpow_sub hu, ← Real.rpow_neg_one u,
    ← Real.rpow_add hu]
  congr 1; ring

/-- One dyadic interval's bad event, by Markov's inequality and the
moment bound. -/
private lemma measure_badDyadicInterval_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ → Ω → ℝ} {α β K γ : ℝ}
    (hβ : 0 < β)
    (hX_int : ∀ s t : ℝ, Integrable (fun ω => |X s ω - X t ω| ^ β) μ)
    (hkolm : ∀ s t : ℝ, ∫ ω, |X s ω - X t ω| ^ β ∂μ ≤ K * |s - t| ^ (1 + α))
    (m k : ℕ) :
    μ {ω | (2 : ℝ) ^ (-(m : ℝ) * γ)
        < |X ((k + 1 : ℝ) / (2 : ℝ) ^ m) ω - X ((k : ℝ) / (2 : ℝ) ^ m) ω|}
      ≤ ENNReal.ofReal (K * ((2 : ℝ) ^ (-(m : ℝ))) ^ (1 + α)
        / ((2 : ℝ) ^ (-(m : ℝ) * γ)) ^ β) := by
  set s := ((k + 1 : ℝ) / (2 : ℝ) ^ m) with hs
  set t := (k : ℝ) / (2 : ℝ) ^ m with ht
  set c := (2 : ℝ) ^ (-(m : ℝ) * γ) with hcdef
  have hcpos : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hcbpos : 0 < c ^ β := Real.rpow_pos_of_pos hcpos _
  have habs : |s - t| = (2 : ℝ) ^ (-(m : ℝ)) := by
    rw [hs, ht]
    have h1 : ((k + 1 : ℝ) / (2 : ℝ) ^ m) - (k : ℝ) / (2 : ℝ) ^ m = 1 / (2 : ℝ) ^ m := by
      rw [div_sub_div_same]; ring_nf
    rw [h1, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 : ℝ) ^ m), one_div,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
  have hkolm' : ∫ ω, |X s ω - X t ω| ^ β ∂μ
      ≤ K * ((2 : ℝ) ^ (-(m : ℝ))) ^ (1 + α) := by
    have h := hkolm s t
    rwa [habs] at h
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (|X s ω - X t ω| ^ β)) μ :=
    (hX_int s t).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hmarkov : μ {ω | ENNReal.ofReal (c ^ β)
        ≤ ENNReal.ofReal (|X s ω - X t ω| ^ β)}
      ≤ (∫⁻ ω, ENNReal.ofReal (|X s ω - X t ω| ^ β) ∂μ) / ENNReal.ofReal (c ^ β) :=
    meas_ge_le_lintegral_div hmeas
      (ENNReal.ofReal_pos.mpr hcbpos).ne' ENNReal.ofReal_ne_top
  have hint : (∫⁻ ω, ENNReal.ofReal (|X s ω - X t ω| ^ β) ∂μ)
      = ENNReal.ofReal (∫ ω, |X s ω - X t ω| ^ β ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (hX_int s t)
      (ae_of_all _ fun ω => Real.rpow_nonneg (abs_nonneg _) β)).symm
  have hsubset : {ω | c < |X s ω - X t ω|}
      ⊆ {ω | ENNReal.ofReal (c ^ β) ≤ ENNReal.ofReal (|X s ω - X t ω| ^ β)} := by
    intro ω hω
    have hω' : c < |X s ω - X t ω| := hω
    show ENNReal.ofReal (c ^ β) ≤ ENNReal.ofReal (|X s ω - X t ω| ^ β)
    rw [ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg (abs_nonneg _) β)]
    exact Real.rpow_le_rpow (le_of_lt hcpos) (le_of_lt hω') hβ.le
  calc μ {ω | c < |X s ω - X t ω|}
      ≤ μ {ω | ENNReal.ofReal (c ^ β) ≤ ENNReal.ofReal (|X s ω - X t ω| ^ β)} :=
        measure_mono hsubset
    _ ≤ (∫⁻ ω, ENNReal.ofReal (|X s ω - X t ω| ^ β) ∂μ) / ENNReal.ofReal (c ^ β) :=
        hmarkov
    _ = ENNReal.ofReal (∫ ω, |X s ω - X t ω| ^ β ∂μ) / ENNReal.ofReal (c ^ β) := by
        rw [hint]
    _ ≤ ENNReal.ofReal (K * ((2 : ℝ) ^ (-(m : ℝ))) ^ (1 + α)) / ENNReal.ofReal (c ^ β) := by
        rw [← ENNReal.ofReal_div_of_pos hcbpos, ← ENNReal.ofReal_div_of_pos hcbpos]
        exact ENNReal.ofReal_le_ofReal (by gcongr)
    _ = ENNReal.ofReal (K * ((2 : ℝ) ^ (-(m : ℝ))) ^ (1 + α)
        / ((2 : ℝ) ^ (-(m : ℝ) * γ)) ^ β) := by
        rw [← ENNReal.ofReal_div_of_pos hcbpos]

/-- The bad event at level `m` has small measure, by summing over the
`2^m` dyadic intervals. -/
private lemma measure_badDyadicSet_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ → Ω → ℝ} {α β K γ : ℝ}
    (hβ : 0 < β)
    (hX_int : ∀ s t : ℝ, Integrable (fun ω => |X s ω - X t ω| ^ β) μ)
    (hkolm : ∀ s t : ℝ, ∫ ω, |X s ω - X t ω| ^ β ∂μ ≤ K * |s - t| ^ (1 + α))
    (m : ℕ) :
    μ (badDyadicSet X γ m) ≤ ENNReal.ofReal (K * (2 : ℝ) ^ (-(m : ℝ) * (α - γ * β))) := by
  have h2 : ((2 ^ m : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ m) := by
    rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    norm_cast
  calc μ (badDyadicSet X γ m)
      ≤ ∑ k ∈ Finset.range (2 ^ m),
          μ {ω | (2 : ℝ) ^ (-(m : ℝ) * γ)
            < |X ((k + 1 : ℝ) / (2 : ℝ) ^ m) ω - X ((k : ℝ) / (2 : ℝ) ^ m) ω|} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.range (2 ^ m), ENNReal.ofReal (K * ((2 : ℝ) ^ (-(m : ℝ))) ^ (1 + α)
        / ((2 : ℝ) ^ (-(m : ℝ) * γ)) ^ β) :=
        Finset.sum_le_sum (fun k _ => measure_badDyadicInterval_le hβ hX_int hkolm m k)
    _ = ENNReal.ofReal (K * (2 : ℝ) ^ (-(m : ℝ) * (α - γ * β))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, h2,
          ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2 : ℝ) ^ m)]
        congr 1
        rw [show (2 : ℝ) ^ m * (K * ((2 : ℝ) ^ (-(m : ℝ))) ^ (1 + α)
              / ((2 : ℝ) ^ (-(m : ℝ) * γ)) ^ β)
            = K * ((2 : ℝ) ^ m * (((2 : ℝ) ^ (-(m : ℝ))) ^ (1 + α)
              / ((2 : ℝ) ^ (-(m : ℝ) * γ)) ^ β)) by ring,
          two_pow_mul_rpow_identity]

/-- The complement of the good set is covered by infinitely many bad
events, hence has measure zero. -/
private lemma goodSet_ae {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ → Ω → ℝ} {α β K γ : ℝ} (hβ : 0 < β) (_hγ : 0 < γ) (hK : 0 ≤ K)
    (hδ : 0 < α - γ * β)
    (hX_int : ∀ s t : ℝ, Integrable (fun ω => |X s ω - X t ω| ^ β) μ)
    (hkolm : ∀ s t : ℝ, ∫ ω, |X s ω - X t ω| ^ β ∂μ ≤ K * |s - t| ^ (1 + α)) :
    ∀ᵐ ω ∂μ, ω ∈ goodSet X γ := by
  have hsum : (∑' m : ℕ, μ (badDyadicSet X γ m)) ≠ ⊤ := by
    have hρ0 : (0:ℝ) ≤ (2 : ℝ) ^ (-(α - γ * β)) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    have hρ1 : (2 : ℝ) ^ (-(α - γ * β)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hge : ∀ m : ℕ, (2 : ℝ) ^ (-(m : ℝ) * (α - γ * β))
        = ((2 : ℝ) ^ (-(α - γ * β))) ^ m := by
      intro m
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(α - γ * β))) m,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1; ring
    have hsumK : Summable (fun m : ℕ => K * ((2 : ℝ) ^ (-(α - γ * β))) ^ m) :=
      (summable_geometric_of_lt_one hρ0 hρ1).mul_left K
    have hle : (∑' m : ℕ, μ (badDyadicSet X γ m))
        ≤ ∑' m : ℕ, ENNReal.ofReal (K * (2 : ℝ) ^ (-(m : ℝ) * (α - γ * β))) :=
      ENNReal.tsum_le_tsum (fun m => measure_badDyadicSet_le hβ hX_int hkolm m)
    have htsum : (∑' m : ℕ,
        ENNReal.ofReal (K * (2 : ℝ) ^ (-(m : ℝ) * (α - γ * β))))
        = ENNReal.ofReal (∑' m : ℕ, K * ((2 : ℝ) ^ (-(α - γ * β))) ^ m) := by
      have hcongr : (∑' m : ℕ,
          ENNReal.ofReal (K * (2 : ℝ) ^ (-(m : ℝ) * (α - γ * β))))
          = ∑' m : ℕ, ENNReal.ofReal (K * ((2 : ℝ) ^ (-(α - γ * β))) ^ m) :=
        tsum_congr (fun m => by rw [hge m])
      rw [hcongr, ENNReal.ofReal_tsum_of_nonneg
        (fun m => mul_nonneg hK (pow_nonneg
          (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _).le m)) hsumK]
    exact ne_top_of_le_ne_top (by rw [htsum]; exact ENNReal.ofReal_ne_top) hle
  have hlim : μ (Filter.limsup (badDyadicSet X γ) Filter.atTop) = 0 :=
    measure_limsup_atTop_eq_zero hsum
  rw [ae_iff]
  apply measure_mono_null _ hlim
  intro ω hω
  rw [Filter.mem_limsup_iff_frequently_mem]
  rw [Filter.frequently_atTop]
  have hω' : ∀ M : ℕ, ∃ m : ℕ, M ≤ m ∧ ω ∈ badDyadicSet X γ m := by
    simp only [goodSet, Set.mem_ofPred_eq] at hω
    push Not at hω
    intro M
    obtain ⟨m, hmM, k, hk, hlt⟩ := hω M
    exact ⟨m, hmM, Set.mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr hk, hlt⟩⟩
  intro M
  obtain ⟨m, hmM, hm⟩ := hω' M
  exact ⟨m, hmM, hm⟩

/-! ### Main theorem -/

/-- A single full-measure set carries a Hölder bound for the original process
on the dyadic rationals of `[0, 1]`. The moment-integrability correction in
the module docstring is required for this Bochner formulation. -/
theorem kolmogorov_ae_holder_on_dyadics {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℝ → Ω → ℝ} {α β K : ℝ} (_hα : 0 < α) (hβ : 0 < β)
    (hK : 0 ≤ K)
    (hX_int : ∀ s t : ℝ, Integrable (fun ω => |X s ω - X t ω| ^ β) μ)
    (hkolm : ∀ s t : ℝ, ∫ ω, |X s ω - X t ω| ^ β ∂μ ≤ K * |s - t| ^ (1 + α)) :
    ∀ γ : ℝ, γ < α / β → γ > 0 →
      ∀ᵐ ω ∂μ, ∃ C : ℝ, 0 < C ∧
        ∀ q r : ℝ, q ∈ dyadicRationals ∩ Set.Icc 0 1 →
          r ∈ dyadicRationals ∩ Set.Icc 0 1 →
          |X q ω - X r ω| ≤ C * |q - r| ^ γ := by
  intro γ hγα hγ0
  have hδ : 0 < α - γ * β := by
    have h : γ * β < α := by
      rw [lt_div_iff₀ hβ] at hγα
      linarith [hγα]
    linarith
  have hgood := goodSet_ae hβ hγ0 hK hδ hX_int hkolm
  filter_upwards [hgood] with ω hω
  obtain ⟨M, hM⟩ := hω
  -- The constant `D` dominates every dyadic increment, coercing the
  -- finitely many coarse increments by their sum.
  set D := (1 + ∑ m ∈ Finset.range M, ∑ k ∈ Finset.range (2 ^ m),
    |X ((k + 1 : ℝ) / (2 : ℝ) ^ m) ω - X ((k : ℝ) / (2 : ℝ) ^ m) ω|)
    * (2 : ℝ) ^ ((M : ℝ) * γ) with hDdef
  have hD1 : 1 ≤ D := by
    rw [hDdef]
    have h1 : (1:ℝ) ≤ 1 + ∑ m ∈ Finset.range M, ∑ k ∈ Finset.range (2 ^ m),
        |X ((k + 1 : ℝ) / (2 : ℝ) ^ m) ω - X ((k : ℝ) / (2 : ℝ) ^ m) ω| := by
      have : 0 ≤ ∑ m ∈ Finset.range M, ∑ k ∈ Finset.range (2 ^ m),
          |X ((k + 1 : ℝ) / (2 : ℝ) ^ m) ω - X ((k : ℝ) / (2 : ℝ) ^ m) ω| := by
        apply Finset.sum_nonneg
        intro m _
        exact Finset.sum_nonneg (fun k _ => abs_nonneg _)
      linarith
    have h2 : (1:ℝ) ≤ (2 : ℝ) ^ ((M : ℝ) * γ) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ _ := mul_le_mul h1 h2 (by norm_num) (by linarith)
  have hDpos : 0 < D := by linarith
  have hinc : ∀ m : ℕ, ∀ k : ℕ, k < 2 ^ m →
      |X ((k + 1 : ℝ) / (2 : ℝ) ^ m) ω - X ((k : ℝ) / (2 : ℝ) ^ m) ω|
        ≤ D * (2 : ℝ) ^ (-(m : ℝ) * γ) := by
    intro m k hk
    by_cases hmM : M ≤ m
    · calc |X ((k + 1 : ℝ) / (2 : ℝ) ^ m) ω - X ((k : ℝ) / (2 : ℝ) ^ m) ω|
          ≤ (2 : ℝ) ^ (-(m : ℝ) * γ) := hM m hmM k hk
        _ ≤ D * (2 : ℝ) ^ (-(m : ℝ) * γ) := by
            have : (0:ℝ) ≤ (2 : ℝ) ^ (-(m : ℝ) * γ) :=
              (Real.rpow_pos_of_pos (by norm_num) _).le
            calc (2 : ℝ) ^ (-(m : ℝ) * γ) = 1 * (2 : ℝ) ^ (-(m : ℝ) * γ) := by ring
              _ ≤ D * (2 : ℝ) ^ (-(m : ℝ) * γ) :=
                  mul_le_mul_of_nonneg_right hD1 this
    · have hmM' : m < M := Nat.lt_of_not_le hmM
      have hterm : |X ((k + 1 : ℝ) / (2 : ℝ) ^ m) ω - X ((k : ℝ) / (2 : ℝ) ^ m) ω|
          ≤ 1 + ∑ m' ∈ Finset.range M, ∑ k' ∈ Finset.range (2 ^ m'),
            |X ((k' + 1 : ℝ) / (2 : ℝ) ^ m') ω - X ((k' : ℝ) / (2 : ℝ) ^ m') ω| := by
        have h1 := Finset.single_le_sum (f := fun m' => ∑ k' ∈ Finset.range (2 ^ m'),
            |X ((k' + 1 : ℝ) / (2 : ℝ) ^ m') ω - X ((k' : ℝ) / (2 : ℝ) ^ m') ω|)
          (s := Finset.range M)
          (fun m' _ => Finset.sum_nonneg (fun k' _ => abs_nonneg _))
          (Finset.mem_range.mpr hmM')
        have h2 : |X ((k + 1 : ℝ) / (2 : ℝ) ^ m) ω - X ((k : ℝ) / (2 : ℝ) ^ m) ω|
            ≤ ∑ k' ∈ Finset.range (2 ^ m),
              |X ((k' + 1 : ℝ) / (2 : ℝ) ^ m) ω - X ((k' : ℝ) / (2 : ℝ) ^ m) ω| :=
          Finset.single_le_sum (f := fun (k' : ℕ) =>
            |X (((k' : ℝ) + 1) / (2 : ℝ) ^ m) ω - X ((k' : ℝ) / (2 : ℝ) ^ m) ω|)
            (s := Finset.range (2 ^ m)) (a := k)
            (fun k' _ => abs_nonneg _) (Finset.mem_range.mpr hk)
        linarith
      have hfactor : (1:ℝ) ≤ (2 : ℝ) ^ ((M : ℝ) * γ) * (2 : ℝ) ^ (-(m : ℝ) * γ) := by
        have : (2 : ℝ) ^ ((M : ℝ) * γ) * (2 : ℝ) ^ (-(m : ℝ) * γ)
            = (2 : ℝ) ^ (((M : ℝ) - (m : ℝ)) * γ) := by
          rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
          congr 1; ring
        rw [this]
        exact Real.one_le_rpow (by norm_num) (mul_nonneg
          (by
            have h : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM'.le
            linarith) hγ0.le)
      calc |X ((k + 1 : ℝ) / (2 : ℝ) ^ m) ω - X ((k : ℝ) / (2 : ℝ) ^ m) ω|
          ≤ 1 + ∑ m' ∈ Finset.range M, ∑ k' ∈ Finset.range (2 ^ m'),
            |X ((k' + 1 : ℝ) / (2 : ℝ) ^ m') ω - X ((k' : ℝ) / (2 : ℝ) ^ m') ω| := hterm
        _ ≤ D * (2 : ℝ) ^ (-(m : ℝ) * γ) := by
            rw [hDdef]
            have hnn : 0 ≤ 1 + ∑ m' ∈ Finset.range M, ∑ k' ∈ Finset.range (2 ^ m'),
                |X ((k' + 1 : ℝ) / (2 : ℝ) ^ m') ω - X ((k' : ℝ) / (2 : ℝ) ^ m') ω| := by
              have : 0 ≤ ∑ m' ∈ Finset.range M, ∑ k' ∈ Finset.range (2 ^ m'),
                  |X ((k' + 1 : ℝ) / (2 : ℝ) ^ m') ω - X ((k' : ℝ) / (2 : ℝ) ^ m') ω| := by
                apply Finset.sum_nonneg
                intro m' _
                exact Finset.sum_nonneg (fun k' _ => abs_nonneg _)
              linarith
            calc 1 + ∑ m' ∈ Finset.range M, ∑ k' ∈ Finset.range (2 ^ m'),
                  |X ((k' + 1 : ℝ) / (2 : ℝ) ^ m') ω - X ((k' : ℝ) / (2 : ℝ) ^ m') ω|
                = (1 + ∑ m' ∈ Finset.range M, ∑ k' ∈ Finset.range (2 ^ m'),
                  |X ((k' + 1 : ℝ) / (2 : ℝ) ^ m') ω - X ((k' : ℝ) / (2 : ℝ) ^ m') ω|) * 1 := by
                  ring
              _ ≤ (1 + ∑ m' ∈ Finset.range M, ∑ k' ∈ Finset.range (2 ^ m'),
                  |X ((k' + 1 : ℝ) / (2 : ℝ) ^ m') ω - X ((k' : ℝ) / (2 : ℝ) ^ m') ω|)
                  * ((2 : ℝ) ^ ((M : ℝ) * γ) * (2 : ℝ) ^ (-(m : ℝ) * γ)) :=
                  mul_le_mul_of_nonneg_left hfactor hnn
              _ = _ := by ring
  refine ⟨D * (4 + 2 * (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ))), ?_, ?_⟩
  · have hρ1 : (2 : ℝ) ^ (-γ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have h2 : 0 < 2 * (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ)) := by
      apply div_pos _ (by linarith)
      have : 0 < (2 : ℝ) ^ (-γ) := Real.rpow_pos_of_pos (by norm_num) _
      linarith
    exact mul_pos hDpos (by linarith [h2])
  · intro q r hq hr
    exact dyadic_holder_of_increment_bound (f := fun t => X t ω) hγ0 hDpos hinc hq hr

/-- **Kolmogorov continuity theorem**, in the original modification formulation.
The direct dyadic bound permits choosing `Y = X`. See the module docstring for
the necessary moment-integrability correction to the archived v1 statement. -/
theorem kolmogorov_continuity_theorem {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℝ → Ω → ℝ} {α β K : ℝ} (_hα : 0 < α) (hβ : 0 < β)
    (hK : 0 ≤ K)
    (hX_int : ∀ s t : ℝ, Integrable (fun ω => |X s ω - X t ω| ^ β) μ)
    (hkolm : ∀ s t : ℝ, ∫ ω, |X s ω - X t ω| ^ β ∂μ ≤ K * |s - t| ^ (1 + α)) :
    ∀ γ : ℝ, γ < α / β → γ > 0 →
      ∃ Y : ℝ → Ω → ℝ,
        (∀ t, ∀ᵐ ω ∂μ, Y t ω = X t ω) ∧
        (∀ᵐ ω ∂μ, ∃ C : ℝ, 0 < C ∧
          ∀ q r : ℝ, q ∈ dyadicRationals ∩ Set.Icc 0 1 →
            r ∈ dyadicRationals ∩ Set.Icc 0 1 →
            |Y q ω - Y r ω| ≤ C * |q - r| ^ γ) := by
  intro γ hγα hγ0
  refine ⟨X, ?_, kolmogorov_ae_holder_on_dyadics _hα hβ hK hX_int hkolm γ hγα hγ0⟩
  intro t
  exact Filter.Eventually.of_forall (fun ω => rfl)

private theorem kolmogorov_integrable_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : ℝ → Ω → ℝ} {β q : ℝ} {M : NNReal}
    (hX : ProbabilityTheory.IsKolmogorovProcess X μ β q M) (s t : ℝ) :
    Integrable (fun ω => |X s ω - X t ω| ^ β) μ := by
  have hfin : (∫⁻ ω, edist (X s ω) (X t ω) ^ β ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top
        (ENNReal.rpow_ne_top_of_nonneg hX.q_pos.le (edist_ne_top s t)))
      (hX.kolmogorovCondition s t)
  have hint := integrable_toReal_of_lintegral_ne_top
    (hX.measurable_edist.pow_const β).aemeasurable hfin
  convert hint using 1
  funext ω
  rw [← ENNReal.toReal_rpow, edist_dist, Real.dist_eq,
    ENNReal.toReal_ofReal (abs_nonneg _)]

private theorem kolmogorov_integral_moment_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : ℝ → Ω → ℝ} {β q : ℝ} {M : NNReal}
    (hX : ProbabilityTheory.IsKolmogorovProcess X μ β q M) (s t : ℝ) :
    ∫ ω, |X s ω - X t ω| ^ β ∂μ ≤ (M : ℝ) * |s - t| ^ q := by
  have hi := kolmogorov_integrable_moment hX s t
  have hn : ∀ ω, 0 ≤ |X s ω - X t ω| ^ β := fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have he : ∀ ω, ENNReal.ofReal (|X s ω - X t ω| ^ β) =
      edist (X s ω) (X t ω) ^ β := by
    intro ω
    rw [edist_dist, Real.dist_eq,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hX.p_pos.le]
  have hb : (M : ENNReal) * edist s t ^ q =
      ENNReal.ofReal ((M : ℝ) * |s - t| ^ q) := by
    rw [edist_dist, Real.dist_eq,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hX.q_pos.le]
    simpa only [ENNReal.ofReal_coe_nnreal] using
      (show ENNReal.ofReal ((M : ℝ) * |s - t| ^ q) =
          ENNReal.ofReal (M : ℝ) * ENNReal.ofReal (|s - t| ^ q) from
        ENNReal.ofReal_mul M.property).symm
  have hle : ENNReal.ofReal (∫ ω, |X s ω - X t ω| ^ β ∂μ) ≤
      ENNReal.ofReal ((M : ℝ) * |s - t| ^ q) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)]
    simp_rw [he]
    rw [← hb]
    exact hX.kolmogorovCondition s t
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg M.property
    (Real.rpow_nonneg (abs_nonneg _) _))).mp hle


/-- The canonical Kolmogorov-process condition implies a common a.e. Hölder
bound for `X` on the dyadics of `[0, 1]`. Its measurable-pair and finite
lintegral fields supply the Bochner hypotheses internally, including when
`M = 0`. No claim is made about the raw paths at every real time. -/
theorem kolmogorov_ae_holder_on_dyadics_of_isKolmogorovProcess
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ → Ω → ℝ} {α β : ℝ} {M : NNReal} (hα : 0 < α)
    (hX : ProbabilityTheory.IsKolmogorovProcess X μ β (1 + α) M) :
    ∀ γ : ℝ, γ < α / β → γ > 0 →
      ∀ᵐ ω ∂μ, ∃ C : ℝ, 0 < C ∧
        ∀ q r : ℝ, q ∈ dyadicRationals ∩ Set.Icc 0 1 →
          r ∈ dyadicRationals ∩ Set.Icc 0 1 →
          |X q ω - X r ω| ≤ C * |q - r| ^ γ :=
  kolmogorov_ae_holder_on_dyadics hα hX.p_pos M.property
    (kolmogorov_integrable_moment hX) (kolmogorov_integral_moment_le hX)

end MathlibExt.Probability.KolmogorovContinuity
