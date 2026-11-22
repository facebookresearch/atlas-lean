/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Matrix.Mul

namespace MetaMathlibExt

@[expose] public section

open Polynomial

/-- For positive integers `k₁, k₂, p, s` with `p ≥ 2`, `k₁² < k₂` and `p < s`, the characteristic
polynomial `P(z) = z^{s+p} - k₁ z^p - k₂` of the `([k]; p; s)`-generalized Padovan–Perrin
recurrence has only simple roots (stated as separability over `ℂ`; `k₂ > 0` and `s > 0` follow
from the other hypotheses).

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Lemma 4 (`integers-2024-A49-lem-4`). -/
public theorem_wanted padovanPerrin_charPoly_separable (k₁ k₂ p s : ℕ) (hk₁ : 0 < k₁)
    (hp : 2 ≤ p) (hps : p < s) (hk : k₁ ^ 2 < k₂) :
    (X ^ (s + p) - C (k₁ : ℂ) * X ^ p - C (k₂ : ℂ)).Separable

section Model

variable {R : Type*}

/-- The `([k]; p; s)`-generalized Padovan–Perrin recurrence of order `s + p`,
`v n = k₁ v (n - s) + k₂ v (n - s - p)` for `n ≥ s + p` (equation (1)), as a Mathlib
`LinearRecurrence`: `v (n + (s + p)) = k₂ v n + k₁ v (n + p)`.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, equation (1). -/
def padovanPerrinRecurrence [CommSemiring R] (k₁ k₂ : R) (p s : ℕ) : LinearRecurrence R :=
  ⟨s + p, fun i => (if (i : ℕ) = 0 then k₂ else 0) + (if (i : ℕ) = p then k₁ else 0)⟩

/-- For `s > 0`, a sequence solves the `([k]; p; s)`-Padovan–Perrin recurrence exactly when
`v (n + (s + p)) = k₁ v (n + p) + k₂ v n` for every `n`.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, equation (1). -/
theorem padovanPerrinRecurrence_isSolution_iff [CommSemiring R] (k₁ k₂ : R) (p s : ℕ)
    (hs : 0 < s) (v : ℕ → R) :
    (padovanPerrinRecurrence k₁ k₂ p s).IsSolution v ↔
      ∀ n, v (n + (s + p)) = k₁ * v (n + p) + k₂ * v n := by
  unfold LinearRecurrence.IsSolution
  refine forall_congr' fun n => ?_
  have key : ∑ i : Fin (padovanPerrinRecurrence k₁ k₂ p s).order,
      (padovanPerrinRecurrence k₁ k₂ p s).coeffs i * v (n + i) = k₁ * v (n + p) + k₂ * v n := by
    change ∑ i : Fin (s + p),
      ((if (i : ℕ) = 0 then k₂ else 0) + (if (i : ℕ) = p then k₁ else 0)) * v (n + i) = _
    rw [Fin.sum_univ_eq_sum_range
      (fun i => ((if i = 0 then k₂ else 0) + (if i = p then k₁ else 0)) * v (n + i)) (s + p)]
    simp [add_mul, Finset.sum_add_distrib, hs, add_comm]
  rw [key]
  exact Iff.rfl

/-- The Fibonacci fundamental system of the `([k]; p; s)`-Padovan–Perrin model (equation (2)):
`padovanPerrinFundamental k₁ k₂ p s j` is the solution `v⁽ʲ⁾` of the recurrence with initial
values `v⁽ʲ⁾ n = 1` if `n + 1 = j` and `0` otherwise, for `0 ≤ n < s + p`.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, equation (2) and Definition 1. -/
def padovanPerrinFundamental [CommSemiring R] (k₁ k₂ : R) (p s j : ℕ) : ℕ → R :=
  (padovanPerrinRecurrence k₁ k₂ p s).mkSol fun i => if (i : ℕ) + 1 = j then 1 else 0

/-- Initial values of the Fibonacci fundamental system: `v⁽ʲ⁾ n = δ_{n+1, j}` for `n < s + p`.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, equation (2). -/
theorem padovanPerrinFundamental_of_lt [CommSemiring R] (k₁ k₂ : R) (p s j n : ℕ)
    (hn : n < s + p) :
    padovanPerrinFundamental k₁ k₂ p s j n = if n + 1 = j then 1 else 0 :=
  (padovanPerrinRecurrence k₁ k₂ p s).mkSol_eq_init _ ⟨n, hn⟩

/-- Each member of the Fibonacci fundamental system solves the Padovan–Perrin recurrence.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, equation (2). -/
theorem padovanPerrinFundamental_isSolution [CommSemiring R] (k₁ k₂ : R) (p s j : ℕ) :
    (padovanPerrinRecurrence k₁ k₂ p s).IsSolution (padovanPerrinFundamental k₁ k₂ p s j) :=
  (padovanPerrinRecurrence k₁ k₂ p s).is_sol_mkSol _

/-- The combinatorial coefficient `ρ(n, s + p)` of equation (12) specialized to the
`([k]; p; s)`-Padovan–Perrin model: `0` for `n < s + p`, and for `n ≥ s + p` the sum of
`(a + b)! / (a! b!) · k₁^a k₂^b` over `a, b ≥ 0` with `s a + (s + p) b = n - (s + p)`. The paper's
Proposition 4 prints the constraint as `= n - (s + p - 1)`, which contradicts its own normalization
`ρ(s + p, s + p) = 1` for `s ≥ 2`; the constraint used here is the one of the general formula (12)
(`t₀ + 2 t₁ + ⋯ + r t_{r-1} = n - r` with only `t_{s-1}, t_{s+p-1}` weighted). Meant for `s > 0`.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, equation (12) and Proposition 4. -/
def padovanPerrinRho [CommSemiring R] (k₁ k₂ : R) (p s n : ℕ) : R :=
  if n < s + p then 0 else
    ∑ ab ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun ab => s * ab.1 + (s + p) * ab.2 = n - (s + p)),
      (Nat.choose (ab.1 + ab.2) ab.1 : R) * k₁ ^ ab.1 * k₂ ^ ab.2

/-- `ρ(n, s + p) = 0` for `n < s + p`.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 4. -/
theorem padovanPerrinRho_of_lt [CommSemiring R] (k₁ k₂ : R) (p s n : ℕ) (hn : n < s + p) :
    padovanPerrinRho k₁ k₂ p s n = 0 := by
  simp [padovanPerrinRho, hn]

/-- `ρ(s + p, s + p) = 1` for `s > 0`.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 4. -/
theorem padovanPerrinRho_self [CommSemiring R] (k₁ k₂ : R) (p s : ℕ) (hs : 0 < s) :
    padovanPerrinRho k₁ k₂ p s (s + p) = 1 := by
  rw [padovanPerrinRho, Nat.sub_self]
  simp only [lt_irrefl, ↓reduceIte]
  rw [Finset.sum_eq_single (0, 0)]
  · simp
  · rintro ⟨a, b⟩ hab hne
    simp only [Finset.mem_filter] at hab
    exfalso
    apply hne
    have ha : a = 0 := by
      rcases Nat.eq_zero_or_pos a with h | h
      · exact h
      · nlinarith [hab.2]
    have hb : b = 0 := by
      rcases Nat.eq_zero_or_pos b with h | h
      · exact h
      · nlinarith [hab.2]
    simp [ha, hb]
  · intro h
    exfalso
    apply h
    simp

/-- The characteristic recurrence of `ρ(n, s + p)` for `s > 0`:
`ρ(n + (s + p) + 1, s + p) = k₁ ρ(n + p + 1, s + p) + k₂ ρ(n + 1, s + p)`, i.e.
`ρ(m) = k₁ ρ(m - s) + k₂ ρ(m - s - p)` for `m > s + p`. Together with `padovanPerrinRho_of_lt` and
`padovanPerrinRho_self` it determines `ρ`.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, equation (12) and Proposition 4. -/
theorem padovanPerrinRho_add_succ [CommSemiring R] (k₁ k₂ : R) (p s n : ℕ) (hs : 0 < s) :
    padovanPerrinRho k₁ k₂ p s (n + (s + p) + 1) =
      k₁ * padovanPerrinRho k₁ k₂ p s (n + p + 1) + k₂ * padovanPerrinRho k₁ k₂ p s (n + 1) := by
  set r := s + p with hr
  have hr1 : 0 < r := by omega
  let c : ℕ → ℕ → R := fun a b => (Nat.choose (a + b) a : R) * k₁ ^ a * k₂ ^ b
  let box : ℕ → ℕ → ℕ → R := fun A B m =>
    ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B, if s * a + r * b = m then c a b else 0
  have hrho : ∀ N, r ≤ N → padovanPerrinRho k₁ k₂ p s N = box (N + 1) (N + 1) (N - r) := by
    intro N hN
    simp only [padovanPerrinRho, ← hr, not_lt.2 hN, ite_false, box, c]
    rw [Finset.sum_filter, Finset.sum_product]
  have hbox : ∀ A B m, m < A → m < B → box A B m = box (m + 1) (m + 1) m := by
    intro A B m hA hB
    have inner : ∀ a, (∑ b ∈ Finset.range B, if s * a + r * b = m then c a b else 0) =
        ∑ b ∈ Finset.range (m + 1), if s * a + r * b = m then c a b else 0 := by
      intro a
      symm
      apply Finset.sum_subset (Finset.range_subset_range.2 hB)
      intro b _ hb
      simp only [Finset.mem_range, not_lt] at hb
      rw [ite_eq_right_iff]
      intro h
      exfalso
      nlinarith
    simp only [box, inner]
    symm
    apply Finset.sum_subset (Finset.range_subset_range.2 hA)
    intro a _ ha
    simp only [Finset.mem_range, not_lt] at ha
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right_iff]
    intro h
    exfalso
    nlinarith
  have pascal : ∀ a b, a + b ≠ 0 → c a b =
      (if 0 < a then k₁ * c (a - 1) b else 0) + (if 0 < b then k₂ * c a (b - 1) else 0) := by
    intro a b hab
    rcases a with _ | a <;> rcases b with _ | b
    · simp at hab
    · simp [c, pow_succ]
      ring
    · simp [c, pow_succ]
      ring
    · have e1 : a + 1 + (b + 1) = (a + b + 1) + 1 := by omega
      have e2 : a + 1 + b = a + b + 1 := by omega
      have e3 : a + (b + 1) = a + b + 1 := by omega
      simp only [c, e1, e2, e3, Nat.choose_succ_succ, Nat.cast_add, Nat.succ_pos, ite_true,
        Nat.add_sub_cancel, pow_succ]
      ring
  have step : ∀ M m, box (M + 1) (M + 1) (m + 1) =
      k₁ * (if s ≤ m + 1 then box M (M + 1) (m + 1 - s) else 0) +
        k₂ * (if r ≤ m + 1 then box (M + 1) M (m + 1 - r) else 0) := by
    intro M m
    have e : ∀ a b, (if s * a + r * b = m + 1 then c a b else 0) =
        (if s * a + r * b = m + 1 then (if 0 < a then k₁ * c (a - 1) b else 0) else 0) +
        (if s * a + r * b = m + 1 then (if 0 < b then k₂ * c a (b - 1) else 0) else 0) := by
      intro a b
      by_cases h : s * a + r * b = m + 1
      · simp only [h, ite_true]
        apply pascal
        intro h0
        obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
        simp at h
      · simp [h]
    have part1 : (∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1),
        if s * a + r * b = m + 1 then (if 0 < a then k₁ * c (a - 1) b else 0) else 0) =
        k₁ * (if s ≤ m + 1 then box M (M + 1) (m + 1 - s) else 0) := by
      rw [Finset.sum_range_succ']
      simp only [lt_irrefl, ite_false, ite_self, Finset.sum_const_zero, add_zero, Nat.succ_pos,
        ite_true, Nat.add_sub_cancel]
      split_ifs with hsm
      · simp only [box, Finset.mul_sum, mul_ite, mul_zero]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        have : s * (a + 1) + r * b = (s * a + r * b) + s := by ring
        rw [this]
        congr 1
        apply propext
        omega
      · rw [mul_zero]
        refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
        rw [ite_eq_right_iff]
        intro h
        exfalso
        nlinarith
    have part2 : (∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1),
        if s * a + r * b = m + 1 then (if 0 < b then k₂ * c a (b - 1) else 0) else 0) =
        k₂ * (if r ≤ m + 1 then box (M + 1) M (m + 1 - r) else 0) := by
      refine (Finset.sum_congr rfl fun a _ => Finset.sum_range_succ' _ _).trans ?_
      simp only [lt_irrefl, ite_false, ite_self, add_zero, Nat.succ_pos,
        ite_true, Nat.add_sub_cancel]
      split_ifs with hrm
      · simp only [box, Finset.mul_sum, mul_ite, mul_zero]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        have : s * a + r * (b + 1) = (s * a + r * b) + r := by ring
        rw [this]
        congr 1
        apply propext
        omega
      · rw [mul_zero]
        refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
        rw [ite_eq_right_iff]
        intro h
        exfalso
        nlinarith
    simp only [box]
    simp_rw [e, Finset.sum_add_distrib]
    rw [part1, part2]
  -- assemble
  rw [hrho _ (by omega)]
  have h1 : n + r + 1 - r = n + 1 := by omega
  rw [h1, step]
  congr 1
  · by_cases hsn : s ≤ n + 1
    · have h2 : n + p + 1 - r = n + 1 - s := by omega
      simp only [hsn, ite_true]
      rw [hrho _ (by omega), h2,
        hbox _ _ _ (by omega) (by omega), hbox (n + p + 1 + 1) _ _ (by omega) (by omega)]
    · simp only [hsn, ite_false, mul_zero, padovanPerrinRho,
        show n + p + 1 < s + p by omega, ite_true]
  · by_cases hrn : r ≤ n + 1
    · simp only [hrn, ite_true]
      rw [hrho _ hrn, hbox _ _ _ (by omega) (by omega),
        hbox (n + 1 + 1) _ _ (by omega) (by omega)]
    · simp only [hrn, ite_false, mul_zero, padovanPerrinRho,
        show n + 1 < s + p by omega, ite_true]

/-- A value check: for the Padovan–Perrin case `k₁ = k₂ = 1`, `p = 1`, `s = 2`,
`ρ(12, 3) = 5` (`= v⁽³⁾₁₁` in the paper's Table 1).

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, equation (14) and Table 1. -/
theorem padovanPerrinRho_one_one_one_two_twelve : padovanPerrinRho (1 : ℤ) 1 1 2 12 = 5 := by
  decide

/-- Every solution of the `([k]; p; s)`-Padovan–Perrin recurrence with initial values
`α_j = v j` satisfies `v n = ∑_{j=0}^{s+p-1} α_j v⁽ʲ⁺¹⁾ n` for every `n ≥ 0`. Stated over any
commutative ring instead of `ℝ`.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 1 (`integers-2024-A49-prop-1`). -/
public theorem_wanted padovanPerrin_eq_sum_fundamental [CommRing R] (k₁ k₂ : R) (p s : ℕ)
    (v : ℕ → R)
    (hv : (padovanPerrinRecurrence k₁ k₂ p s).IsSolution v) (n : ℕ) :
    v n = ∑ j ∈ Finset.range (s + p), v j * padovanPerrinFundamental k₁ k₂ p s (j + 1) n

/-- If two solutions `v, w` of the `([k]; p; s)`-Padovan–Perrin recurrence satisfy
`v (j + n₀) = w (j + m₀)` on a window `N ≤ j ≤ N + s + p - 1` of length the order, then
`v (n + n₀) = w (n + m₀)` for every `n ≥ N`. Stated over any commutative ring.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Lemma 1 (`integers-2024-A49-lem-1`). -/
public theorem_wanted padovanPerrin_shift_eq_of_window [CommRing R] (k₁ k₂ : R) (p s : ℕ)
    {v w : ℕ → R}
    (hv : (padovanPerrinRecurrence k₁ k₂ p s).IsSolution v)
    (hw : (padovanPerrinRecurrence k₁ k₂ p s).IsSolution w) (n₀ m₀ N : ℕ)
    (h : ∀ j, N ≤ j → j < N + (s + p) → v (j + n₀) = w (j + m₀)) :
    ∀ n, N ≤ n → v (n + n₀) = w (n + m₀)

/-- The solutions of the `([k]; p; s)`-Padovan–Perrin recurrence form a module (Mathlib's
`solSpace`), and the Fibonacci fundamental system `v⁽¹⁾, …, v⁽ˢ⁺ᵖ⁾` spans it. Stated over any
commutative ring instead of `ℝ`.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Corollary 1 (`integers-2024-A49-cor-1`). -/
public theorem_wanted padovanPerrin_solSpace_eq_span_fundamental [CommRing R] (k₁ k₂ : R)
    (p s : ℕ) :
    (padovanPerrinRecurrence k₁ k₂ p s).solSpace =
      Submodule.span R
        (Set.range fun j : Fin (s + p) => padovanPerrinFundamental k₁ k₂ p s ((j : ℕ) + 1))

/-- For `p + 1 ≤ j ≤ s + p - 1`, the fundamental sequence `v⁽ʲ⁾` is a shift of the fundamental
solution `v⁽ˢ⁺ᵖ⁾`: `v⁽ʲ⁾ n = v⁽ˢ⁺ᵖ⁾ (n + (s + p) - j)` for all `n ≥ 0`, and
`v⁽ʲ⁾ n = k₁ v⁽ˢ⁺ᵖ⁾ (n - j + p) + k₂ v⁽ˢ⁺ᵖ⁾ (n - j)` for `n ≥ j` (where both indices are
nonnegative). The paper's second clause `v⁽ʲ⁾ n = k₂ v⁽ˢ⁺ᵖ⁾ (n + j)` for `1 ≤ j ≤ p` is omitted:
it fails for `k₁ = k₂ = 1`, `p = 1`, `s = 2`, `j = 1`, `n = 0` (`v⁽¹⁾ 0 = 1`, `v⁽³⁾ 1 = 0`).
Stated over any commutative ring.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 2 (`integers-2024-A49-prop-2`). -/
public theorem_wanted padovanPerrinFundamental_eq_shift [CommRing R] (k₁ k₂ : R) (p s j : ℕ)
    (hp : 0 < p) (hpj : p + 1 ≤ j) (hjs : j ≤ s + p - 1) :
    (∀ n, padovanPerrinFundamental k₁ k₂ p s j n =
        padovanPerrinFundamental k₁ k₂ p s (s + p) (n + (s + p) - j)) ∧
      ∀ n, j ≤ n → padovanPerrinFundamental k₁ k₂ p s j n =
        k₁ * padovanPerrinFundamental k₁ k₂ p s (s + p) (n - j + p) +
          k₂ * padovanPerrinFundamental k₁ k₂ p s (s + p) (n - j)

/-- The powers of the companion matrix `A([k]; p; s)` of order `s + p` (first row `k₁` in
column `s` and `k₂` in column `s + p`, ones on the subdiagonal) have entries
`(Aⁿ)_{ij} = v⁽ˢ⁺ᵖ⁻ʲ⁺¹⁾ (n + s + p - i)` for `1 ≤ i, j ≤ s + p`; with the `0`-based indices of
`Fin (s + p)` this reads `(Aⁿ) i j = v⁽ˢ⁺ᵖ⁻ʲ⁾ (n + (s + p) - 1 - i)`. Stated over any commutative
ring.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Theorem 1, equations (5) and (9) (`integers-2024-A49-thm-1`). -/
public theorem_wanted padovanPerrin_companion_pow_apply [CommRing R] (k₁ k₂ : R) (p s : ℕ)
    (hp : 0 < p) (hs : 0 < s) (n : ℕ) (i j : Fin (s + p)) :
    ((Matrix.of fun a b : Fin (s + p) =>
        if (a : ℕ) = 0 then
          (if (b : ℕ) + 1 = s then k₁ else 0) + (if (b : ℕ) + 1 = s + p then k₂ else 0)
        else if (a : ℕ) = (b : ℕ) + 1 then 1 else 0) ^ n) i j =
      padovanPerrinFundamental k₁ k₂ p s (s + p - j) (n + (s + p) - 1 - i)

/-- Product identity of the Fibonacci fundamental system: for `m, n ≥ 0` and
`1 ≤ i, j ≤ s + p`,
`v⁽ˢ⁺ᵖ⁻ʲ⁺¹⁾ (n + m + s + p - i) = ∑_{k=1}^{s+p} v⁽ˢ⁺ᵖ⁻ᵏ⁺¹⁾ (m + s + p - i) v⁽ˢ⁺ᵖ⁻ʲ⁺¹⁾ (n + s + p - k)`.
Stated over any commutative ring.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 3, equation (10) (`integers-2024-A49-prop-3`). -/
public theorem_wanted padovanPerrinFundamental_mul_sum [CommRing R] (k₁ k₂ : R) (p s : ℕ)
    (hp : 0 < p) (hs : 0 < s) (m n i j : ℕ) (hi : 1 ≤ i) (hi' : i ≤ s + p) (hj : 1 ≤ j)
    (hj' : j ≤ s + p) :
    padovanPerrinFundamental k₁ k₂ p s (s + p - j + 1) (n + m + (s + p) - i) =
      ∑ k ∈ Finset.Icc 1 (s + p),
        padovanPerrinFundamental k₁ k₂ p s (s + p - k + 1) (m + (s + p) - i) *
          padovanPerrinFundamental k₁ k₂ p s (s + p - j + 1) (n + (s + p) - k)

/-- Combinatorial expression of the `([k]; p; s)`-Padovan–Perrin sequences: for every solution
`v` with initial values `α_j = v j` and every `n ≥ s + p`,
`v n = ∑_{m=0}^{s+p-1} ρ(n - m, s + p) A_m` with `A_m = k₂ α_m + k₁ α_{m+p}` for `m ≤ s - 1` and
`A_m = k₂ α_m` for `s ≤ m ≤ s + p - 1`. Here `ρ` is `padovanPerrinRho`, whose constraint
`s a + (s + p) b = n - (s + p)` follows the general formula (12); with the printed constraint
`= n - (s + p - 1)` the identity fails (for `k₁ = k₂ = 1`, `p = 1`, `s = 2` the printed `ρ(4, 3)`
is `1` instead of `0`). Stated over any commutative ring.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Theorem 3 (`integers-2024-A49-thm-3`). -/
public theorem_wanted padovanPerrin_eq_sum_rho [CommRing R] (k₁ k₂ : R) (p s : ℕ) (hp : 0 < p)
    (hs : 0 < s) (v : ℕ → R) (hv : (padovanPerrinRecurrence k₁ k₂ p s).IsSolution v) (n : ℕ)
    (hn : s + p ≤ n) :
    v n = ∑ m ∈ Finset.range (s + p), padovanPerrinRho k₁ k₂ p s (n - m) *
      (k₂ * v m + if m < s then k₁ * v (m + p) else 0)

/-- The Fibonacci fundamental solution is a shifted `ρ`: `v⁽ˢ⁺ᵖ⁾ n = ρ(n + 1, s + p)` for
`n ≥ s + p`, with `ρ` as in `padovanPerrinRho` (constraint `s a + (s + p) b = n - (s + p)` of
formula (12); the printed `n - (s + p - 1)` fails, e.g. `k₁ = k₂ = 1`, `p = 1`, `s = 2`, `n = 3`:
`v⁽³⁾ 3 = 0` while the printed `ρ(4, 3) = 1`). Stated over any commutative ring.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 4 (`integers-2024-A49-prop-4`). -/
public theorem_wanted padovanPerrinFundamental_last_eq_rho [CommRing R] (k₁ k₂ : R) (p s : ℕ)
    (hp : 0 < p) (hs : 0 < s) (n : ℕ) (hn : s + p ≤ n) :
    padovanPerrinFundamental k₁ k₂ p s (s + p) n = padovanPerrinRho k₁ k₂ p s (n + 1)

/-- For `p + 1 ≤ j ≤ s + p - 1` and every `n ≥ 0`,
`v⁽ʲ⁾ n = v⁽ˢ⁺ᵖ⁾ (n + (s + p) - j) = ρ(n + (s + p) - j + 1, s + p)`, with `ρ` as in
`padovanPerrinRho`. The paper's second clause `v⁽ʲ⁾ n = k₂ ρ(n + j + 1, s + p)` for `1 ≤ j ≤ p` is
omitted: it fails for `k₁ = 1`, `k₂ = 2`, `p = 1`, `s = 2`, `j = 1`, `n = 0` (`v⁽¹⁾ 0 = 1`,
`2 ρ(2, 3) = 0`). Stated over any commutative ring.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 5 (`integers-2024-A49-prop-5`). -/
public theorem_wanted padovanPerrinFundamental_eq_rho [CommRing R] (k₁ k₂ : R) (p s j : ℕ)
    (hp : 0 < p) (hpj : p + 1 ≤ j) (hjs : j ≤ s + p - 1) (n : ℕ) :
    padovanPerrinFundamental k₁ k₂ p s j n =
        padovanPerrinFundamental k₁ k₂ p s (s + p) (n + (s + p) - j) ∧
      padovanPerrinFundamental k₁ k₂ p s (s + p) (n + (s + p) - j) =
        padovanPerrinRho k₁ k₂ p s (n + (s + p) - j + 1)

/-- For positive integers `k₁, k₂, s` and `p = 1`, if
`(-k₂ (s + 1) / (k₁ s))^s ≠ k₁ / (s + 1)` then `P(z) = z^{s+1} - k₁ z - k₂` has only simple roots
(stated as separability over `ℂ`).

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Lemma 2 (`integers-2024-A49-lem-2`). -/
public theorem_wanted padovanPerrin_charPoly_separable_of_p_eq_one (k₁ k₂ s : ℕ) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hs : 0 < s)
    (h : (-(k₂ : ℚ) * (s + 1) / (k₁ * s)) ^ s ≠ k₁ / (s + 1)) :
    (X ^ (s + 1) - C (k₁ : ℂ) * X - C (k₂ : ℂ)).Separable

/-- If the characteristic polynomial `P(z) = z^{s+p} - k₁ z^p - k₂` (with `k₂ ≠ 0`) has distinct
roots `λ₁, …, λ_{s+p}`, then `ρ(n, s + p) = ∑_i λ_iⁿ⁻¹ / P'(λ_i)` for every `n ≥ s + p`. The paper
states this for the general `ρ` of formula (12) attached to an arbitrary characteristic
polynomial `z^r - a₀ z^{r-1} - ⋯ - a_{r-1}`; this is its specialization to the
`([k]; p; s)`-Padovan–Perrin coefficients, the case the paper applies.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Lemma 5 (`integers-2024-A49-lem-5`). -/
public theorem_wanted padovanPerrinRho_eq_sum_roots (k₁ k₂ : ℂ) (p s : ℕ) (hp : 0 < p)
    (hs : 0 < s) (hk₂ : k₂ ≠ 0) (hsep : (X ^ (s + p) - C k₁ * X ^ p - C k₂).Separable) (n : ℕ)
    (hn : s + p ≤ n) :
    padovanPerrinRho k₁ k₂ p s n =
      ((X ^ (s + p) - C k₁ * X ^ p - C k₂).roots.map fun x =>
        x ^ (n - 1) / (derivative (X ^ (s + p) - C k₁ * X ^ p - C k₂)).eval x).sum

/-- Analytic expression of the `([k]; p; s)`-Padovan–Perrin sequences: for positive integers
`k₁, k₂, p, s` with `p ≥ 2`, `k₁² < k₂`, `p < s`, every complex solution `v` with initial values
`α_j = v j` satisfies, for `n ≥ s + p`,
`v n = ∑_{m=0}^{s+p-1} A_m ∑_i λ_iⁿ⁻¹⁻ᵐ / P'(λ_i)` over the roots `λ_i` of
`P(z) = z^{s+p} - k₁ z^p - k₂`, where `A_m = k₂ α_m + k₁ α_{m+p}` for `m ≤ s - 1` and
`A_m = k₂ α_m` otherwise. The paper's assumption that the roots are distinct is dropped: it
follows from the other hypotheses (Lemma 4, `padovanPerrin_charPoly_separable`).

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 6 (`integers-2024-A49-prop-6`). -/
public theorem_wanted padovanPerrin_eq_sum_roots (k₁ k₂ p s : ℕ) (hk₁ : 0 < k₁) (hp : 2 ≤ p)
    (hps : p < s) (hk : k₁ ^ 2 < k₂) (v : ℕ → ℂ)
    (hv : (padovanPerrinRecurrence (k₁ : ℂ) (k₂ : ℂ) p s).IsSolution v) (n : ℕ)
    (hn : s + p ≤ n) :
    v n = ∑ m ∈ Finset.range (s + p),
      ((k₂ : ℂ) * v m + if m < s then (k₁ : ℂ) * v (m + p) else 0) *
        ((X ^ (s + p) - C (k₁ : ℂ) * X ^ p - C (k₂ : ℂ)).roots.map fun x =>
          x ^ (n - 1 - m) /
            (derivative (X ^ (s + p) - C (k₁ : ℂ) * X ^ p - C (k₂ : ℂ))).eval x).sum

/-- Combinatorial formula for the `k`-Padovan–Perrin numbers `v n = v (n - 2) + k v (n - 3)`
(the case `k₁ = 1`, `k₂ = k`, `p = 1`, `s = 2`): for `n ≥ 3`,
`v n = ρ(n, 3)(k α₀ + α₁) + (k α₁ + α₂) ρ(n - 1, 3) + k α₂ ρ(n - 2, 3)`, with `ρ` as in
`padovanPerrinRho`. The paper prints the middle coefficient as `k α₁`; the coefficient
`A₁ = k₂ α₁ + k₁ α₂ = k α₁ + α₂` is the one its Theorem 3 gives, and the printed form fails for
`k = 2`, `(α₀, α₁, α₂) = (0, 0, 1)`, `n = 4` (`v 4 = 1`, printed right side `0`). Stated for any
`k` in a commutative ring instead of an integer `k ≥ 2`.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 8 (`integers-2024-A49-prop-8`). -/
public theorem_wanted kPadovanPerrin_eq_sum_rho [CommRing R] (k : R) (v : ℕ → R)
    (hv : (padovanPerrinRecurrence 1 k 1 2).IsSolution v) (n : ℕ) (hn : 3 ≤ n) :
    v n = padovanPerrinRho 1 k 1 2 n * (k * v 0 + v 1) +
      (k * v 1 + v 2) * padovanPerrinRho 1 k 1 2 (n - 1) +
        k * v 2 * padovanPerrinRho 1 k 1 2 (n - 2)

/-- For the `k`-Padovan–Perrin fundamental system (`k₁ = 1`, `k₂ = k`, `p = 1`, `s = 2`) and
every `n ≥ 0`: `v⁽³⁾ n = ρ(n + 1, 3)` and `v⁽²⁾ n = ρ(n + 2, 3)`. The paper's third formula
`v⁽¹⁾ n = k ρ(n + 2, 3)` is omitted: it fails for `k = 2`, `n = 0` (`v⁽¹⁾ 0 = 1`,
`2 ρ(2, 3) = 0`). Stated for any `k` in a commutative ring instead of an integer `k ≥ 2`.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 9 (`integers-2024-A49-prop-9`). -/
public theorem_wanted kPadovanPerrinFundamental_eq_rho [CommRing R] (k : R) (n : ℕ) :
    padovanPerrinFundamental 1 k 1 2 3 n = padovanPerrinRho 1 k 1 2 (n + 1) ∧
      padovanPerrinFundamental 1 k 1 2 2 n = padovanPerrinRho 1 k 1 2 (n + 2)

/-- Analytic formula for the `k`-Padovan–Perrin numbers `v n = v (n - 2) + k v (n - 3)` with an
integer `k ≥ 2` (so `27 k² - 4 ≠ 0` and the roots `λ_i` of `z³ - z - k` are distinct): for
`n ≥ 3`, `v n = ∑_i ((k α₀ + α₁) λ_iⁿ⁻¹ + (k α₁ + α₂) λ_iⁿ⁻² + k α₂ λ_iⁿ⁻³) / P'(λ_i)`. The paper
prints the middle coefficient as `k α₁`; `k α₁ + α₂` is the coefficient `A₁` of its Theorem 3,
and the printed form fails already for `k = 2`, `(α₀, α₁, α₂) = (0, 0, 1)`, `n = 4` (where it
gives `0` while `v 4 = 1`).

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 10 (`integers-2024-A49-prop-10`). -/
public theorem_wanted kPadovanPerrin_eq_sum_roots (k : ℕ) (hk : 2 ≤ k) (v : ℕ → ℂ)
    (hv : (padovanPerrinRecurrence 1 (k : ℂ) 1 2).IsSolution v) (n : ℕ) (hn : 3 ≤ n) :
    v n = ((X ^ 3 - X - C (k : ℂ)).roots.map fun x =>
      (((k : ℂ) * v 0 + v 1) * x ^ (n - 1) + ((k : ℂ) * v 1 + v 2) * x ^ (n - 2) +
          (k : ℂ) * v 2 * x ^ (n - 3)) /
        (derivative (X ^ 3 - X - C (k : ℂ))).eval x).sum

end Model

end

end MetaMathlibExt
