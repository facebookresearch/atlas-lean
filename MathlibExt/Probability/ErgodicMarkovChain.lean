/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.KolmogorovCycleNecessity
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

/-!
# Ergodic finite Markov chains

A finite-state Markov chain (given by its stochastic transition matrix `P`)
is *ergodic* if some positive power of `P` has all strictly positive entries.
From that single witness we deduce that every later power is all-positive,
that every positive power of an ergodic chain is ergodic, and we exhibit the
uniform chain as ergodic and the identity chain as non-ergodic.

## Source

This ports `v1/Atlas/TheoryOfProbability/code/ErgodicMarkovChain.lean`
(`StochasticMatrix.toMatrix`, `StochasticMatrix.IsErgodic`), the
"Definition (Ergodic Markov chain)" target (Lecture 30/31, Ergodic Markov
chains section) of `v1/Atlas/TheoryOfProbability/targets.yaml`:
"Say a Markov chain is ergodic if some power of the transition matrix has
all non-zero entries." In v1, `StochasticMatrix` itself lives in
`v1/Atlas/TheoryOfProbability/code/FiniteMarkovChain.lean`; the theorems
below are new consequences of the definition, proved here from scratch
by matrix algebra. No measure theory is used.

## Main results

* `StochasticMatrix.matPow_eq_pow`: the recursively defined power `matPow`
  agrees with the ordinary matrix power `P.toMatrix ^ n`.
* `StochasticMatrix.isErgodic_iff_isPrimitive`: ergodicity is exactly
  primitivity (`Matrix.IsPrimitive`) of the transition matrix.
* `StochasticMatrix.IsErgodic.exists_matPow_pos`: an ergodic chain has, for
  every pair of states, some positive power with a positive `(i, j)`-entry.
* `StochasticMatrix.matPow_pos_of_le_of_pos_pow`: if some power is
  all-positive, every later power is all-positive.
* `StochasticMatrix.IsErgodic.eventually_all_matPow_pos`: once a power is
  all-positive, every later power is all-positive.
* `StochasticMatrix.IsErgodic.pow`: every positive power of an ergodic
  chain is ergodic.
* `StochasticMatrix.isErgodic_uniform`: the uniform chain is ergodic.
* `StochasticMatrix.not_isErgodic_identity`: the identity chain is not
  ergodic (for `M ≥ 1`).

## Canonical representation

The root `StochasticMatrix` and its `matPow` recursion come from
`MathlibExt.Probability.KolmogorovCycleNecessity`, also used by the cycle-sufficiency
APIs. This file extends that root namespace with the matrix-power bridge and
finite-state ergodicity results. The module namespace remains openable for clients;
all stochastic-matrix declarations use the shared canonical type.

## Scope

In: the definition, the `matPow = Matrix ^` bridge, and the consequences
above, all for finite chains with state space `Fin (M + 1)`.

Out: stationary distributions, irreducibility, reversibility, and the
cycle condition (batches 17 and 37); ergodic theorems for
measure-preserving transformations (`Mathlib.Dynamics.Ergodic`); any
statement about the chain as a stochastic process (filtrations,
stopping times, path measures).
-/

@[expose] public section

open Finset BigOperators

namespace MathlibExt.Probability.ErgodicMarkovChain
end MathlibExt.Probability.ErgodicMarkovChain

namespace StochasticMatrix

variable {M : ℕ}

/-- Underlying matrix of probabilities of a `StochasticMatrix`. -/
def toMatrix (P : StochasticMatrix M) : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ :=
  P.prob

/-- A finite-state Markov chain (given by its stochastic transition matrix `P`) is
*ergodic* if some positive power `P^n` has all strictly positive entries. -/
def IsErgodic (P : StochasticMatrix M) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ i j : Fin (M + 1), (P.toMatrix ^ n) i j > 0

/-- The recursively defined power `matPow` agrees with the ordinary matrix power. -/
theorem matPow_eq_pow (P : StochasticMatrix M) : ∀ (n : ℕ) (i j : Fin (M + 1)),
    P.matPow n i j = (P.toMatrix ^ n) i j := by
  intro n
  induction n with
  | zero =>
    intro i j
    simp [matPow, Matrix.one_apply]
  | succ k ih =>
    intro i j
    calc P.matPow (k + 1) i j
        = ∑ k', P.prob i k' * P.matPow k k' j := by simp only [matPow]
      _ = ∑ k', P.toMatrix i k' * (P.toMatrix ^ k) k' j :=
        Finset.sum_congr rfl fun k' _ => by
          rw [ih k' j]
          rfl
      _ = (P.toMatrix * P.toMatrix ^ k) i j := Matrix.mul_apply.symm
      _ = (P.toMatrix ^ (k + 1)) i j := by rw [pow_succ']

/-- Ergodicity is exactly primitivity of the transition matrix. This is the
bridge to Mathlib: `Matrix.IsPrimitive` is the same condition for a bare
matrix, while `IsErgodic` is the stochastic-matrix form, with nonnegativity
supplied by the `StochasticMatrix` structure. -/
theorem isErgodic_iff_isPrimitive (P : StochasticMatrix M) :
    P.IsErgodic ↔ Matrix.IsPrimitive P.toMatrix := by
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨fun i j => P.nonneg i j, n, hn, h⟩
  · rintro ⟨-, n, hn, h⟩
    exact ⟨n, hn, h⟩

/-- Every row of every power of a stochastic matrix sums to `1`: powers of a
stochastic matrix are stochastic. -/
theorem matPow_row_sum (P : StochasticMatrix M) : ∀ (n : ℕ) (i : Fin (M + 1)),
    ∑ j, P.matPow n i j = 1 := by
  intro n
  induction n with
  | zero => intro i; simp [matPow]
  | succ k ih =>
    intro i
    calc ∑ j, P.matPow (k + 1) i j
        = ∑ j, ∑ k', P.prob i k' * P.matPow k k' j := by simp only [matPow]
      _ = ∑ k', ∑ j, P.prob i k' * P.matPow k k' j := Finset.sum_comm
      _ = ∑ k', P.prob i k' * (∑ j, P.matPow k k' j) :=
        Finset.sum_congr rfl fun k' _ => by rw [← Finset.mul_sum]
      _ = ∑ k', P.prob i k' * 1 :=
        Finset.sum_congr rfl fun k' _ => by rw [ih k']
      _ = 1 := by simp [P.row_sum i]

/-- One step of the power recursion: `matPow 1` is the matrix itself. -/
theorem matPow_one (P : StochasticMatrix M) (i j : Fin (M + 1)) :
    P.matPow 1 i j = P.prob i j := by
  simp only [matPow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp only [hb, ite_false, mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- Powers add: `matPow (a + b)` is the matrix product of `matPow a` and `matPow b`. -/
theorem matPow_add (P : StochasticMatrix M) (a b : ℕ) (i j : Fin (M + 1)) :
    P.matPow (a + b) i j = ∑ k, P.matPow a i k * P.matPow b k j := by
  calc P.matPow (a + b) i j = (P.toMatrix ^ (a + b)) i j :=
        matPow_eq_pow P _ _ _
    _ = ((P.toMatrix ^ a) * (P.toMatrix ^ b)) i j := by rw [pow_add]
    _ = ∑ k, (P.toMatrix ^ a) i k * (P.toMatrix ^ b) k j := Matrix.mul_apply
    _ = ∑ k, P.matPow a i k * P.matPow b k j :=
      Finset.sum_congr rfl fun k _ => by
        rw [← matPow_eq_pow P a i k, ← matPow_eq_pow P b k j]

/-- If some power `w` of a stochastic matrix is all-positive, then every later
power `m ≥ w` is all-positive: write `m = (m - w) + w`, use `matPow_add`, and
note that row `i` of `matPow (m - w)` sums to `1`, so some entry of that row is
positive, and that entry times the positive `matPow w` entry gives a positive
summand. -/
theorem matPow_pos_of_le_of_pos_pow {P : StochasticMatrix M} {w m : ℕ}
    (hw : ∀ i j : Fin (M + 1), 0 < P.matPow w i j) (hwm : w ≤ m) (i j : Fin (M + 1)) :
    0 < P.matPow m i j := by
  have hsum : 0 < ∑ k, P.matPow (m - w) i k := by
    rw [matPow_row_sum]; exact one_pos
  rw [Finset.sum_pos_iff_of_nonneg (fun k _ => matPow_nonneg P (m - w) i k)] at hsum
  obtain ⟨k, -, hk⟩ := hsum
  have hmn : m = (m - w) + w := (Nat.sub_add_cancel hwm).symm
  rw [hmn, matPow_add]
  rw [Finset.sum_pos_iff_of_nonneg
    (fun k' _ => mul_nonneg (matPow_nonneg P (m - w) i k') (le_of_lt (hw k' j)))]
  exact ⟨k, Finset.mem_univ k, mul_pos hk (hw k j)⟩

/-- An ergodic chain has, for every pair of states, some positive power with
a positive `(i, j)`-entry. (This is the per-pair form; it is strictly weaker
than ergodicity, which asks for one power working for all pairs at once.) -/
theorem IsErgodic.exists_matPow_pos {P : StochasticMatrix M} (h : P.IsErgodic)
    (i j : Fin (M + 1)) : ∃ n : ℕ, 0 < n ∧ 0 < P.matPow n i j := by
  obtain ⟨n, hn, hpos⟩ := h
  exact ⟨n, hn, by rw [matPow_eq_pow]; exact hpos i j⟩

/-- Once a power of an ergodic chain is all-positive, every later power is
all-positive: there is a threshold `w` past which every power is all-positive. -/
theorem IsErgodic.eventually_all_matPow_pos {P : StochasticMatrix M} (h : P.IsErgodic) :
    ∃ w, 0 < w ∧ ∀ m, w ≤ m → ∀ i j : Fin (M + 1), 0 < P.matPow m i j := by
  obtain ⟨w, hw, hpos⟩ := h
  exact ⟨w, hw, fun m hwm i j =>
    matPow_pos_of_le_of_pos_pow
      (fun k j' => by rw [matPow_eq_pow]; exact hpos k j') hwm i j⟩

/-- The `p`-th power of a stochastic matrix, as a stochastic matrix. -/
def pow (P : StochasticMatrix M) (p : ℕ) : StochasticMatrix M where
  prob := P.matPow p
  nonneg := fun i j => matPow_nonneg P p i j
  row_sum := fun i => matPow_row_sum P p i

/-- The underlying matrix of `P.pow p` is the `p`-th matrix power of `P`. -/
theorem toMatrix_pow (P : StochasticMatrix M) (p : ℕ) :
    (P.pow p).toMatrix = P.toMatrix ^ p := by
  funext i j
  exact matPow_eq_pow P p i j

/-- Powers of a power: `(P.pow p).matPow n = P.matPow (p * n)`. -/
theorem matPow_pow (P : StochasticMatrix M) (p n : ℕ) (i j : Fin (M + 1)) :
    (P.pow p).matPow n i j = P.matPow (p * n) i j := by
  rw [matPow_eq_pow, toMatrix_pow, ← pow_mul, ← matPow_eq_pow]

/-- Every positive power of an ergodic chain is ergodic. -/
theorem IsErgodic.pow {P : StochasticMatrix M} (h : P.IsErgodic) {p : ℕ}
    (hp : 0 < p) : (P.pow p).IsErgodic := by
  obtain ⟨w, hw, hpos⟩ := h
  refine ⟨w, hw, fun i j => ?_⟩
  have hle : w ≤ p * w := by
    rw [mul_comm p w]
    exact le_mul_of_one_le_right (Nat.zero_le w) hp
  have hpos' : 0 < P.matPow (p * w) i j :=
    matPow_pos_of_le_of_pos_pow (fun k j' => by rw [matPow_eq_pow]; exact hpos k j') hle i j
  rw [← matPow_pow] at hpos'
  rw [← matPow_eq_pow]
  exact hpos'

/-- The uniform chain: every transition has probability `1 / (M + 1)`. -/
noncomputable def uniform (M : ℕ) : StochasticMatrix M where
  prob := fun _ _ => ((M + 1 : ℕ) : ℝ)⁻¹
  nonneg := fun _ _ => by positivity
  row_sum := fun _ => by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by positivity)

/-- The uniform chain has constant transition probabilities `1 / (M + 1)`. -/
theorem prob_uniform (M : ℕ) (i j : Fin (M + 1)) :
    (uniform M).prob i j = ((M + 1 : ℕ) : ℝ)⁻¹ :=
  rfl

/-- The uniform chain is ergodic, with witness `n = 1`. -/
theorem isErgodic_uniform (M : ℕ) : (uniform M).IsErgodic := by
  refine ⟨1, one_pos, fun i j => ?_⟩
  rw [← matPow_eq_pow, matPow_one, prob_uniform]
  positivity

/-- The identity chain: `prob i j` is `1` on the diagonal and `0` elsewhere. -/
def identity (M : ℕ) : StochasticMatrix M where
  prob := fun i j => if i = j then 1 else 0
  nonneg := fun i j => by split_ifs <;> norm_num
  row_sum := fun i => by simp

/-- The identity chain has the displayed transition probabilities. -/
theorem prob_identity (M : ℕ) (i j : Fin (M + 1)) :
    (identity M).prob i j = if i = j then 1 else 0 :=
  rfl

/-- Every power of the identity chain is the identity matrix. -/
theorem matPow_identity (M : ℕ) : ∀ (n : ℕ) (i j : Fin (M + 1)),
    (identity M).matPow n i j = if i = j then 1 else 0 := by
  intro n
  induction n with
  | zero => intro i j; simp [matPow]
  | succ k ih =>
    intro i j
    simp only [matPow, prob_identity]
    rw [Finset.sum_eq_single i]
    · simp [ih i j]
    · intro b _ hb
      have hb' : i ≠ b := Ne.symm hb
      simp only [hb', ite_false, zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

/-- The identity chain is not ergodic (for `M ≥ 1`): every power has a zero
off-diagonal entry. -/
theorem not_isErgodic_identity {M : ℕ} (hM : 1 ≤ M) : ¬ (identity M).IsErgodic := by
  rintro ⟨n, -, h⟩
  have h01 := h ⟨0, Nat.succ_pos M⟩ ⟨1, by omega⟩
  rw [← matPow_eq_pow, matPow_identity] at h01
  have hne : (⟨0, Nat.succ_pos M⟩ : Fin (M + 1)) ≠ ⟨1, by omega⟩ := by simp
  simp only [hne, ite_false] at h01
  exact lt_irrefl 0 h01

end StochasticMatrix
