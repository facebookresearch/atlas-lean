/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Kolmogorov's cycle theorem, necessity half

For a finite Markov chain, a distribution satisfying the detailed balance
equations is stationary, and — for an irreducible chain — is strictly
positive and forces the transition matrix to satisfy Kolmogorov's cycle
condition.

## Source

This formalizes the necessity half (`→` direction) of
"Kolmogorov's cycle theorem" / `kolmogorov_cycle_theorem` (Lecture 32,
Cycle theorem) of `v1/Atlas/TheoryOfProbability/targets.yaml`:
"Suppose `p` is irreducible. Then there exists a reversible measure if and
only if (1) `p(x, y) > 0` implies `p(y, x) > 0`, and (2) for any loop
`x₀, x₁, …, xₙ` with `∏ P(xᵢ, xᵢ₋₁) > 0`, we have
`∏ P(xᵢ₋₁, xᵢ) / P(xᵢ, xᵢ₋₁) = 1`."
Its v1 formalization is `v1/Atlas/TheoryOfProbability/code/KolmogorovCycle.lean`
(`kolmogorov_cycle_theorem`), where the statement is proved in full.

Only the necessity half is ported here. The sufficiency half — constructing
a reversible measure from the cycle condition via the cycle-weight
construction (`cycleWeight`, `listRatioProduct`, `cycleWeight_detailed_balance`
in v1) — is not claimed.

## Main results

* `StochasticMatrix.detailedBalance_isStationary`: detailed balance implies
  stationarity.
* `StochasticMatrix.distribution_pos_of_irreducible_detailedBalance`:
  for an irreducible chain, a distribution satisfying detailed balance is
  strictly positive at every state.
* `StochasticMatrix.kolmogorov_cycle_necessity`: for an irreducible chain,
  reversibility implies Kolmogorov's cycle condition.
-/

@[expose] public section

open Finset BigOperators

/-- A `StochasticMatrix M` is an `(M + 1) × (M + 1)` row-stochastic matrix: entries
`prob i j` are non-negative real numbers, and the rows sum to `1`. This is the
transition matrix of a Markov chain on the finite state space `Fin (M + 1)`. -/
structure StochasticMatrix (M : ℕ) where
  prob : Fin (M + 1) → Fin (M + 1) → ℝ
  nonneg : ∀ i j, 0 ≤ prob i j
  row_sum : ∀ i, ∑ j, prob i j = 1

namespace StochasticMatrix

variable {M : ℕ}

/-- The `n`-th matrix power of a stochastic transition matrix `P`. Entry `(i, j)`
represents the probability of moving from state `i` to state `j` in exactly `n` steps. -/
def matPow (P : StochasticMatrix M) : ℕ → (Fin (M + 1) → Fin (M + 1) → ℝ)
  | 0 => fun i j => if i = j then 1 else 0
  | n + 1 => fun i j => ∑ k, P.prob i k * P.matPow n k j

/-- A stochastic matrix `P` is **irreducible** if for every pair of states `i, j` there is some
positive number of steps `n` such that `P ^ n i j > 0`; i.e., every state is reachable from
every other state in finitely many steps. -/
def IsIrreducible (P : StochasticMatrix M) : Prop :=
  ∀ i j : Fin (M + 1), ∃ n : ℕ, 0 < n ∧ 0 < P.matPow n i j

/-- A **probability distribution** on the finite state space `Fin (M + 1)`: a function
`val : Fin (M + 1) → ℝ` whose values are nonnegative and sum to `1`. -/
structure Distribution (M : ℕ) where
  val : Fin (M + 1) → ℝ
  nonneg : ∀ i, 0 ≤ val i
  sum_one : ∑ i, val i = 1

/-- A distribution `π` is **stationary** for the transition matrix `P` if `π P = π`, i.e.,
`∑ᵢ π(i) P(i, j) = π(j)` for every state `j`. -/
def IsStationary (P : StochasticMatrix M) (π : Distribution M) : Prop :=
  ∀ j, ∑ i, π.val i * P.prob i j = π.val j

/-- The **detailed balance** (reversibility) equations between `P` and `π`:
`π(i) P(i, j) = π(j) P(j, i)` for all states `i, j`. -/
def DetailedBalance (P : StochasticMatrix M) (π : Distribution M) : Prop :=
  ∀ i j : Fin (M + 1), π.val i * P.prob i j = π.val j * P.prob j i

/-- A transition matrix `P` is **reversible** if there exists a distribution `π` that is
both stationary and satisfies the detailed balance equations with `P`. -/
def IsReversible (P : StochasticMatrix M) : Prop :=
  ∃ π : Distribution M, P.IsStationary π ∧ P.DetailedBalance π

/-- **Kolmogorov's cycle condition** on a stochastic matrix `P`:
(1) `symm_support`: `P(x, y) > 0` implies `P(y, x) > 0`; and
(2) `cycle_prod`: for any loop `x₀, x₁, …, xₙ = x₀` whose reverse path has positive
probability, the product of forward transition probabilities along the loop equals the
product of backward transition probabilities. -/
structure KolmogorovCycleCondition (P : StochasticMatrix M) : Prop where
  symm_support : ∀ x y : Fin (M + 1), P.prob x y > 0 → P.prob y x > 0
  cycle_prod : ∀ (n : ℕ) (c : Fin (n + 1) → Fin (M + 1)), c 0 = c (Fin.last n) →
    (∏ i : Fin n, P.prob (c i.succ) (c i.castSucc)) > 0 →
    (∏ i : Fin n, P.prob (c i.castSucc) (c i.succ)) =
      (∏ i : Fin n, P.prob (c i.succ) (c i.castSucc))

/-- If `π` satisfies detailed balance with `P`, then `π` is stationary for `P`. Detailed
balance is a strictly stronger condition than stationarity. -/
theorem detailedBalance_isStationary (P : StochasticMatrix M) (π : Distribution M)
    (hdb : P.DetailedBalance π) : P.IsStationary π := by
  intro j
  calc ∑ i, π.val i * P.prob i j
      = ∑ i, π.val j * P.prob j i :=
        Finset.sum_congr rfl fun i _ => hdb i j
    _ = π.val j * ∑ i, P.prob j i := by rw [← Finset.mul_sum]
    _ = π.val j * 1 := by rw [P.row_sum j]
    _ = π.val j := mul_one _

/-- Every entry of every power of a stochastic matrix is nonnegative. -/
lemma matPow_nonneg (P : StochasticMatrix M) : ∀ (n : ℕ) (i j : Fin (M + 1)),
    0 ≤ P.matPow n i j := by
  intro n
  induction n with
  | zero => intro i j; simp only [matPow]; split_ifs <;> linarith
  | succ k ih =>
    intro i j
    simp only [matPow]
    exact Finset.sum_nonneg fun c _ => mul_nonneg (P.nonneg i c) (ih c j)

/-- For an irreducible chain `P`, any distribution `π` satisfying detailed balance
must assign strictly positive mass to every state. -/
theorem distribution_pos_of_irreducible_detailedBalance
    (P : StochasticMatrix M) (π : Distribution M)
    (hirr : P.IsIrreducible) (hdb : P.DetailedBalance π) :
    ∀ i, 0 < π.val i := by
  have hsome : ∃ j, 0 < π.val j := by
    by_contra h
    have hzero : ∀ j, π.val j = 0 := by
      intro j
      have hj : ¬ 0 < π.val j := fun hj => h ⟨j, hj⟩
      exact le_antisymm (not_lt.mp hj) (π.nonneg j)
    have hsum : ∑ i : Fin (M + 1), π.val i = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact hzero i
    linarith [π.sum_one]
  obtain ⟨j₀, hj₀⟩ := hsome
  have step : ∀ a c, 0 < π.val a → 0 < P.prob a c → 0 < π.val c := by
    intro a c ha hPac
    have hdb_ac := hdb a c
    have hLHS : 0 < π.val a * P.prob a c := mul_pos ha hPac
    rw [hdb_ac] at hLHS
    exact pos_of_mul_pos_left hLHS (P.nonneg c a)
  have key : ∀ (m : ℕ), ∀ a b, 0 < π.val a → 0 < P.matPow m a b → 0 < π.val b := by
    intro m
    induction m with
    | zero =>
      intro a b ha hm
      simp only [matPow] at hm
      split_ifs at hm with heq
      · exact heq ▸ ha
      · linarith
    | succ k ih =>
      intro a b ha hm
      simp only [matPow] at hm
      rw [Finset.sum_pos_iff_of_nonneg
        (fun c _ => mul_nonneg (P.nonneg a c) (matPow_nonneg P k c b))] at hm
      obtain ⟨c, _, hc⟩ := hm
      have hPac : 0 < P.prob a c := pos_of_mul_pos_left hc (matPow_nonneg P k c b)
      have hPkb : 0 < P.matPow k c b := pos_of_mul_pos_right hc (P.nonneg a c)
      exact ih c b (step a c ha hPac) hPkb
  intro i
  obtain ⟨n, _, hn⟩ := hirr j₀ i
  exact key n j₀ i hj₀ hn

/-- Helper lemma: along a loop `c : Fin (n + 1) → Fin (M + 1)` with `c 0 = c (Fin.last n)`,
the product `∏ i, f (c (i.castSucc))` equals the shifted product `∏ i, f (c (i.succ))`.
This is a telescoping/cyclic rearrangement of products. -/
private lemma prod_castSucc_eq_prod_succ {n : ℕ} {M : ℕ}
    (f : Fin (M + 1) → ℝ) (c : Fin (n + 1) → Fin (M + 1))
    (hcycle : c 0 = c (Fin.last n)) :
    ∏ i : Fin n, f (c i.castSucc) = ∏ i : Fin n, f (c i.succ) := by
  have h1 : ∏ i : Fin (n + 1), f (c i) =
      (∏ i : Fin n, f (c i.castSucc)) * f (c (Fin.last n)) :=
    Fin.prod_univ_castSucc (fun i => f (c i))
  have h2 : ∏ i : Fin (n + 1), f (c i) =
      f (c 0) * (∏ i : Fin n, f (c i.succ)) :=
    Fin.prod_univ_succ (fun i => f (c i))
  cases n with
  | zero => simp
  | succ k =>
    have heq := h1.symm.trans h2
    rw [← hcycle] at heq
    by_cases hfc : f (c 0) = 0
    · have hL : ∏ i : Fin (k + 1), f (c i.castSucc) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (k + 1)))
        show f (c ((0 : Fin (k + 1)).castSucc)) = 0
        have hcast : ((0 : Fin (k + 1)).castSucc : Fin (k + 2)) = (0 : Fin (k + 2)) := by
          ext; simp [Fin.castSucc]
        rw [hcast]; exact hfc
      have hR : ∏ i : Fin (k + 1), f (c i.succ) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ (Fin.last k))
        show f (c ((Fin.last k).succ)) = 0
        have hsucc : ((Fin.last k).succ : Fin (k + 2)) = Fin.last (k + 1) := by
          ext; simp [Fin.last]
        rw [hsucc, ← hcycle]; exact hfc
      rw [hL, hR]
    · have heq' : f (c 0) * (∏ i : Fin (k + 1), f (c i.castSucc)) =
          f (c 0) * (∏ i : Fin (k + 1), f (c i.succ)) := by
        rw [mul_comm (f (c 0))]; exact heq
      exact mul_left_cancel₀ hfc heq'

/-- **Kolmogorov's cycle theorem, necessity half.** For an irreducible finite
Markov chain with transition matrix `P`, if there exists a reversible measure
(i.e. `P.IsReversible`) then `P` satisfies Kolmogorov's cycle condition:
(1) `P(x, y) > 0` implies `P(y, x) > 0`; and
(2) for any loop `x₀, x₁, …, xₙ = x₀` with `∏ P(xᵢ, xᵢ₋₁) > 0`, the product
of forward transition probabilities along the loop equals the product of
backward transition probabilities. -/
theorem kolmogorov_cycle_necessity {M : ℕ} (P : StochasticMatrix M)
    (hirr : P.IsIrreducible) (hrev : P.IsReversible) :
    P.KolmogorovCycleCondition := by
  obtain ⟨π, _, hdb⟩ := hrev
  have hπ := distribution_pos_of_irreducible_detailedBalance P π hirr hdb
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have h := hdb x y
    have hLHS : 0 < π.val x * P.prob x y := mul_pos (hπ x) hxy
    rw [h] at hLHS
    exact pos_of_mul_pos_right hLHS (π.nonneg y)
  · intro n c hcycle _hback
    have hdb_prod : (∏ i : Fin n, π.val (c i.castSucc)) *
        (∏ i : Fin n, P.prob (c i.castSucc) (c i.succ)) =
        (∏ i : Fin n, π.val (c i.succ)) *
        (∏ i : Fin n, P.prob (c i.succ) (c i.castSucc)) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => hdb (c i.castSucc) (c i.succ)
    have hprod_eq : ∏ i : Fin n, π.val (c i.castSucc) =
        ∏ i : Fin n, π.val (c i.succ) :=
      prod_castSucc_eq_prod_succ π.val c hcycle
    have hpi_pos : 0 < ∏ i : Fin n, π.val (c i.castSucc) :=
      Finset.prod_pos fun i _ => hπ (c i.castSucc)
    rw [hprod_eq] at hdb_prod
    have hpi_ne : (∏ i : Fin n, π.val (c i.succ)) ≠ 0 := by
      rw [← hprod_eq]; exact ne_of_gt hpi_pos
    exact mul_left_cancel₀ hpi_ne hdb_prod

end StochasticMatrix
