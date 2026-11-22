/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.KolmogorovCycleNecessity

@[expose] public section

open Finset BigOperators

namespace MathlibExtTest.Probability.KolmogorovCycleNecessity

/-- Detailed balance implies stationarity, with the exact public signature. -/
example {M : ℕ} (P : StochasticMatrix M) (π : StochasticMatrix.Distribution M)
    (hdb : P.DetailedBalance π) : P.IsStationary π :=
  P.detailedBalance_isStationary π hdb

/-- For an irreducible chain, a detailed-balance distribution is everywhere positive. -/
example {M : ℕ} (P : StochasticMatrix M) (π : StochasticMatrix.Distribution M)
    (hirr : P.IsIrreducible) (hdb : P.DetailedBalance π) (i : Fin (M + 1)) :
    0 < π.val i :=
  P.distribution_pos_of_irreducible_detailedBalance π hirr hdb i

/-- Reversibility of an irreducible chain implies the cycle condition, with the exact
public signature. -/
example {M : ℕ} (P : StochasticMatrix M) (hirr : P.IsIrreducible)
    (hrev : P.IsReversible) : P.KolmogorovCycleCondition :=
  P.kolmogorov_cycle_necessity hirr hrev

/-- The two-state uniform chain: every transition has probability `1 / 2`. -/
noncomputable def uniformTwo : StochasticMatrix 1 where
  prob := fun _ _ => 1 / 2
  nonneg := fun _ _ => by norm_num
  row_sum := fun _ => by simp

/-- The uniform distribution on two states. -/
noncomputable def uniformTwoDist : StochasticMatrix.Distribution 1 where
  val := fun _ => 1 / 2
  nonneg := fun _ => by norm_num
  sum_one := by simp

/-- One step of the uniform two-state chain has probability `1 / 2` everywhere. -/
private lemma uniformTwo_matPow_one (i j : Fin 2) :
    uniformTwo.matPow 1 i j = 1 / 2 := by
  have hsum : uniformTwo.matPow 1 i j =
      ∑ k : Fin 2, (1 / 2 : ℝ) * uniformTwo.matPow 0 k j :=
    rfl
  rw [hsum, Finset.sum_eq_single j]
  · simp [StochasticMatrix.matPow]
  · intro b _ hb
    simp only [StochasticMatrix.matPow, hb, ite_false, mul_zero]
  · simp

/-- The uniform two-state chain is irreducible: one step already has positive
probability everywhere. -/
private lemma uniformTwo_irreducible : uniformTwo.IsIrreducible := by
  intro i j
  exact ⟨1, one_pos, by rw [uniformTwo_matPow_one i j]; norm_num⟩

/-- The uniform distribution satisfies detailed balance with the uniform two-state chain. -/
example : uniformTwo.DetailedBalance uniformTwoDist := by
  intro _ _
  simp [uniformTwo, uniformTwoDist]

/-- Hence the uniform distribution is stationary for the uniform two-state chain. -/
example : uniformTwo.IsStationary uniformTwoDist :=
  uniformTwo.detailedBalance_isStationary uniformTwoDist (by intro _ _; simp [uniformTwo, uniformTwoDist])

/-- The uniform two-state chain is irreducible. -/
example : uniformTwo.IsIrreducible :=
  uniformTwo_irreducible

/-- The uniform two-state chain is reversible. -/
example : uniformTwo.IsReversible :=
  ⟨uniformTwoDist,
    uniformTwo.detailedBalance_isStationary uniformTwoDist
      (by intro _ _; simp [uniformTwo, uniformTwoDist]),
    by intro _ _; simp [uniformTwo, uniformTwoDist]⟩

/-- Therefore the uniform two-state chain satisfies Kolmogorov's cycle condition. -/
example : uniformTwo.KolmogorovCycleCondition :=
  uniformTwo.kolmogorov_cycle_necessity uniformTwo_irreducible
    ⟨uniformTwoDist,
      uniformTwo.detailedBalance_isStationary uniformTwoDist
        (by intro _ _; simp [uniformTwo, uniformTwoDist]),
      by intro _ _; simp [uniformTwo, uniformTwoDist]⟩

/-- The three-state cyclic shift: from `i` the chain moves deterministically to `i + 1`
(mod `3`). -/
noncomputable def cyclicThree : StochasticMatrix 2 where
  prob := fun i j => if j = i + 1 then 1 else 0
  nonneg := fun i j => by by_cases h : j = i + 1 <;> simp [h]
  row_sum := fun i => by fin_cases i <;> simp

/-- The uniform distribution on three states. -/
noncomputable def uniformThreeDist : StochasticMatrix.Distribution 2 where
  val := fun _ => 1 / 3
  nonneg := fun _ => by norm_num
  sum_one := by simp

/-- The uniform distribution is stationary for the cyclic shift, even though the shift
is not reversible: exactly one predecessor contributes to each state. -/
example : cyclicThree.IsStationary uniformThreeDist := by
  intro j
  fin_cases j <;> simp [Fin.sum_univ_three, cyclicThree, uniformThreeDist]

/-- The cyclic shift does **not** satisfy detailed balance with the uniform distribution:
mass flows `0 → 1` but never `1 → 0`. So detailed balance is strictly stronger than
stationarity. -/
example : ¬ cyclicThree.DetailedBalance uniformThreeDist := by
  intro hdb
  have h := hdb 0 1
  simp [cyclicThree, uniformThreeDist] at h

end MathlibExtTest.Probability.KolmogorovCycleNecessity
