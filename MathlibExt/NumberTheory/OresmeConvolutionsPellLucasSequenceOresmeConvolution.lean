/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.PellLucasSequence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Pell–Lucas–Oresme convolution

The Cauchy convolution of the associated Pell sequence `pellLucasSequence` with the
Oresme numbers `n / 2^n` over `ℚ` has a closed form in neighboring Pell–Lucas numbers.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 5.4 (`fq-2024-cookbacon061124-prop-5.4`).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Pell–Lucas–Oresme convolution.** Let $Q_m$ denote the Pell–Lucas numbers, with
$Q_0 = Q_1 = 1$ and $Q_{m+2} = 2Q_{m+1} + Q_m$, and let $O_m = m/2^m$ denote the Oresme numbers.
For every natural number $n$,
$\sum_{k=0}^{n} Q_k O_{n-k} = \frac{2}{49}(5 Q_{n+1} - 4 Q_n) + \frac{7n - 2}{49 \cdot 2^n}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 5.4 (`fq-2024-cookbacon061124-prop-5.4`). -/
public theorem pellLucasSequence_oresme_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (pellLucasSequence k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 / 49 * (5 * (pellLucasSequence (n + 1) : ℚ) - 4 * pellLucasSequence n) +
        1 / 49 * ((7 * (n : ℚ) - 2) / 2 ^ n) := by
  let O (m : ℕ) : ℚ := m / 2 ^ m
  let S (m : ℕ) := ∑ k ∈ Finset.range (m + 1), (pellLucasSequence k : ℚ) * O (m - k)
  have shift (m : ℕ) :
      S (m + 1) =
        ∑ k ∈ Finset.range (m + 1), (pellLucasSequence (k + 1) : ℚ) * O (m - k) +
          O (m + 1) := by
    dsimp only [S]
    rw [Finset.sum_range_succ']
    simp
  have step (m : ℕ) : S (m + 2) = 2 * S (m + 1) + S m + (O (m + 2) - O (m + 1)) := by
    rw [shift (m + 1), Finset.sum_range_succ', shift m]
    simp [S, pellLucasSequence_succ_succ, two_mul, add_mul, Finset.sum_add_distrib]
    ring
  change S n = _
  induction n using Nat.twoStepInduction with
  | zero => norm_num [S, O]
  | one => norm_num [S, O, Finset.sum_range_succ, pellLucasSequence_succ_succ]
  | more n ih₀ ih₁ =>
    rw [step, ih₀, ih₁, pellLucasSequence_succ_succ (n + 1), pellLucasSequence_succ_succ n]
    simp only [O, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, pow_succ]
    field_simp
    ring

end

end MetaMathlibExt
