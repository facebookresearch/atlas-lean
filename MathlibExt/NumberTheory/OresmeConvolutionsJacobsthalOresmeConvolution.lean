/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Jacobsthal–Oresme convolution

Cauchy convolution `∑_{k=0}^n J_k O_{n-k}` of the Oresme numbers `O_n = n/2^n` with the
Jacobsthal numbers `J_n`, the terms of the Lucas sequence `U(1, -2)`, following M. R. Bacon
and C. K. Cook. The Oresme numbers are written inline as `n / 2^n` over `ℚ`.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 6.2 (`fq-2024-cookbacon061124-prop-6.2`).
-/

namespace MetaMathlibExt

/-- **Jacobsthal–Oresme convolution.** Let $J_m$ denote the Jacobsthal numbers, the terms of the
Lucas sequence $U(1, -2)$, and let $O_m = m/2^m$ denote the Oresme numbers. For every natural
number $n$,
$\sum_{k=0}^{n} J_k O_{n-k} = \frac{2}{9} J_{n+1} - \frac{2(n+1)}{9 \cdot 2^n}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 6.2 (`fq-2024-cookbacon061124-prop-6.2`). -/
public theorem jacobsthal_oresme_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (lucasU ⟨1, -2, by decide⟩ k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 / 9 * (lucasU ⟨1, -2, by decide⟩ (n + 1) : ℚ) - 2 * ((n : ℚ) + 1) / (9 * 2 ^ n)
    := by
  let O (m : ℕ) : ℚ := m / 2 ^ m
  let S (m : ℕ) := ∑ k ∈ Finset.range (m + 1), (lucasU ⟨1, -2, by decide⟩ k : ℚ) * O (m - k)
  have hJ : ∀ k : ℕ, (lucasU ⟨1, -2, by decide⟩ (k + 2) : ℚ)
      = (lucasU ⟨1, -2, by decide⟩ (k + 1) : ℚ)
        + 2 * (lucasU ⟨1, -2, by decide⟩ k : ℚ) := by
    intro k
    have h : lucasU ⟨1, -2, by decide⟩ (k + 2)
        = 1 * lucasU ⟨1, -2, by decide⟩ (k + 1)
          - -2 * lucasU ⟨1, -2, by decide⟩ k :=
      lucasU_add_two ⟨1, -2, by decide⟩ k
    have h2 : ((lucasU ⟨1, -2, by decide⟩ (k + 2) : ℤ) : ℚ)
        = ((lucasU ⟨1, -2, by decide⟩ (k + 1) : ℤ) : ℚ)
          + 2 * ((lucasU ⟨1, -2, by decide⟩ k : ℤ) : ℚ) := by
      rw [h]
      push_cast
      ring
    exact h2
  have hJ0 : (lucasU ⟨1, -2, by decide⟩ 0 : ℚ) = 0 := by simp [lucasU]
  have hJ1 : (lucasU ⟨1, -2, by decide⟩ 1 : ℚ) = 1 := by simp [lucasU]
  have shift (m : ℕ) :
      S (m + 1) = ∑ k ∈ Finset.range (m + 1),
        (lucasU ⟨1, -2, by decide⟩ (k + 1) : ℚ) * O (m - k) := by
    dsimp only [S]
    rw [Finset.sum_range_succ']
    simp [hJ0]
  have step (m : ℕ) : S (m + 2) = S (m + 1) + 2 * S m + O (m + 1) := by
    rw [shift (m + 1), Finset.sum_range_succ', shift m]
    simp [S, hJ, hJ1, add_mul, two_mul, Finset.sum_add_distrib, add_assoc, add_comm,
      add_left_comm]
  change S n = _
  induction n using Nat.twoStepInduction with
  | zero => simp [S, O, hJ1]
  | one =>
    simp [S, O, Finset.sum_range_succ, hJ0, hJ1, hJ]
    norm_num
  | more n ih₀ ih₁ =>
    rw [step, ih₀, ih₁]
    have hRn : (lucasU ⟨1, -2, by decide⟩ (n + 3) : ℚ)
        = (lucasU ⟨1, -2, by decide⟩ (n + 2) : ℚ)
          + 2 * (lucasU ⟨1, -2, by decide⟩ (n + 1) : ℚ) := hJ (n + 1)
    rw [hRn]
    simp only [O, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, pow_succ]
    field_simp
    ring

end MetaMathlibExt
