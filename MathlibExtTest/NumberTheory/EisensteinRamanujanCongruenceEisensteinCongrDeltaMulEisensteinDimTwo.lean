/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.EisensteinRamanujanCongruenceEisensteinCongrDeltaMulEisensteinDimTwo
import MathlibExt.NumberTheory.EisensteinRamanujanCongruence
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Topology.Instances.Rat

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MathlibExtTest.NumberTheory.EisensteinRamanujanCongruenceEisensteinCongrDeltaMulEisensteinDimTwo

-- At k = 24 and n = 0 the congruence compares the Bernoulli constant term.
-- (k is let-bound so that the filter predicate in N' elaborates.)
example :
    let k := 24
    let σ₀ : ℕ → ℕ → ℚ := fun w n => if w = 0 then (if n = 0 then 1 else 0)
      else if n = 0 then -bernoulli w / (2 * w) else (ArithmeticFunction.sigma (w - 1) n : ℚ)
    let Δ : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24
    let b : ℕ → ℕ → ℚ := fun i n =>
      coeff n (Δ ^ i * PowerSeries.mk (σ₀ (k - 12 * i))) / σ₀ (k - 12 * i) 0
    let Nw : ℕ → ℕ := fun w => if w ≤ 2 then 1 else (σ₀ w 0).num.natAbs
    let N' : ℕ := ((Nat.divisors (Nw k)).filter fun d =>
      ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))).sup id
    let γ₂ : ℚ := 2 ^ (k - 1) + 25 - 1 / σ₀ (k - 12) 0
    ((σ₀ k 0 - (b 1 0 + γ₂ * b 2 0)) / N').den.Coprime N' := by
  intro k σ₀ Δ b Nw N' γ₂
  exact (MetaMathlibExt.eisenstein_congr_delta_mul_eisenstein_dim_two 24 (by decide)).1 0

-- At k = 24 and n = 5 the congruence compares a divisor sum at a non-degenerate index.
example :
    let k := 24
    let σ₀ : ℕ → ℕ → ℚ := fun w n => if w = 0 then (if n = 0 then 1 else 0)
      else if n = 0 then -bernoulli w / (2 * w) else (ArithmeticFunction.sigma (w - 1) n : ℚ)
    let Δ : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24
    let b : ℕ → ℕ → ℚ := fun i n =>
      coeff n (Δ ^ i * PowerSeries.mk (σ₀ (k - 12 * i))) / σ₀ (k - 12 * i) 0
    let Nw : ℕ → ℕ := fun w => if w ≤ 2 then 1 else (σ₀ w 0).num.natAbs
    let N' : ℕ := ((Nat.divisors (Nw k)).filter fun d =>
      ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))).sup id
    let γ₂ : ℚ := 2 ^ (k - 1) + 25 - 1 / σ₀ (k - 12) 0
    ((σ₀ k 5 - (b 1 5 + γ₂ * b 2 5)) / N').den.Coprime N' := by
  intro k σ₀ Δ b Nw N' γ₂
  exact (MetaMathlibExt.eisenstein_congr_delta_mul_eisenstein_dim_two 24 (by decide)).2 5
    (by decide)

-- At k = 38 and n = 0 the modulus filters over three weights.
example :
    let k := 38
    let σ₀ : ℕ → ℕ → ℚ := fun w n => if w = 0 then (if n = 0 then 1 else 0)
      else if n = 0 then -bernoulli w / (2 * w) else (ArithmeticFunction.sigma (w - 1) n : ℚ)
    let Δ : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24
    let b : ℕ → ℕ → ℚ := fun i n =>
      coeff n (Δ ^ i * PowerSeries.mk (σ₀ (k - 12 * i))) / σ₀ (k - 12 * i) 0
    let Nw : ℕ → ℕ := fun w => if w ≤ 2 then 1 else (σ₀ w 0).num.natAbs
    let N' : ℕ := ((Nat.divisors (Nw k)).filter fun d =>
      ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))).sup id
    let γ₂ : ℚ := 2 ^ (k - 1) + 25 - 1 / σ₀ (k - 12) 0
    ((σ₀ k 0 - (b 1 0 + γ₂ * b 2 0)) / N').den.Coprime N' := by
  intro k σ₀ Δ b Nw N' γ₂
  exact (MetaMathlibExt.eisenstein_congr_delta_mul_eisenstein_dim_two 38 (by decide)).1 0

-- At k = 38 and n = 7 the congruence compares a divisor sum with inner weight 14.
example :
    let k := 38
    let σ₀ : ℕ → ℕ → ℚ := fun w n => if w = 0 then (if n = 0 then 1 else 0)
      else if n = 0 then -bernoulli w / (2 * w) else (ArithmeticFunction.sigma (w - 1) n : ℚ)
    let Δ : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24
    let b : ℕ → ℕ → ℚ := fun i n =>
      coeff n (Δ ^ i * PowerSeries.mk (σ₀ (k - 12 * i))) / σ₀ (k - 12 * i) 0
    let Nw : ℕ → ℕ := fun w => if w ≤ 2 then 1 else (σ₀ w 0).num.natAbs
    let N' : ℕ := ((Nat.divisors (Nw k)).filter fun d =>
      ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))).sup id
    let γ₂ : ℚ := 2 ^ (k - 1) + 25 - 1 / σ₀ (k - 12) 0
    ((σ₀ k 7 - (b 1 7 + γ₂ * b 2 7)) / N').den.Coprime N' := by
  intro k σ₀ Δ b Nw N' γ₂
  exact (MetaMathlibExt.eisenstein_congr_delta_mul_eisenstein_dim_two 38 (by decide)).1 7

end MathlibExtTest.NumberTheory.EisensteinRamanujanCongruenceEisensteinCongrDeltaMulEisensteinDimTwo
