/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.MvPowerSeries.ColeHopfSolution
import Mathlib.Tactic.NormNum

open MvPowerSeries MvPowerSeries.ColeHopf

-- Nonstationary heat flow: a quadratic spatial profile acquires a time term.
example (ν : ℚ) : heatSolution ν (0 : Fin 2) 1 (1 + X 1 ^ 2) =
    1 + X 1 ^ 2 + C (2 * ν) * X 0 := by
  symm
  apply heatSolution_unique (by decide)
  · simp [heatRhs, pow_two]
    rw [map_ofNat]
    ring
  · intro n hn
    have hn0 : n ≠ Finsupp.single 0 1 := by
      intro he
      have := congrArg (fun m : Fin 2 →₀ ℕ => m 0) he
      simp [hn] at this
    rw [map_add, coeff_C_mul, coeff_X, ite_eq_right hn0, mul_zero, add_zero]

-- Boundary data may contain positive time coefficients; they are ignored.
example (ν : ℚ) : heatSolution ν (0 : Fin 2) 1 (1 + X 1 + X 0) = 1 + X 1 := by
  symm
  apply heatSolution_unique (by decide)
  · simp [heatRhs]
  · intro n hn
    have hn0 : n ≠ Finsupp.single 0 1 := by
      intro he
      have := congrArg (fun m : Fin 2 →₀ ℕ => m 0) he
      simp [hn] at this
    simp only [map_add, coeff_X, ite_eq_right hn0, add_zero]

-- A nonconstant boundary determines the transformed formal Burgers solution.
example (ν : ℚ) :
    ∃! u : MvPowerSeries (Fin 2) ℚ,
      pderiv 0 u = burgersRhs ν 1 u ∧
      ∀ n : Fin 2 →₀ ℕ, n 0 = 0 →
        coeff n u = coeff n (coleHopf ν 1 (1 + X 1 ^ 2)) := by
  exact existsUnique_burgers_of_heat_boundary (by decide) (by simp)

-- The construction allows zero viscosity and retains the entire spatial slice.
example (b : MvPowerSeries (Fin 2) ℚ) :
    coleHopf 0 1 (heatSolution 0 0 1 b) = 0 := by
  simp [coleHopf]

-- The public endpoint applies over any characteristic-zero field and extra axes.
example {σ K : Type*} [Field K] [CharZero K] {t x : σ}
    (hxt : x ≠ t) (ν : K) (b : MvPowerSeries σ K)
    (hb : constantCoeff b ≠ 0) :
    coleHopf ν x (heatSolution ν t x b) =
      Causal.solution t (burgersRhs ν x) (coleHopf ν x b) :=
  coleHopf_heatSolution_eq_solution hxt hb

#print axioms MvPowerSeries.ColeHopf.heatSolution_pde
#print axioms MvPowerSeries.ColeHopf.coleHopf_heatSolution_eq_solution
