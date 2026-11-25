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

-- At zero viscosity, the Cole–Hopf transform degenerates to zero.
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

-- Arbitrary Burgers data can be lifted, including extra formal parameters.
example {σ K : Type*} [Field K] [CharZero K] (ν : K) (hν : ν ≠ 0)
    (x : σ) (v : MvPowerSeries σ K) :
    coleHopf ν x (initialHeatProfile ν x v) = v :=
  coleHopf_initialHeatProfile hν x v

-- Nonconstant prescribed Burgers data, with an additional parameter axis.
example : ∃! u : MvPowerSeries (Fin 3) ℚ,
    pderiv 0 u = burgersRhs 1 1 u ∧
      ∀ n : Fin 3 →₀ ℕ, n 0 = 0 → coeff n u = coeff n (X 1 + X 2 + X 0) :=
  existsUnique_burgers (by decide) 1 (X 1 + X 2 + X 0)

-- The constructed heat transform realizes that arbitrary initial-value solution.
example (v : MvPowerSeries (Fin 3) ℚ) :
    coleHopf 1 1 (heatSolution 1 0 1 (initialHeatProfile 1 1 v)) =
      Causal.solution 0 (burgersRhs 1 1) v :=
  coleHopf_heatSolution_initialHeatProfile (by decide) (by norm_num) v

-- Normalization fixes the entire spatial zero slice, including parameter axes.
example (v : MvPowerSeries (Fin 3) ℚ) :
    coeff (Finsupp.single 2 1) (initialHeatProfile 1 1 v) = 0 := by
  rw [initialHeatProfile_slice 1 1 v _ (by simp)]
  simp [coeff_one]

-- The first spatial coefficient of the inverse profile detects sign and scale.
example : coeff (Finsupp.single (1 : Fin 2) 1)
    (initialHeatProfile (1 : ℚ) 1 (C 2 + X 1)) = -1 := by
  have h := congrArg (coeff 0)
    (initialHeatProfile_pderiv (1 : ℚ) (1 : Fin 2) (C 2 + X 1))
  rw [coeff_pderiv] at h
  norm_num at h
  exact h

-- Zero viscosity still has a unique formal Burgers solution, without inversion.
example (v : MvPowerSeries (Fin 2) ℚ) :
    ∃! u : MvPowerSeries (Fin 2) ℚ, pderiv 0 u = burgersRhs 0 1 u ∧
      ∀ n : Fin 2 →₀ ℕ, n 0 = 0 → coeff n u = coeff n v :=
  existsUnique_burgers (by decide) 0 v

#print axioms MvPowerSeries.ColeHopf.heatSolution_pde
#print axioms MvPowerSeries.ColeHopf.coleHopf_heatSolution_eq_solution
