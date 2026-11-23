/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.MvPowerSeries.CausalEquation
import Mathlib.Tactic.NormNum

open MvPowerSeries MvPowerSeries.Causal

-- A nonlinear spatial PDE is causal along the time axis.
example (boundary : MvPowerSeries (Fin 2) ℚ) :
    ∃! u : MvPowerSeries (Fin 2) ℚ,
      pderiv 0 u = pderiv 1 (pderiv 1 u) + u * u ∧
      ∀ n : Fin 2 →₀ ℕ, n 0 = 0 → coeff n u = coeff n boundary := by
  apply existsUnique_solution
  intro k a b h
  exact ((h.pderiv (by decide)).pderiv (by decide)).add (h.mul h)

-- Integration divides by the positive degree, even for a nonconstant integrand.
example : coeff (Finsupp.single (0 : Fin 1) 2)
    (pIntegral 0 (X 0 : MvPowerSeries (Fin 1) ℚ) 0) = 1 / 2 := by
  have h : (Finsupp.single (0 : Fin 1) 2).update 0 1 = Finsupp.single 0 1 := by
    apply Finsupp.ext
    intro i
    fin_cases i
    simp
  norm_num [coeff_pIntegral, coeff_X, h]

-- The complete spatial boundary is retained, not just its constant coefficient.
example (b f : MvPowerSeries (Fin 2) ℚ) (n : ℕ) :
    coeff (Finsupp.single 1 n) (pIntegral 0 f b) = coeff (Finsupp.single 1 n) b := by
  simp

#print axioms MvPowerSeries.Causal.existsUnique_solution
