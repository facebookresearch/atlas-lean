/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.MvPowerSeries.ColeHopf

open MvPowerSeries

-- Zero viscosity is admitted; no positivity assumption is needed formally.
example (φ : MvPowerSeries (Fin 2) ℚ) : coleHopf 0 1 φ = 0 := by
  simp [coleHopf]

-- A constant nonzero heat profile yields the zero Burgers solution.
example (ν : ℚ) : coleHopf ν (1 : Fin 2) (C 3) = 0 := by
  simp [coleHopf]

-- A nonconstant stationary heat profile produces a formal Burgers solution.
example (ν : ℚ) :
    pderiv (0 : Fin 2) (coleHopf ν 1 (1 + X 1)) =
      C ν * pderiv 1 (pderiv 1 (coleHopf ν 1 (1 + X 1))) -
      coleHopf ν 1 (1 + X 1) * pderiv 1 (coleHopf ν 1 (1 + X 1)) := by
  apply pderiv_coleHopf_of_heat
  · simp
  · simp

#print axioms MvPowerSeries.pderiv_coleHopf_of_heat
