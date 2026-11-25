/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.MvPowerSeries.ColeHopf

open MvPowerSeries

-- Pin the sign and factor independently of the heat-to-Burgers theorem.
example : constantCoeff (coleHopf (1 : ℚ) (1 : Fin 2) (1 + X 1)) = -2 := by
  simp [coleHopf]

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

-- A quadratic heat profile evolves in time when viscosity is nonzero.
example (ν : ℚ) :
    let φ : MvPowerSeries (Fin 2) ℚ := 1 + X 1 ^ 2 + C (2 * ν) * X 0
    pderiv 0 (coleHopf ν 1 φ) =
      C ν * pderiv 1 (pderiv 1 (coleHopf ν 1 φ)) -
        coleHopf ν 1 φ * pderiv 1 (coleHopf ν 1 φ) := by
  dsimp
  apply pderiv_coleHopf_of_heat
  · simp
  · have htwo (i : Fin 2) : pderiv i (2 : MvPowerSeries (Fin 2) ℚ) = 0 := by
      simpa only [map_ofNat] using (pderiv_C (i := i) (r := (2 : ℚ)))
    simp [map_mul, map_ofNat, smul_eq_mul, htwo]
    ring

-- A non-heat profile exercises the residual identity with a nonzero result.
example (ν : ℚ) :
    constantCoeff
      (pderiv (0 : Fin 2) (coleHopf ν 1 (1 + X 0 * X 1)) +
        coleHopf ν 1 (1 + X 0 * X 1) *
          pderiv 1 (coleHopf ν 1 (1 + X 0 * X 1)) -
        C ν * pderiv 1 (pderiv 1 (coleHopf ν 1 (1 + X 0 * X 1)))) = -2 * ν := by
  rw [coleHopf_residual ν (0 : Fin 2) 1 _ (by simp)]
  simp [smul_eq_mul]

#print axioms MvPowerSeries.pderiv_coleHopf_of_heat
