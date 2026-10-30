/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKStarTriangle

/-!
# Star–triangle invariance of FK expectations with an external environment

The star–triangle transformation applied inside a larger graph: weighting the terminal
partitions by an arbitrary external factor, the star and the triangle give the same conditional
expectations.

## i. Overview

When a triangle or star sits inside a larger FK graph, the rest of the graph contributes a factor
`external c` depending only on the terminal partition `c`. `triangleFKTerminalWeightedSum` and
`starFKTerminalWeightedSum` are the local partition functions with this environment, and the
`WeightedRatio`s are the resulting expectations of an observable of the terminal partition. On the
triangular critical surface with dual odds `yᵢ yᵢ* = q`, the star sum is `q ^ 2 / (y₀ y₁ y₂)` times
the triangle sum for every environment, so all such expectations agree. This is the form of the
star–triangle move used to transport FK measures between the triangular and hexagonal lattices.
Unconditional, given the critical-surface equation.

## ii. Key results

- `triHexFK_terminalWeightedSum_identity` : `y₀ y₁ y₂ · star sum = q ^ 2 · triangle sum` for every
  environment. Unconditional (given the surface equation).
- `triHexFK_terminalWeightedRatio_eq` : equality of star and triangle expectations for every
  environment and observable, for `q ≠ 0`, `y₀ y₁ y₂ ≠ 0`. Unconditional (given the surface
  equation).

## iii. Table of contents

- A. Local sums with an external environment
- B. Star–triangle invariance

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), §6.6.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace StatMech
namespace FK
namespace PeriodicPlanar

/-! ## A. Local sums with an external environment -/

/-- Local FK partition function of a triangle embedded in a graph whose remainder contributes the
factor `external c` for terminal partition `c`. -/
def triangleFKTerminalWeightedSum
    (y0 y1 y2 : Real) (external : ThreeTerminalConnectivity → Real) : Real :=
  ∑ c, external c * triangleFKTerminalWeight y0 y1 y2 c

/-- Local FK partition function of a star embedded in a graph whose remainder contributes the factor
`external c` for terminal partition `c`. -/
def starFKTerminalWeightedSum
    (q y0 y1 y2 : Real) (external : ThreeTerminalConnectivity → Real) : Real :=
  ∑ c, external c * starFKTerminalWeight q y0 y1 y2 c

/-- Expectation of a terminal observable for an embedded triangle with external environment
`external`. -/
noncomputable def triangleFKTerminalWeightedRatio
    (y0 y1 y2 : Real) (external observable : ThreeTerminalConnectivity → Real) : Real :=
  triangleFKTerminalWeightedSum y0 y1 y2
      (fun c ↦ external c * observable c) /
    triangleFKTerminalWeightedSum y0 y1 y2 external

/-- Expectation of a terminal observable for an embedded star with external environment `external`.
-/
noncomputable def starFKTerminalWeightedRatio
    (q y0 y1 y2 : Real)
    (external observable : ThreeTerminalConnectivity → Real) : Real :=
  starFKTerminalWeightedSum q y0 y1 y2
      (fun c ↦ external c * observable c) /
    starFKTerminalWeightedSum q y0 y1 y2 external

/-! ## B. Star–triangle invariance -/

lemma triHexFK_terminalWeightedSum_identity
    {q y0 y1 y2 y0Star y1Star y2Star : Real}
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0)
    (external : ThreeTerminalConnectivity → Real) :
    (y0 * y1 * y2) *
        starFKTerminalWeightedSum q y0Star y1Star y2Star external =
      q ^ 2 * triangleFKTerminalWeightedSum y0 y1 y2 external := by
  unfold starFKTerminalWeightedSum triangleFKTerminalWeightedSum
  rw [mul_sum, mul_sum]
  apply sum_congr rfl
  intro c _
  have hweight := triHexFK_terminalWeight_identity
    h0 h1 h2 hsurface c
  calc
    (y0 * y1 * y2) *
        (external c * starFKTerminalWeight q y0Star y1Star y2Star c) =
      external c * ((y0 * y1 * y2) *
        starFKTerminalWeight q y0Star y1Star y2Star c) := by ring
    _ = external c *
        (q ^ 2 * triangleFKTerminalWeight y0 y1 y2 c) := by rw [hweight]
    _ = q ^ 2 *
        (external c * triangleFKTerminalWeight y0 y1 y2 c) := by ring

/-- Star–triangle transformation in an external environment: on the triangular critical surface with
dual odds, star and triangle give the same expectation of every terminal observable, for every
environment (Grimmett, *The Random-Cluster Model*, §6.6). -/
theorem triHexFK_terminalWeightedRatio_eq
    {q y0 y1 y2 y0Star y1Star y2Star : Real}
    (hq : q ≠ 0) (hyprod : y0 * y1 * y2 ≠ 0)
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0)
    (external observable : ThreeTerminalConnectivity → Real) :
    starFKTerminalWeightedRatio q y0Star y1Star y2Star external observable =
      triangleFKTerminalWeightedRatio y0 y1 y2 external observable := by
  have scale (coeff : ThreeTerminalConnectivity → Real) :
      starFKTerminalWeightedSum q y0Star y1Star y2Star coeff =
        (q ^ 2 / (y0 * y1 * y2)) *
          triangleFKTerminalWeightedSum y0 y1 y2 coeff := by
    have hid := triHexFK_terminalWeightedSum_identity
      h0 h1 h2 hsurface coeff
    calc
      starFKTerminalWeightedSum q y0Star y1Star y2Star coeff =
          ((y0 * y1 * y2) *
            starFKTerminalWeightedSum q y0Star y1Star y2Star coeff) /
              (y0 * y1 * y2) := by
        apply (eq_div_iff hyprod).2
        ring
      _ = (q ^ 2 * triangleFKTerminalWeightedSum y0 y1 y2 coeff) /
              (y0 * y1 * y2) := by rw [hid]
      _ = (q ^ 2 / (y0 * y1 * y2)) *
          triangleFKTerminalWeightedSum y0 y1 y2 coeff := by ring
  unfold starFKTerminalWeightedRatio triangleFKTerminalWeightedRatio
  rw [scale (fun c ↦ external c * observable c), scale external]
  exact mul_div_mul_left _ _ (div_ne_zero (pow_ne_zero 2 hq) hyprod)

end PeriodicPlanar
end FK
end StatMech
