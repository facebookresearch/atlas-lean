/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FK.TriHexFKStarTriangle

open Finset
open scoped BigOperators

namespace StatMech
namespace FK
namespace PeriodicPlanar



def triangleFKTerminalWeightedSum
    (y0 y1 y2 : Real) (external : ThreeTerminalConnectivity → Real) : Real :=
  ∑ c, external c * triangleFKTerminalWeight y0 y1 y2 c


def starFKTerminalWeightedSum
    (q y0 y1 y2 : Real) (external : ThreeTerminalConnectivity → Real) : Real :=
  ∑ c, external c * starFKTerminalWeight q y0 y1 y2 c



noncomputable def triangleFKTerminalWeightedRatio
    (y0 y1 y2 : Real) (external observable : ThreeTerminalConnectivity → Real) : Real :=
  triangleFKTerminalWeightedSum y0 y1 y2
      (fun c ↦ external c * observable c) /
    triangleFKTerminalWeightedSum y0 y1 y2 external



noncomputable def starFKTerminalWeightedRatio
    (q y0 y1 y2 : Real)
    (external observable : ThreeTerminalConnectivity → Real) : Real :=
  starFKTerminalWeightedSum q y0 y1 y2
      (fun c ↦ external c * observable c) /
    starFKTerminalWeightedSum q y0 y1 y2 external



theorem triHexFK_terminalWeightedSum_identity
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
