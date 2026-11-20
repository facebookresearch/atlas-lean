/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.FKTrihexDuality

open Finset
open scoped BigOperators

namespace StatMech
namespace FK
namespace PeriodicPlanar

open FrontierA


inductive ThreeTerminalConnectivity
  | separate
  | pair01
  | pair12
  | pair20
  | together
  deriving DecidableEq, Fintype




def triangleFKTerminalWeight (y0 y1 y2 : Real) :
    ThreeTerminalConnectivity -> Real
  | .separate => 1
  | .pair01 => y2
  | .pair12 => y0
  | .pair20 => y1
  | .together => y0 * y1 + y1 * y2 + y2 * y0 + y0 * y1 * y2




def starFKTerminalWeight (q y0 y1 y2 : Real) :
    ThreeTerminalConnectivity -> Real
  | .separate => q + y0 + y1 + y2
  | .pair01 => y0 * y1
  | .pair12 => y1 * y2
  | .pair20 => y2 * y0
  | .together => y0 * y1 * y2


def triangleFKTerminalPartition (y0 y1 y2 : Real) : Real :=
  ∑ c, triangleFKTerminalWeight y0 y1 y2 c


def starFKTerminalPartition (q y0 y1 y2 : Real) : Real :=
  ∑ c, starFKTerminalWeight q y0 y1 y2 c


noncomputable def triangleFKTerminalProbability (y0 y1 y2 : Real)
    (c : ThreeTerminalConnectivity) : Real :=
  triangleFKTerminalWeight y0 y1 y2 c /
    triangleFKTerminalPartition y0 y1 y2


noncomputable def starFKTerminalProbability (q y0 y1 y2 : Real)
    (c : ThreeTerminalConnectivity) : Real :=
  starFKTerminalWeight q y0 y1 y2 c /
    starFKTerminalPartition q y0 y1 y2

theorem triangleFKTerminalPartition_eq (y0 y1 y2 : Real) :
    triangleFKTerminalPartition y0 y1 y2 =
      1 + y0 + y1 + y2 +
        (y0 * y1 + y1 * y2 + y2 * y0 + y0 * y1 * y2) := by
  have huniv : (Finset.univ : Finset ThreeTerminalConnectivity) =
      {.separate, .pair01, .pair12, .pair20, .together} := by decide
  rw [triangleFKTerminalPartition, huniv]
  simp [triangleFKTerminalWeight]
  ring

theorem starFKTerminalPartition_eq (q y0 y1 y2 : Real) :
    starFKTerminalPartition q y0 y1 y2 =
      q + y0 + y1 + y2 + y0 * y1 + y1 * y2 + y2 * y0 +
        y0 * y1 * y2 := by
  have huniv : (Finset.univ : Finset ThreeTerminalConnectivity) =
      {.separate, .pair01, .pair12, .pair20, .together} := by decide
  rw [starFKTerminalPartition, huniv]
  simp [starFKTerminalWeight]
  ring

theorem triangleFKTerminalPartition_pos
    {y0 y1 y2 : Real} (hy0 : 0 < y0) (hy1 : 0 < y1) (hy2 : 0 < y2) :
    0 < triangleFKTerminalPartition y0 y1 y2 := by
  rw [triangleFKTerminalPartition_eq]
  positivity

theorem starFKTerminalPartition_pos
    {q y0 y1 y2 : Real} (hq : 0 < q)
    (hy0 : 0 < y0) (hy1 : 0 < y1) (hy2 : 0 < y2) :
    0 < starFKTerminalPartition q y0 y1 y2 := by
  rw [starFKTerminalPartition_eq]
  positivity

theorem triangleFKTerminalProbability_sum_eq_one
    {y0 y1 y2 : Real} (hy0 : 0 < y0) (hy1 : 0 < y1) (hy2 : 0 < y2) :
    (∑ c, triangleFKTerminalProbability y0 y1 y2 c) = 1 := by
  unfold triangleFKTerminalProbability triangleFKTerminalPartition
  rw [← Finset.sum_div]
  exact div_self (triangleFKTerminalPartition_pos hy0 hy1 hy2).ne'

theorem starFKTerminalProbability_sum_eq_one
    {q y0 y1 y2 : Real} (hq : 0 < q)
    (hy0 : 0 < y0) (hy1 : 0 < y1) (hy2 : 0 < y2) :
    (∑ c, starFKTerminalProbability q y0 y1 y2 c) = 1 := by
  unfold starFKTerminalProbability starFKTerminalPartition
  rw [← Finset.sum_div]
  exact div_self (starFKTerminalPartition_pos hq hy0 hy1 hy2).ne'




theorem triHexFK_terminalWeight_identity
    {q y0 y1 y2 y0Star y1Star y2Star : Real}
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : triangularFKCriticalSurface q y0 y1 y2 = 0)
    (c : ThreeTerminalConnectivity) :
    (y0 * y1 * y2) *
        starFKTerminalWeight q y0Star y1Star y2Star c =
      q ^ 2 * triangleFKTerminalWeight y0 y1 y2 c := by
  have hcritical :
      y0 * y1 * y2 + y0 * y1 + y1 * y2 + y2 * y0 = q := by
    unfold triangularFKCriticalSurface at hsurface
    linarith
  cases c with
  | separate =>
      simp only [starFKTerminalWeight, triangleFKTerminalWeight, mul_one]
      calc
        (y0 * y1 * y2) * (q + y0Star + y1Star + y2Star) =
            q * (y0 * y1 * y2) +
              (y0 * y0Star) * y1 * y2 +
              (y1 * y1Star) * y2 * y0 +
              (y2 * y2Star) * y0 * y1 := by ring
        _ = q * (y0 * y1 * y2 + y0 * y1 + y1 * y2 + y2 * y0) := by
          rw [h0, h1, h2]
          ring
        _ = q ^ 2 := by rw [hcritical]; ring
  | pair01 =>
      simp only [starFKTerminalWeight, triangleFKTerminalWeight]
      calc
        (y0 * y1 * y2) * (y0Star * y1Star) =
            (y0 * y0Star) * (y1 * y1Star) * y2 := by ring
        _ = q ^ 2 * y2 := by rw [h0, h1]; ring
  | pair12 =>
      simp only [starFKTerminalWeight, triangleFKTerminalWeight]
      calc
        (y0 * y1 * y2) * (y1Star * y2Star) =
            (y1 * y1Star) * (y2 * y2Star) * y0 := by ring
        _ = q ^ 2 * y0 := by rw [h1, h2]; ring
  | pair20 =>
      simp only [starFKTerminalWeight, triangleFKTerminalWeight]
      calc
        (y0 * y1 * y2) * (y2Star * y0Star) =
            (y2 * y2Star) * (y0 * y0Star) * y1 := by ring
        _ = q ^ 2 * y1 := by rw [h2, h0]; ring
  | together =>
      simp only [starFKTerminalWeight, triangleFKTerminalWeight]
      calc
        (y0 * y1 * y2) * (y0Star * y1Star * y2Star) =
            (y0 * y0Star) * (y1 * y1Star) * (y2 * y2Star) := by ring
        _ = q ^ 3 := by rw [h0, h1, h2]; ring
        _ = q ^ 2 *
            (y0 * y1 + y1 * y2 + y2 * y0 + y0 * y1 * y2) := by
          rw [show y0 * y1 + y1 * y2 + y2 * y0 + y0 * y1 * y2 = q by
            linarith [hcritical]]
          ring



theorem triHexFK_terminalPartition_identity
    {q y0 y1 y2 y0Star y1Star y2Star : Real}
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : triangularFKCriticalSurface q y0 y1 y2 = 0) :
    (y0 * y1 * y2) *
        starFKTerminalPartition q y0Star y1Star y2Star =
      q ^ 2 * triangleFKTerminalPartition y0 y1 y2 := by
  unfold starFKTerminalPartition triangleFKTerminalPartition
  rw [mul_sum, mul_sum]
  apply sum_congr rfl
  intro c _
  exact triHexFK_terminalWeight_identity h0 h1 h2 hsurface c




theorem triHexFK_terminalProbability_eq
    {q y0 y1 y2 y0Star y1Star y2Star : Real}
    (hq : 0 < q)
    (hy0 : 0 < y0) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hy0Star : 0 < y0Star) (hy1Star : 0 < y1Star)
    (hy2Star : 0 < y2Star)
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : triangularFKCriticalSurface q y0 y1 y2 = 0)
    (c : ThreeTerminalConnectivity) :
    starFKTerminalProbability q y0Star y1Star y2Star c =
      triangleFKTerminalProbability y0 y1 y2 c := by
  have hprod : y0 * y1 * y2 ≠ 0 := by positivity
  have htriZ : triangleFKTerminalPartition y0 y1 y2 ≠ 0 :=
    (triangleFKTerminalPartition_pos hy0 hy1 hy2).ne'
  have hstarZ : starFKTerminalPartition q y0Star y1Star y2Star ≠ 0 :=
    (starFKTerminalPartition_pos hq hy0Star hy1Star hy2Star).ne'
  have hweight := triHexFK_terminalWeight_identity
    h0 h1 h2 hsurface c
  have hpartition := triHexFK_terminalPartition_identity
    h0 h1 h2 hsurface
  unfold starFKTerminalProbability triangleFKTerminalProbability
  apply (div_eq_div_iff hstarZ htriZ).2
  apply (mul_left_cancel₀ hprod)
  calc
    (y0 * y1 * y2) *
        (starFKTerminalWeight q y0Star y1Star y2Star c *
          triangleFKTerminalPartition y0 y1 y2) =
      ((y0 * y1 * y2) *
          starFKTerminalWeight q y0Star y1Star y2Star c) *
        triangleFKTerminalPartition y0 y1 y2 := by ring
    _ = (q ^ 2 * triangleFKTerminalWeight y0 y1 y2 c) *
        triangleFKTerminalPartition y0 y1 y2 := by rw [hweight]
    _ = triangleFKTerminalWeight y0 y1 y2 c *
        (q ^ 2 * triangleFKTerminalPartition y0 y1 y2) := by ring
    _ = triangleFKTerminalWeight y0 y1 y2 c *
        ((y0 * y1 * y2) *
          starFKTerminalPartition q y0Star y1Star y2Star) := by
      rw [hpartition]
    _ = (y0 * y1 * y2) *
        (triangleFKTerminalWeight y0 y1 y2 c *
          starFKTerminalPartition q y0Star y1Star y2Star) := by ring


theorem triHexFK_terminalLaw_eq
    {q y0 y1 y2 y0Star y1Star y2Star : Real}
    (hq : 0 < q)
    (hy0 : 0 < y0) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hy0Star : 0 < y0Star) (hy1Star : 0 < y1Star)
    (hy2Star : 0 < y2Star)
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : triangularFKCriticalSurface q y0 y1 y2 = 0) :
    starFKTerminalProbability q y0Star y1Star y2Star =
      triangleFKTerminalProbability y0 y1 y2 := by
  funext c
  exact triHexFK_terminalProbability_eq hq hy0 hy1 hy2
    hy0Star hy1Star hy2Star h0 h1 h2 hsurface c



theorem triHexFK_terminalLaw_dualParam
    {q p0 p1 p2 : Real}
    (hq : 0 < q) (hp0 : p0 ∈ Set.Ioo (0 : Real) 1)
    (hp1 : p1 ∈ Set.Ioo (0 : Real) 1)
    (hp2 : p2 ∈ Set.Ioo (0 : Real) 1)
    (hsurface : triangularFKCriticalSurface q
      (fkEdgeOdds p0) (fkEdgeOdds p1) (fkEdgeOdds p2) = 0) :
    starFKTerminalProbability q
        (fkEdgeOdds (BeffaraDC.dualParam p0 q))
        (fkEdgeOdds (BeffaraDC.dualParam p1 q))
        (fkEdgeOdds (BeffaraDC.dualParam p2 q)) =
      triangleFKTerminalProbability
        (fkEdgeOdds p0) (fkEdgeOdds p1) (fkEdgeOdds p2) := by
  have odds_pos {p : Real} (hp : p ∈ Set.Ioo (0 : Real) 1) :
      0 < fkEdgeOdds p := by
    exact div_pos hp.1 (sub_pos.mpr hp.2)
  have dual_odds_pos {p : Real} (hp : p ∈ Set.Ioo (0 : Real) 1) :
      0 < fkEdgeOdds (BeffaraDC.dualParam p q) := by
    exact odds_pos (BeffaraDC.dualParam_mem_Ioo hp.1 hp.2 hq)
  exact triHexFK_terminalLaw_eq hq
    (odds_pos hp0) (odds_pos hp1) (odds_pos hp2)
    (dual_odds_pos hp0) (dual_odds_pos hp1) (dual_odds_pos hp2)
    (fkEdgeOdds_mul_dualParam hp0.1 hp0.2 hq)
    (fkEdgeOdds_mul_dualParam hp1.1 hp1.2 hq)
    (fkEdgeOdds_mul_dualParam hp2.1 hp2.2 hq) hsurface

end PeriodicPlanar
end FK
end StatMech
