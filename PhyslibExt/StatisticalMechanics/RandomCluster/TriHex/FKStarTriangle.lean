/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKDuality

/-!
# Star–triangle transformation for the random-cluster model

The FK star–triangle transformation: on the triangular critical surface, a triangle with edge
odds `y` and a star with dual odds `y*` induce the same law on the connectivity of their three
terminals.

## i. Overview

A triangle (three edges between three terminals) and a star (three edges from a center to the
terminals) are the two local pieces exchanged by the star–triangle move.
`ThreeTerminalConnectivity` lists the five partitions of the terminals induced by the open edges.
`triangleFKTerminalWeight y` and `starFKTerminalWeight q y*` are the FK weights (edge odds times
`q` per cluster not containing a terminal) of each partition, and the corresponding normalized
laws are `triangleFKTerminalProbability` and `starFKTerminalProbability`. The main result is that
if `yᵢ yᵢ* = q` and `y` lies on the triangular critical surface, then the star weights are
`q ^ 2 / (y₀ y₁ y₂)` times the triangle weights, so the two terminal laws coincide. This is the
local identity behind the star–triangle transformation of Baxter–Temperley–Ashley (Grimmett,
*The Random-Cluster Model*, §6.6). All results are unconditional for the stated positive odds,
with the critical-surface equation as an explicit hypothesis.

## ii. Key results

- `triHexFK_terminalWeight_identity` : on the critical surface, `y₀ y₁ y₂ · star = q ^ 2 · triangle`
  for each terminal partition. Unconditional (given the surface equation).
- `triHexFK_terminalLaw_eq` : equality of the star and triangle terminal laws for positive odds on
  the critical surface. Unconditional (given the surface equation).
- `triHexFK_terminalLaw_dualParam` : the same for edge parameters `pᵢ ∈ (0, 1)` and the dual
  parameters `dualParam pᵢ q`. Unconditional (given the surface equation).

## iii. Table of contents

- A. Terminal connectivity and local FK weights
- B. Partition functions and terminal laws
- C. The star–triangle identity

## iv. References

- R. J. Baxter, H. N. V. Temperley and S. E. Ashley, *Triangular Potts model at its transition
  temperature, and related models*, Proc. R. Soc. Lond. A 358 (1978) 535–559.
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), §6.6.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace StatMech
namespace FK
namespace PeriodicPlanar

open FrontierA

/-! ## A. Terminal connectivity and local FK weights -/

/-- The five partitions of three terminals `0, 1, 2` that open edges of a triangle or a star can
induce: all separate, one of the three pairs joined, or all together. -/
inductive ThreeTerminalConnectivity
  | separate
  | pair01
  | pair12
  | pair20
  | together
  deriving DecidableEq

/-- The five terminal partitions form a finite type. -/
instance instFintypeThreeTerminalConnectivity : Fintype ThreeTerminalConnectivity where
  elems := {.separate, .pair01, .pair12, .pair20, .together}
  complete := fun x => by cases x <;> decide

/-- FK weight of each terminal partition for a triangle whose edge opposite terminal `i` has odds
`yᵢ`: the sum of the odds products of the open-edge sets inducing that partition. -/
def triangleFKTerminalWeight (y0 y1 y2 : Real) :
    ThreeTerminalConnectivity -> Real
  | .separate => 1
  | .pair01 => y2
  | .pair12 => y0
  | .pair20 => y1
  | .together => y0 * y1 + y1 * y2 + y2 * y0 + y0 * y1 * y2

/-- FK weight of each terminal partition for a star whose edge to terminal `i` has odds `yᵢ`; the
isolated center carries an extra cluster factor `q`. -/
def starFKTerminalWeight (q y0 y1 y2 : Real) :
    ThreeTerminalConnectivity -> Real
  | .separate => q + y0 + y1 + y2
  | .pair01 => y0 * y1
  | .pair12 => y1 * y2
  | .pair20 => y2 * y0
  | .together => y0 * y1 * y2

/-! ## B. Partition functions and terminal laws -/

/-- Local partition function of the triangle: the sum of its terminal weights. -/
def triangleFKTerminalPartition (y0 y1 y2 : Real) : Real :=
  ∑ c, triangleFKTerminalWeight y0 y1 y2 c

/-- Local partition function of the star: the sum of its terminal weights. -/
def starFKTerminalPartition (q y0 y1 y2 : Real) : Real :=
  ∑ c, starFKTerminalWeight q y0 y1 y2 c

/-- The law of the terminal partition induced by an FK triangle. -/
noncomputable def triangleFKTerminalProbability (y0 y1 y2 : Real)
    (c : ThreeTerminalConnectivity) : Real :=
  triangleFKTerminalWeight y0 y1 y2 c /
    triangleFKTerminalPartition y0 y1 y2

/-- The law of the terminal partition induced by an FK star. -/
noncomputable def starFKTerminalProbability (q y0 y1 y2 : Real)
    (c : ThreeTerminalConnectivity) : Real :=
  starFKTerminalWeight q y0 y1 y2 c /
    starFKTerminalPartition q y0 y1 y2

lemma triangleFKTerminalPartition_eq (y0 y1 y2 : Real) :
    triangleFKTerminalPartition y0 y1 y2 =
      1 + y0 + y1 + y2 +
        (y0 * y1 + y1 * y2 + y2 * y0 + y0 * y1 * y2) := by
  have huniv : (Finset.univ : Finset ThreeTerminalConnectivity) =
      {.separate, .pair01, .pair12, .pair20, .together} := by decide
  rw [triangleFKTerminalPartition, huniv]
  simp [triangleFKTerminalWeight]
  ring

lemma starFKTerminalPartition_eq (q y0 y1 y2 : Real) :
    starFKTerminalPartition q y0 y1 y2 =
      q + y0 + y1 + y2 + y0 * y1 + y1 * y2 + y2 * y0 +
        y0 * y1 * y2 := by
  have huniv : (Finset.univ : Finset ThreeTerminalConnectivity) =
      {.separate, .pair01, .pair12, .pair20, .together} := by decide
  rw [starFKTerminalPartition, huniv]
  simp [starFKTerminalWeight]
  ring

lemma triangleFKTerminalPartition_pos
    {y0 y1 y2 : Real} (hy0 : 0 < y0) (hy1 : 0 < y1) (hy2 : 0 < y2) :
    0 < triangleFKTerminalPartition y0 y1 y2 := by
  rw [triangleFKTerminalPartition_eq]
  positivity

lemma starFKTerminalPartition_pos
    {q y0 y1 y2 : Real} (hq : 0 < q)
    (hy0 : 0 < y0) (hy1 : 0 < y1) (hy2 : 0 < y2) :
    0 < starFKTerminalPartition q y0 y1 y2 := by
  rw [starFKTerminalPartition_eq]
  positivity

lemma triangleFKTerminalProbability_sum_eq_one
    {y0 y1 y2 : Real} (hy0 : 0 < y0) (hy1 : 0 < y1) (hy2 : 0 < y2) :
    (∑ c, triangleFKTerminalProbability y0 y1 y2 c) = 1 := by
  unfold triangleFKTerminalProbability triangleFKTerminalPartition
  rw [← Finset.sum_div]
  exact div_self (triangleFKTerminalPartition_pos hy0 hy1 hy2).ne'

lemma starFKTerminalProbability_sum_eq_one
    {q y0 y1 y2 : Real} (hq : 0 < q)
    (hy0 : 0 < y0) (hy1 : 0 < y1) (hy2 : 0 < y2) :
    (∑ c, starFKTerminalProbability q y0 y1 y2 c) = 1 := by
  unfold starFKTerminalProbability starFKTerminalPartition
  rw [← Finset.sum_div]
  exact div_self (starFKTerminalPartition_pos hq hy0 hy1 hy2).ne'

/-! ## C. The star–triangle identity -/

lemma triHexFK_terminalWeight_identity
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

lemma triHexFK_terminalPartition_identity
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

lemma triHexFK_terminalProbability_eq
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

/-- Star–triangle transformation for the random-cluster model: on the triangular critical surface
with dual odds `yᵢ yᵢ* = q`, the star and the triangle induce the same terminal-connectivity law
(Baxter–Temperley–Ashley 1978; Grimmett, *The Random-Cluster Model*, §6.6). -/
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

/-- Star–triangle transformation in edge parameters: for `pᵢ ∈ (0, 1)` on the triangular critical
surface, the star with the dual parameters `dualParam pᵢ q` and the triangle with parameters `pᵢ`
induce the same terminal law (Grimmett, *The Random-Cluster Model*, §6.6). -/
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
