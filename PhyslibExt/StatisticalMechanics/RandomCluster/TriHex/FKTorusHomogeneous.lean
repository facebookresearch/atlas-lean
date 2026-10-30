/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKTorusSweep

/-!
# Homogeneous star–triangle transformation on the tori

Specialization of the torus star–triangle identities to homogeneous edge parameters: the
triangular torus at `p` and the hexagonal torus at the dual parameter `dualParam p q`.

## i. Overview

For constant edge parameter `p` on the triangular torus and `p* = dualParam p q` on the
hexagonal torus, the edge odds are the constant direction odds `y = p / (1 - p)` and
`y* = p* / (1 - p*)` with `y y* = q`. When `y` solves the triangular critical cubic
`y ^ 3 + 3 y ^ 2 = q`, the results of `FKTorusSweep` give equality of every sector-observable
expectation and of the two-point functions of the two tori. Unconditional, given `q > 0`,
`p ∈ (0, 1)` and the critical cubic at `p` (i.e. at the triangular self-dual point).

## ii. Key results

- `triHexFK_torus_homogeneous_activeSectorRatio_eq` : homogeneous equality of sector
  expectations. Unconditional (given the critical cubic).
- `triHexFK_torus_homogeneous_activeTwoPointRatio_eq` : the hexagonal-torus white two-point
  function at `p*` equals the triangular-torus two-point function at `p`. Unconditional (given
  the critical cubic).

## iii. Table of contents

- A. Constant edge odds
- B. Homogeneous star–triangle identities

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), §6.6.
-/

@[expose] public section

namespace StatMech.FK.PeriodicPlanar

open Set

noncomputable section

/-! ## A. Constant edge odds -/

private lemma constant_triangularTorus_odds
    (L : Nat) [Fact (2 < L)] {p : Real} (hp1 : p < 1)
    (e : (triangularTorusGraph L).edgeSet) :
    p = (1 - p) * triangularTorusSweepEdgeOdds L
      (FrontierA.fkEdgeOdds p) (FrontierA.fkEdgeOdds p)
      (FrontierA.fkEdgeOdds p) e := by
  have hden : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp1))
  unfold triangularTorusSweepEdgeOdds
  generalize ((triHexTorusTriangleSweepEdgeEquiv L).symm e).2 = i
  fin_cases i <;>
    simp [triHexDirectionOdds, FrontierA.fkEdgeOdds] <;>
    field_simp [hden]

private lemma constant_hexagonalTorus_odds
    (L : Nat) [Fact (2 < L)] {p : Real} (hp1 : p < 1)
    (e : (hexagonalTorusGraph L).edgeSet) :
    p = (1 - p) * hexagonalTorusSweepEdgeOdds L
      (FrontierA.fkEdgeOdds p) (FrontierA.fkEdgeOdds p)
      (FrontierA.fkEdgeOdds p) e := by
  have hden : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp1))
  unfold hexagonalTorusSweepEdgeOdds
  generalize ((triHexTorusStarSweepEdgeEquiv L).symm e).2 = i
  fin_cases i <;>
    simp [triHexDirectionOdds, FrontierA.fkEdgeOdds] <;>
    field_simp [hden]

/-! ## B. Homogeneous star–triangle identities -/

lemma triHexFK_torus_homogeneous_activeSectorRatio_eq
    (L : Nat) [Fact (2 < L)] {q p : Real}
    (hq : 0 < q) (hp : p ∈ Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0)
    (observable : (TorusSite L → ThreeTerminalConnectivity) → Real) :
    activeNumer (hexagonalTorusGraph L)
          (fun _ => BeffaraDC.dualParam p q) q
          (hexagonalTorusSectorObservable L observable) /
        activeZ (hexagonalTorusGraph L)
          (fun _ => BeffaraDC.dualParam p q) q =
      activeNumer (triangularTorusGraph L) (fun _ => p) q
          (triangularTorusSectorObservable L observable) /
        activeZ (triangularTorusGraph L) (fun _ => p) q := by
  let pStar := BeffaraDC.dualParam p q
  have hpStar : pStar ∈ Ioo (0 : Real) 1 :=
    BeffaraDC.dualParam_mem_Ioo hp.1 hp.2 hq
  have hy : 0 < FrontierA.fkEdgeOdds p :=
    div_pos hp.1 (sub_pos.mpr hp.2)
  have hdual := FrontierA.fkEdgeOdds_mul_dualParam hp.1 hp.2 hq
  apply triHexFK_torus_activeSectorRatio_eq L (fun _ => p)
    (fun _ => pStar) hq.ne' (mul_ne_zero (mul_ne_zero hy.ne' hy.ne') hy.ne')
  · intro e
    exact ne_of_lt hp.2
  · intro e
    exact ne_of_lt hpStar.2
  · intro e
    exact constant_triangularTorus_odds L hp.2 e
  · intro e
    exact constant_hexagonalTorus_odds L hpStar.2 e
  · exact hdual
  · exact hdual
  · exact hdual
  · rwa [FrontierA.triangularFKCriticalSurface_diagonal]

/-- Star–triangle transformation of homogeneous FK two-point functions on the torus: at the
triangular self-dual point, the hexagonal-torus connection probability of white vertices at
`dualParam p q` equals the triangular-torus connection probability at `p` (Grimmett, *The
Random-Cluster Model*, §6.6). -/
theorem triHexFK_torus_homogeneous_activeTwoPointRatio_eq
    (L : Nat) [Fact (2 < L)] {q p : Real}
    (hq : 0 < q) (hp : p ∈ Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0)
    (x y : TorusSite L) :
    activeNumer (hexagonalTorusGraph L)
          (fun _ => BeffaraDC.dualParam p q) q
          (hexagonalTorusActiveWhiteTwoPointIndicator L x y) /
        activeZ (hexagonalTorusGraph L)
          (fun _ => BeffaraDC.dualParam p q) q =
      activeNumer (triangularTorusGraph L) (fun _ => p) q
          (triangularTorusActiveTwoPointIndicator L x y) /
        activeZ (triangularTorusGraph L) (fun _ => p) q := by
  have hratio := triHexFK_torus_homogeneous_activeSectorRatio_eq
    L hq hp hsurface
      (triHexFKTerminalTwoPointObservable (triHexTorusCellTerminal L) x y)
  have htri : triangularTorusSectorObservable L
      (triHexFKTerminalTwoPointObservable (triHexTorusCellTerminal L) x y) =
        triangularTorusActiveTwoPointIndicator L x y := by
    funext omega
    exact triangularTorusSectorTwoPointObservable_eq_indicator L x y omega
  have hhex : hexagonalTorusSectorObservable L
      (triHexFKTerminalTwoPointObservable (triHexTorusCellTerminal L) x y) =
        hexagonalTorusActiveWhiteTwoPointIndicator L x y := by
    funext omega
    exact hexagonalTorusSectorTwoPointObservable_eq_indicator L x y omega
  simpa [htri, hhex] using hratio

end

end StatMech.FK.PeriodicPlanar
