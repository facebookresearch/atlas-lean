/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKTorusHomogeneous

/-!
# Star–triangle invariance of torus connection probabilities to a target set

At the triangular self-dual point, the probability that a vertex is connected to a target set
is the same for the triangular torus at `p` and for the white vertices of the hexagonal torus at
`dualParam p q`.

## i. Overview

`triangularTorusActiveReachEvent L x target` is the event that `x` is joined by open edges of the
triangular torus to some vertex of `target`; `hexagonalTorusActiveWhiteReachEvent` is the same for
the white vertices of the hexagonal torus. Both are sector observables (connectivity in the
terminal sector graph, `triHexFKTerminalReachIndicator`), so the homogeneous torus identity of
`FKTorusHomogeneous` gives equality of their FK probabilities. Unconditional, given `q > 0`,
`p ∈ (0, 1)` and the triangular critical cubic at `p`.

## ii. Key results

- `triHexFK_torus_homogeneous_activeReachProbability_eq` : equality of the hexagonal and
  triangular torus FK probabilities of `x ↔ target`. Unconditional (given the critical cubic).

## iii. Table of contents

- A. Connection events and indicators
- B. Sector form of the indicators
- C. Equality of connection probabilities

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), §6.6.
-/

@[expose] public section

namespace StatMech.FK.PeriodicPlanar

open Set

noncomputable section

/-! ## A. Connection events and indicators -/

/-- The indicator that `x` is joined to some vertex of `target` in the torus terminal sector graph.
-/
def triHexFKTerminalReachIndicator
    (L : Nat) [Fact (2 < L)] (x : TorusSite L)
    (target : Finset (TorusSite L))
    (sector : TorusSite L → ThreeTerminalConnectivity) : Real := by
  classical
  exact if ∃ y ∈ target,
    (triHexFKTerminalSectorGraph (triHexTorusCellTerminal L) sector).Reachable x y
  then 1 else 0

/-- The indicator that `x` is joined by open edges of the triangular torus to some vertex of
`target`. -/
def triangularTorusActiveReachIndicator
    (L : Nat) [Fact (2 < L)] (x : TorusSite L)
    (target : Finset (TorusSite L))
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet) : Real :=
  if ∃ y ∈ target,
      (openSub (triangularTorusGraph L)
        (extendActive (triangularTorusGraph L) omega)).Reachable x y
    then 1 else 0

/-- The indicator that the white vertex of `x` is joined by open edges of the hexagonal torus to the
white vertex of some element of `target`. -/
def hexagonalTorusActiveWhiteReachIndicator
    (L : Nat) [Fact (2 < L)] (x : TorusSite L)
    (target : Finset (TorusSite L))
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) : Real :=
  if ∃ y ∈ target,
      (openSub (hexagonalTorusGraph L)
        (extendActive (hexagonalTorusGraph L) omega)).Reachable
          (x, true) (y, true)
    then 1 else 0

/-- The event that `x` is joined by open edges of the triangular torus to `target`. -/
def triangularTorusActiveReachEvent
    (L : Nat) [Fact (2 < L)] (x : TorusSite L)
    (target : Finset (TorusSite L)) :
    Set (ConfigSpace (triangularTorusGraph L).edgeSet) :=
  {omega | ∃ y ∈ target,
    (openSub (triangularTorusGraph L)
      (extendActive (triangularTorusGraph L) omega)).Reachable x y}

/-- The event that the white vertex of `x` is joined by open edges of the hexagonal torus to the
white vertices of `target`. -/
def hexagonalTorusActiveWhiteReachEvent
    (L : Nat) [Fact (2 < L)] (x : TorusSite L)
    (target : Finset (TorusSite L)) :
    Set (ConfigSpace (hexagonalTorusGraph L).edgeSet) :=
  {omega | ∃ y ∈ target,
    (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Reachable
        (x, true) (y, true)}

/-! ## B. Sector form of the indicators -/

lemma triangularTorusActiveReachIndicator_eq_eventIndicator
    (L : Nat) [Fact (2 < L)] (x : TorusSite L)
    (target : Finset (TorusSite L)) :
    triangularTorusActiveReachIndicator L x target =
      (triangularTorusActiveReachEvent L x target).indicator
        (fun _ => (1 : Real)) := by
  funext omega
  classical
  simp only [triangularTorusActiveReachIndicator,
    triangularTorusActiveReachEvent, Set.indicator, Set.mem_ofPred_eq]
  congr

lemma hexagonalTorusActiveWhiteReachIndicator_eq_eventIndicator
    (L : Nat) [Fact (2 < L)] (x : TorusSite L)
    (target : Finset (TorusSite L)) :
    hexagonalTorusActiveWhiteReachIndicator L x target =
      (hexagonalTorusActiveWhiteReachEvent L x target).indicator
        (fun _ => (1 : Real)) := by
  funext omega
  classical
  simp only [hexagonalTorusActiveWhiteReachIndicator,
    hexagonalTorusActiveWhiteReachEvent, Set.indicator, Set.mem_ofPred_eq]
  congr

lemma triangularTorusSectorReachObservable_eq_indicator
    (L : Nat) [Fact (2 < L)] (x : TorusSite L)
    (target : Finset (TorusSite L))
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet) :
    triangularTorusSectorObservable L
        (triHexFKTerminalReachIndicator L x target) omega =
      triangularTorusActiveReachIndicator L x target omega := by
  classical
  unfold triangularTorusSectorObservable triHexFKTerminalReachIndicator
    triangularTorusActiveReachIndicator
  change (if ∃ y ∈ target,
      (triangularTorusTerminalSectorGraph L omega).Reachable x y
    then 1 else 0) =
    if ∃ y ∈ target,
      (openSub (triangularTorusGraph L)
        (extendActive (triangularTorusGraph L) omega)).Reachable x y
    then 1 else 0
  congr 1
  apply propext
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy,
      (triangularTorus_openSub_reachable_iff_terminalSectorGraph
        L omega x y).mpr hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy,
      (triangularTorus_openSub_reachable_iff_terminalSectorGraph
        L omega x y).mp hxy⟩

lemma hexagonalTorusSectorReachObservable_eq_indicator
    (L : Nat) [Fact (2 < L)] (x : TorusSite L)
    (target : Finset (TorusSite L))
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) :
    hexagonalTorusSectorObservable L
        (triHexFKTerminalReachIndicator L x target) omega =
      hexagonalTorusActiveWhiteReachIndicator L x target omega := by
  classical
  unfold hexagonalTorusSectorObservable triHexFKTerminalReachIndicator
    hexagonalTorusActiveWhiteReachIndicator
  change (if ∃ y ∈ target,
      (hexagonalTorusTerminalSectorGraph L omega).Reachable x y
    then 1 else 0) =
    if ∃ y ∈ target,
      (openSub (hexagonalTorusGraph L)
        (extendActive (hexagonalTorusGraph L) omega)).Reachable
          (x, true) (y, true)
    then 1 else 0
  congr 1
  apply propext
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy,
      (hexagonalTorus_openSub_white_reachable_iff_terminalSectorGraph
        L omega x y).mpr hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy,
      (hexagonalTorus_openSub_white_reachable_iff_terminalSectorGraph
        L omega x y).mp hxy⟩

/-! ## C. Equality of connection probabilities -/

lemma triHexFK_torus_homogeneous_activeReachRatio_eq
    (L : Nat) [Fact (2 < L)] {q p : Real}
    (hq : 0 < q) (hp : p ∈ Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0)
    (x : TorusSite L) (target : Finset (TorusSite L)) :
    activeNumer (hexagonalTorusGraph L)
          (fun _ => BeffaraDC.dualParam p q) q
          (hexagonalTorusActiveWhiteReachIndicator L x target) /
        activeZ (hexagonalTorusGraph L)
          (fun _ => BeffaraDC.dualParam p q) q =
      activeNumer (triangularTorusGraph L) (fun _ => p) q
          (triangularTorusActiveReachIndicator L x target) /
        activeZ (triangularTorusGraph L) (fun _ => p) q := by
  have hratio := triHexFK_torus_homogeneous_activeSectorRatio_eq
    L hq hp hsurface (triHexFKTerminalReachIndicator L x target)
  have htri : triangularTorusSectorObservable L
      (triHexFKTerminalReachIndicator L x target) =
        triangularTorusActiveReachIndicator L x target := by
    funext omega
    exact triangularTorusSectorReachObservable_eq_indicator
      L x target omega
  have hhex : hexagonalTorusSectorObservable L
      (triHexFKTerminalReachIndicator L x target) =
        hexagonalTorusActiveWhiteReachIndicator L x target := by
    funext omega
    exact hexagonalTorusSectorReachObservable_eq_indicator
      L x target omega
  simpa [htri, hhex] using hratio

/-- Star–triangle transformation of torus connection probabilities: at the triangular self-dual
point, `φ_hex,p*(x ↔ target) = φ_tri,p(x ↔ target)` on the torus (Grimmett, *The Random-Cluster
Model*, §6.6). -/
theorem triHexFK_torus_homogeneous_activeReachProbability_eq
    (L : Nat) [Fact (2 < L)] {q p : Real}
    (hq : 0 < q) (hp : p ∈ Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0)
    (x : TorusSite L) (target : Finset (TorusSite L)) :
    activeProbOf (hexagonalTorusGraph L)
        (fun _ => BeffaraDC.dualParam p q) q
        (hexagonalTorusActiveWhiteReachEvent L x target) =
      activeProbOf (triangularTorusGraph L) (fun _ => p) q
        (triangularTorusActiveReachEvent L x target) := by
  rw [activeProbOf, activeProbOf,
    activeMean_eq_div, activeMean_eq_div,
    ← triangularTorusActiveReachIndicator_eq_eventIndicator,
    ← hexagonalTorusActiveWhiteReachIndicator_eq_eventIndicator]
  exact triHexFK_torus_homogeneous_activeReachRatio_eq
    L hq hp hsurface x target

end

end StatMech.FK.PeriodicPlanar
