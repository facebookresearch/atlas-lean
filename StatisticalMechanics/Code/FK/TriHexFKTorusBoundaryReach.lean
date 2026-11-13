/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexFKTorusHomogeneous





namespace StatMech.FK.PeriodicPlanar

open Set

noncomputable section



def triHexFKTerminalReachIndicator
    (L : Nat) [Fact (2 < L)] (x : TorusSite L)
    (target : Finset (TorusSite L))
    (sector : TorusSite L → ThreeTerminalConnectivity) : Real := by
  classical
  exact if ∃ y ∈ target,
    (triHexFKTerminalSectorGraph (triHexTorusCellTerminal L) sector).Reachable x y
  then 1 else 0


def triangularTorusActiveReachIndicator
    (L : Nat) [Fact (2 < L)] (x : TorusSite L)
    (target : Finset (TorusSite L))
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet) : Real :=
  if ∃ y ∈ target,
      (openSub (triangularTorusGraph L)
        (extendActive (triangularTorusGraph L) omega)).Reachable x y
    then 1 else 0


def hexagonalTorusActiveWhiteReachIndicator
    (L : Nat) [Fact (2 < L)] (x : TorusSite L)
    (target : Finset (TorusSite L))
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) : Real :=
  if ∃ y ∈ target,
      (openSub (hexagonalTorusGraph L)
        (extendActive (hexagonalTorusGraph L) omega)).Reachable
          (x, true) (y, true)
    then 1 else 0


def triangularTorusActiveReachEvent
    (L : Nat) [Fact (2 < L)] (x : TorusSite L)
    (target : Finset (TorusSite L)) :
    Set (ConfigSpace (triangularTorusGraph L).edgeSet) :=
  {omega | ∃ y ∈ target,
    (openSub (triangularTorusGraph L)
      (extendActive (triangularTorusGraph L) omega)).Reachable x y}


def hexagonalTorusActiveWhiteReachEvent
    (L : Nat) [Fact (2 < L)] (x : TorusSite L)
    (target : Finset (TorusSite L)) :
    Set (ConfigSpace (hexagonalTorusGraph L).edgeSet) :=
  {omega | ∃ y ∈ target,
    (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Reachable
        (x, true) (y, true)}

theorem triangularTorusActiveReachIndicator_eq_eventIndicator
    (L : Nat) [Fact (2 < L)] (x : TorusSite L)
    (target : Finset (TorusSite L)) :
    triangularTorusActiveReachIndicator L x target =
      (triangularTorusActiveReachEvent L x target).indicator
        (fun _ => (1 : Real)) := by
  funext omega
  classical
  simp only [triangularTorusActiveReachIndicator,
    triangularTorusActiveReachEvent, Set.indicator, Set.mem_setOf_eq]

theorem hexagonalTorusActiveWhiteReachIndicator_eq_eventIndicator
    (L : Nat) [Fact (2 < L)] (x : TorusSite L)
    (target : Finset (TorusSite L)) :
    hexagonalTorusActiveWhiteReachIndicator L x target =
      (hexagonalTorusActiveWhiteReachEvent L x target).indicator
        (fun _ => (1 : Real)) := by
  funext omega
  classical
  simp only [hexagonalTorusActiveWhiteReachIndicator,
    hexagonalTorusActiveWhiteReachEvent, Set.indicator, Set.mem_setOf_eq]

theorem triangularTorusSectorReachObservable_eq_indicator
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

theorem hexagonalTorusSectorReachObservable_eq_indicator
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


theorem triHexFK_torus_homogeneous_activeReachRatio_eq
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
