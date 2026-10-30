/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKFiniteWiredGraphs
public import PhyslibExt.StatisticalMechanics.RandomCluster.InfiniteVolume
public import PhyslibExt.StatisticalMechanics.RandomCluster.ActiveBoundaryEquiv

/-!
# Star–triangle equality of finite-volume wired FK boundary-connection probabilities

The finite wired FK measures on the triangle and star graphs of a planar box, expressed through
the cell sums of `FKFiniteWiredSweep`; at the triangular self-dual point the hexagonal and
triangular probabilities that the root is connected to the boundary coincide.

## i. Overview

`wiredActiveWeight`, `wiredActiveZ`, `wiredActiveNumer` and `wiredActiveRatio` are the wired FK
weight, partition function, unnormalized expectation and expectation of an observable of the
active (graph) edges, defined from `wiredFkWeight` through `extendActive`; the ratio is the
expectation under the genuine finite-volume wired FK measure `wiredFkProb`
(`wiredActiveRatio_eq_wiredFkProb_lift`). For the finite triangle and star graphs of
`FKFiniteWiredGraphs`, with homogeneous edge parameter `p` of odds `y`, the wired weights factor as
a closed-edge product times the cell sums, so the wired FK probability that the root terminal is
connected to the boundary equals the abstract `triangleFK…`/`starFK…` boundary-reach ratios. With
the dual parameter on the star graph this gives
`triHexPlanarFiniteWiredBoundaryProbability_eq_homogeneous`: at the triangular self-dual point,
`φ¹_{hex, p*}(root ↔ ∂) = φ¹_{tri, p}(root ↔ ∂)` in every finite box. Unconditional, given
`q > 0`, `p ∈ (0, 1)` and the triangular critical cubic at `p`.

## ii. Key results

- `wiredActiveRatio_eq_wiredFkProb_lift` : the active-edge ratio is the wired FK expectation.
  Unconditional.
- `triHexPlanarFiniteTriangleWiredBoundaryProbability_eq`,
  `triHexPlanarFiniteStarWiredBoundaryProbability_eq` : wired boundary-connection probabilities
  as cell sums. Unconditional.
- `triHexPlanarFiniteWiredBoundaryProbability_eq_homogeneous` : finite-volume star–triangle
  equality of wired boundary-connection probabilities. Unconditional (given the critical cubic).

## iii. Table of contents

- A. Wired FK weights of active-edge configurations
- B. The triangle graph
- C. The star graph
- D. Wired boundary-connection probabilities

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), §§4.1, 6.6.
-/

@[expose] public section

open Finset Set
open scoped BigOperators

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

/-! ## A. Wired FK weights of active-edge configurations -/

/-- The wired FK weight of a configuration of the edges of `G`, extended by closed edges off `G`. -/
def wiredActiveWeight {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (boundary : V → Prop) [DecidablePred boundary]
    (p q : Real) (omega : ConfigSpace G.edgeSet) : Real :=
  wiredFkWeight G boundary p q (extendActive G omega)

/-- The wired FK partition function of `G`, summed over active-edge configurations. -/
def wiredActiveZ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (boundary : V → Prop) [DecidablePred boundary]
    (p q : Real) : Real :=
  ∑ omega : ConfigSpace G.edgeSet,
    wiredActiveWeight G boundary p q omega

/-- The unnormalized wired FK expectation of an active-edge observable. -/
def wiredActiveNumer {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (boundary : V → Prop) [DecidablePred boundary]
    (p q : Real) (observable : ConfigSpace G.edgeSet → Real) : Real :=
  ∑ omega : ConfigSpace G.edgeSet,
    observable omega * wiredActiveWeight G boundary p q omega

/-- The wired FK expectation of an active-edge observable. -/
def wiredActiveRatio {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (boundary : V → Prop) [DecidablePred boundary]
    (p q : Real) (observable : ConfigSpace G.edgeSet → Real) : Real :=
  wiredActiveNumer G boundary p q observable /
    wiredActiveZ G boundary p q

lemma wiredActiveRatio_eq_wiredFkProb_lift
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (boundary : V -> Prop) [DecidablePred boundary]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (observable : ConfigSpace G.edgeSet -> Real) :
    wiredActiveRatio G boundary p q observable =
      ∑ omega : ConfigSpace (Sym2 V),
        observable (restrictActive G omega) *
          wiredFkProb G boundary p q omega := by
  rw [← activeBCMean_boundaryClique_eq_wired G boundary hp hp1 hq]
  rw [activeBCMean_eq_div]
  unfold wiredActiveRatio wiredActiveNumer wiredActiveZ wiredActiveWeight
    activeBCNumer activeBCZ activeBCWeight wiredFkWeight
  simp only [numClustersBC_boundaryClique]
  rfl

/-! ## B. The triangle graph -/

lemma triHexPlanarFiniteTriangle_localOddsProduct
    (n : Nat) (y : Real)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet) :
    (∏ z, triangleFKLocalOddsWeight y y y
      (triHexPlanarFiniteTriangleConfigEquiv n omega z)) =
      ∏ e : (triHexPlanarFiniteTriangleGraph n).edgeSet,
        if omega e then y else 1 := by
  rw [triangleFKGlobalLocalOdds_eq_directionProduct]
  calc
    (∏ a : TriHexPlanarFiniteCell n × Fin 3,
        if triHexLocalDirection
            (triHexPlanarFiniteTriangleConfigEquiv n omega a.1) a.2 then
          triHexDirectionOdds y y y a.2 else 1) =
      ∏ a : TriHexPlanarFiniteCell n × Fin 3,
        if omega (triHexPlanarFiniteTriangleEdgeEquiv n a) then y else 1 := by
          apply Fintype.prod_congr
          rintro ⟨z, i⟩
          fin_cases i <;> rfl
    _ = ∏ e : (triHexPlanarFiniteTriangleGraph n).edgeSet,
        if omega e then y else 1 := by
      simpa using (triHexPlanarFiniteTriangleEdgeEquiv n).prod_comp
        (fun e => if omega e then y else 1)

lemma triHexPlanarFiniteTriangle_edgeProduct
    (n : Nat) {p y : Real} (hodds : p = (1 - p) * y)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet) :
    edgeProduct (triHexPlanarFiniteTriangleGraph n) p
        (extendActive (triHexPlanarFiniteTriangleGraph n) omega) =
      (∏ _e : (triHexPlanarFiniteTriangleGraph n).edgeSet, (1 - p)) *
        ∏ z, triangleFKLocalOddsWeight y y y
          (triHexPlanarFiniteTriangleConfigEquiv n omega z) := by
  change edgeProductW (triHexPlanarFiniteTriangleGraph n) (fun _ => p)
      (extendActive (triHexPlanarFiniteTriangleGraph n) omega) = _
  rw [edgeProductW_extendActive_odds_factor
    (triHexPlanarFiniteTriangleGraph n) (fun _ => p) (fun _ => y)
    (fun _ => hodds)]
  rw [triHexPlanarFiniteTriangle_localOddsProduct]

lemma triHexPlanarFiniteTriangle_wiredActiveWeight_eq
    (n : Nat) {p y q : Real} (hodds : p = (1 - p) * y)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet) :
    wiredActiveWeight (triHexPlanarFiniteTriangleGraph n)
        (triHexPlanarFiniteBoundary n) p q omega =
      (∏ _e : (triHexPlanarFiniteTriangleGraph n).edgeSet, (1 - p)) *
        (triHexFKTerminalWiredExternal q
            (triHexPlanarFiniteTerminalMap n)
            (triHexPlanarFiniteBoundary n)
            (fun z => triangleFKLocalConnectivity
              (triHexPlanarFiniteTriangleConfigEquiv n omega z)) *
          ∏ z, triangleFKLocalOddsWeight y y y
            (triHexPlanarFiniteTriangleConfigEquiv n omega z)) := by
  unfold wiredActiveWeight wiredFkWeight
  rw [triHexPlanarFiniteTriangle_edgeProduct n hodds,
    triHexPlanarFiniteTriangle_numClustersWired_eq_sector]
  unfold triHexFKTerminalWiredExternal
    triHexPlanarFiniteTriangleWiredSectorGraph
  ring

lemma triHexPlanarFiniteTriangle_wiredActiveZ_eq
    (n : Nat) {p y q : Real} (hodds : p = (1 - p) * y) :
    wiredActiveZ (triHexPlanarFiniteTriangleGraph n)
        (triHexPlanarFiniteBoundary n) p q =
      (∏ _e : (triHexPlanarFiniteTriangleGraph n).edgeSet, (1 - p)) *
        triangleFKGlobalConfigSum y y y
          (triHexFKTerminalWiredExternal q
            (triHexPlanarFiniteTerminalMap n)
            (triHexPlanarFiniteBoundary n)) := by
  classical
  unfold wiredActiveZ triangleFKGlobalConfigSum
  rw [← (triHexPlanarFiniteTriangleConfigEquiv n).symm.sum_comp
    (fun omega => wiredActiveWeight (triHexPlanarFiniteTriangleGraph n)
      (triHexPlanarFiniteBoundary n) p q omega)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro config _
  rw [triHexPlanarFiniteTriangle_wiredActiveWeight_eq n hodds]
  rw [(triHexPlanarFiniteTriangleConfigEquiv n).apply_symm_apply config]

/-- The indicator that the root terminal is joined by open edges of the finite triangle graph to a
boundary terminal. -/
def triHexPlanarFiniteTriangleBoundaryReachIndicator (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet) : Real :=
  if ∃ y : TriHexPlanarFiniteTerminal n,
      triHexPlanarFiniteBoundary n y ∧
      (openSub (triHexPlanarFiniteTriangleGraph n)
        (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Reachable
          (triHexPlanarFiniteTerminalMap n
            (triHexPlanarFiniteRootCell n) 0) y then 1 else 0

lemma triHexPlanarFiniteTriangle_sectorBoundaryObservable_eq_indicator
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet) :
    triHexFKTerminalBoundaryReachObservable
        (triHexPlanarFiniteTerminalMap n)
        (triHexPlanarFiniteBoundary n)
        (triHexPlanarFiniteTerminalMap n (triHexPlanarFiniteRootCell n) 0)
        (fun z => triangleFKLocalConnectivity
          (triHexPlanarFiniteTriangleConfigEquiv n omega z)) =
      triHexPlanarFiniteTriangleBoundaryReachIndicator n omega := by
  classical
  unfold triHexFKTerminalBoundaryReachObservable
    triHexPlanarFiniteTriangleBoundaryReachIndicator
  congr 1
  apply propext
  constructor <;> rintro ⟨y, hy, hreach⟩
  · exact ⟨y, hy,
      (triHexPlanarFiniteTriangle_openSub_reachable_iff_sector
        n omega _ _).mpr hreach⟩
  · exact ⟨y, hy,
      (triHexPlanarFiniteTriangle_openSub_reachable_iff_sector
        n omega _ _).mp hreach⟩

lemma triHexPlanarFiniteTriangle_wiredActiveNumer_boundary_eq
    (n : Nat) {p y q : Real} (hodds : p = (1 - p) * y) :
    wiredActiveNumer (triHexPlanarFiniteTriangleGraph n)
        (triHexPlanarFiniteBoundary n) p q
        (triHexPlanarFiniteTriangleBoundaryReachIndicator n) =
      (∏ _e : (triHexPlanarFiniteTriangleGraph n).edgeSet, (1 - p)) *
        triangleFKGlobalConfigSum y y y
          (fun sector => triHexFKTerminalWiredExternal q
              (triHexPlanarFiniteTerminalMap n)
              (triHexPlanarFiniteBoundary n) sector *
            triHexFKTerminalBoundaryReachObservable
              (triHexPlanarFiniteTerminalMap n)
              (triHexPlanarFiniteBoundary n)
              (triHexPlanarFiniteTerminalMap n
                (triHexPlanarFiniteRootCell n) 0) sector) := by
  classical
  unfold wiredActiveNumer triangleFKGlobalConfigSum
  rw [← (triHexPlanarFiniteTriangleConfigEquiv n).symm.sum_comp
    (fun omega => triHexPlanarFiniteTriangleBoundaryReachIndicator n omega *
      wiredActiveWeight (triHexPlanarFiniteTriangleGraph n)
        (triHexPlanarFiniteBoundary n) p q omega)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro config _
  rw [triHexPlanarFiniteTriangle_wiredActiveWeight_eq n hodds]
  rw [← triHexPlanarFiniteTriangle_sectorBoundaryObservable_eq_indicator
    n ((triHexPlanarFiniteTriangleConfigEquiv n).symm config)]
  rw [(triHexPlanarFiniteTriangleConfigEquiv n).apply_symm_apply config]
  ring

lemma triHexPlanarFiniteTriangle_wiredActiveRatio_eq
    (n : Nat) {p y q : Real} (hp1 : p ≠ 1)
    (hodds : p = (1 - p) * y) :
    wiredActiveRatio (triHexPlanarFiniteTriangleGraph n)
        (triHexPlanarFiniteBoundary n) p q
        (triHexPlanarFiniteTriangleBoundaryReachIndicator n) =
      triangleFKFiniteWiredBoundaryReachRatio q y y y
        (triHexPlanarFiniteTerminalMap n)
        (triHexPlanarFiniteBoundary n)
        (triHexPlanarFiniteTerminalMap n
          (triHexPlanarFiniteRootCell n) 0) := by
  unfold wiredActiveRatio triangleFKFiniteWiredBoundaryReachRatio
  rw [triHexPlanarFiniteTriangle_wiredActiveNumer_boundary_eq n hodds,
    triHexPlanarFiniteTriangle_wiredActiveZ_eq n hodds]
  apply mul_div_mul_left
  rw [Finset.prod_ne_zero_iff]
  intro _ _
  exact sub_ne_zero.mpr (Ne.symm hp1)

/-! ## C. The star graph -/

lemma triHexPlanarFiniteStar_isolatedCenterFactor_product
    (n : Nat) (q : Real)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    (∏ z, starFKIsolatedCenterFactor q
      (triHexPlanarFiniteStarConfigEquiv n omega z)) =
      q ^ Fintype.card (TriHexPlanarFiniteStarIsolatedCenter n omega) := by
  unfold starFKIsolatedCenterFactor TriHexPlanarFiniteStarIsolatedCenter
  have h := @fintype_prod_ite_eq_pow_card_subtype
    (TriHexPlanarFiniteCell n) inferInstance
      (fun z => triHexPlanarFiniteStarConfigEquiv n omega z =
        (false, false, false)) inferInstance inferInstance q
  rw [h]

lemma triHexPlanarFiniteStar_localOddsProduct
    (n : Nat) (q y : Real)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    (∏ z, starFKLocalOddsWeight q y y y
      (triHexPlanarFiniteStarConfigEquiv n omega z)) =
      q ^ Fintype.card (TriHexPlanarFiniteStarIsolatedCenter n omega) *
        ∏ e : (triHexPlanarFiniteStarGraph n).edgeSet,
          if omega e then y else 1 := by
  rw [starFKGlobalLocalOdds_eq_isolated_mul_directionProduct,
    triHexPlanarFiniteStar_isolatedCenterFactor_product]
  congr 1
  calc
    (∏ a : TriHexPlanarFiniteCell n × Fin 3,
        if triHexLocalDirection
            (triHexPlanarFiniteStarConfigEquiv n omega a.1) a.2 then
          triHexDirectionOdds y y y a.2 else 1) =
      ∏ a : TriHexPlanarFiniteCell n × Fin 3,
        if omega (triHexPlanarFiniteStarEdgeEquiv n a) then y else 1 := by
          apply Fintype.prod_congr
          rintro ⟨z, i⟩
          fin_cases i <;> rfl
    _ = ∏ e : (triHexPlanarFiniteStarGraph n).edgeSet,
        if omega e then y else 1 := by
      simpa using (triHexPlanarFiniteStarEdgeEquiv n).prod_comp
        (fun e => if omega e then y else 1)

lemma triHexPlanarFiniteStar_edgeProduct
    (n : Nat) {p y : Real} (hodds : p = (1 - p) * y)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    edgeProduct (triHexPlanarFiniteStarGraph n) p
        (extendActive (triHexPlanarFiniteStarGraph n) omega) =
      (∏ _e : (triHexPlanarFiniteStarGraph n).edgeSet, (1 - p)) *
        ∏ e : (triHexPlanarFiniteStarGraph n).edgeSet,
          if omega e then y else 1 := by
  change edgeProductW (triHexPlanarFiniteStarGraph n) (fun _ => p)
      (extendActive (triHexPlanarFiniteStarGraph n) omega) = _
  exact edgeProductW_extendActive_odds_factor
    (triHexPlanarFiniteStarGraph n) (fun _ => p) (fun _ => y)
      (fun _ => hodds) omega

lemma triHexPlanarFiniteStar_wiredActiveWeight_eq
    (n : Nat) {p y q : Real} (hodds : p = (1 - p) * y)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    wiredActiveWeight (triHexPlanarFiniteStarGraph n)
        (triHexPlanarFiniteStarBoundary n) p q omega =
      (∏ _e : (triHexPlanarFiniteStarGraph n).edgeSet, (1 - p)) *
        (triHexFKTerminalWiredExternal q
            (triHexPlanarFiniteTerminalMap n)
            (triHexPlanarFiniteBoundary n)
            (fun z => starFKLocalConnectivity
              (triHexPlanarFiniteStarConfigEquiv n omega z)) *
          ∏ z, starFKLocalOddsWeight q y y y
            (triHexPlanarFiniteStarConfigEquiv n omega z)) := by
  unfold wiredActiveWeight wiredFkWeight
  rw [triHexPlanarFiniteStar_edgeProduct n hodds,
    triHexPlanarFiniteStar_numClustersWired_eq_sector_add_isolated,
    pow_add, triHexPlanarFiniteStar_localOddsProduct]
  unfold triHexFKTerminalWiredExternal
    triHexPlanarFiniteStarWiredSectorGraph
  ring

lemma triHexPlanarFiniteStar_wiredActiveZ_eq
    (n : Nat) {p y q : Real} (hodds : p = (1 - p) * y) :
    wiredActiveZ (triHexPlanarFiniteStarGraph n)
        (triHexPlanarFiniteStarBoundary n) p q =
      (∏ _e : (triHexPlanarFiniteStarGraph n).edgeSet, (1 - p)) *
        starFKGlobalConfigSum q y y y
          (triHexFKTerminalWiredExternal q
            (triHexPlanarFiniteTerminalMap n)
            (triHexPlanarFiniteBoundary n)) := by
  classical
  unfold wiredActiveZ starFKGlobalConfigSum
  rw [← (triHexPlanarFiniteStarConfigEquiv n).symm.sum_comp
    (fun omega => wiredActiveWeight (triHexPlanarFiniteStarGraph n)
      (triHexPlanarFiniteStarBoundary n) p q omega)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro config _
  rw [triHexPlanarFiniteStar_wiredActiveWeight_eq n hodds]
  rw [(triHexPlanarFiniteStarConfigEquiv n).apply_symm_apply config]

/-- The indicator that the root terminal is joined by open edges of the finite star graph to a
boundary terminal. -/
def triHexPlanarFiniteStarBoundaryReachIndicator (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) : Real :=
  if ∃ y : TriHexPlanarFiniteTerminal n,
      triHexPlanarFiniteBoundary n y ∧
      (openSub (triHexPlanarFiniteStarGraph n)
        (extendActive (triHexPlanarFiniteStarGraph n) omega)).Reachable
          (Sum.inr (triHexPlanarFiniteTerminalMap n
            (triHexPlanarFiniteRootCell n) 0)) (Sum.inr y) then 1 else 0

lemma triHexPlanarFiniteStar_sectorBoundaryObservable_eq_indicator
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    triHexFKTerminalBoundaryReachObservable
        (triHexPlanarFiniteTerminalMap n)
        (triHexPlanarFiniteBoundary n)
        (triHexPlanarFiniteTerminalMap n (triHexPlanarFiniteRootCell n) 0)
        (fun z => starFKLocalConnectivity
          (triHexPlanarFiniteStarConfigEquiv n omega z)) =
      triHexPlanarFiniteStarBoundaryReachIndicator n omega := by
  classical
  unfold triHexFKTerminalBoundaryReachObservable
    triHexPlanarFiniteStarBoundaryReachIndicator
  congr 1
  apply propext
  constructor <;> rintro ⟨y, hy, hreach⟩
  · exact ⟨y, hy,
      (triHexPlanarFiniteStar_openSub_white_reachable_iff_sector
        n omega _ _).mpr hreach⟩
  · exact ⟨y, hy,
      (triHexPlanarFiniteStar_openSub_white_reachable_iff_sector
        n omega _ _).mp hreach⟩

lemma triHexPlanarFiniteStar_wiredActiveNumer_boundary_eq
    (n : Nat) {p y q : Real} (hodds : p = (1 - p) * y) :
    wiredActiveNumer (triHexPlanarFiniteStarGraph n)
        (triHexPlanarFiniteStarBoundary n) p q
        (triHexPlanarFiniteStarBoundaryReachIndicator n) =
      (∏ _e : (triHexPlanarFiniteStarGraph n).edgeSet, (1 - p)) *
        starFKGlobalConfigSum q y y y
          (fun sector => triHexFKTerminalWiredExternal q
              (triHexPlanarFiniteTerminalMap n)
              (triHexPlanarFiniteBoundary n) sector *
            triHexFKTerminalBoundaryReachObservable
              (triHexPlanarFiniteTerminalMap n)
              (triHexPlanarFiniteBoundary n)
              (triHexPlanarFiniteTerminalMap n
                (triHexPlanarFiniteRootCell n) 0) sector) := by
  classical
  unfold wiredActiveNumer starFKGlobalConfigSum
  rw [← (triHexPlanarFiniteStarConfigEquiv n).symm.sum_comp
    (fun omega => triHexPlanarFiniteStarBoundaryReachIndicator n omega *
      wiredActiveWeight (triHexPlanarFiniteStarGraph n)
        (triHexPlanarFiniteStarBoundary n) p q omega)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro config _
  rw [triHexPlanarFiniteStar_wiredActiveWeight_eq n hodds]
  rw [← triHexPlanarFiniteStar_sectorBoundaryObservable_eq_indicator
    n ((triHexPlanarFiniteStarConfigEquiv n).symm config)]
  rw [(triHexPlanarFiniteStarConfigEquiv n).apply_symm_apply config]
  ring

lemma triHexPlanarFiniteStar_wiredActiveRatio_eq
    (n : Nat) {p y q : Real} (hp1 : p ≠ 1)
    (hodds : p = (1 - p) * y) :
    wiredActiveRatio (triHexPlanarFiniteStarGraph n)
        (triHexPlanarFiniteStarBoundary n) p q
        (triHexPlanarFiniteStarBoundaryReachIndicator n) =
      starFKFiniteWiredBoundaryReachRatio q y y y
        (triHexPlanarFiniteTerminalMap n)
        (triHexPlanarFiniteBoundary n)
        (triHexPlanarFiniteTerminalMap n
          (triHexPlanarFiniteRootCell n) 0) := by
  unfold wiredActiveRatio starFKFiniteWiredBoundaryReachRatio
  rw [triHexPlanarFiniteStar_wiredActiveNumer_boundary_eq n hodds,
    triHexPlanarFiniteStar_wiredActiveZ_eq n hodds]
  apply mul_div_mul_left
  rw [Finset.prod_ne_zero_iff]
  intro _ _
  exact sub_ne_zero.mpr (Ne.symm hp1)

/-! ## D. Wired boundary-connection probabilities -/

/-- The finite-volume wired FK probability on the triangle graph that the root is connected to the
boundary. -/
noncomputable def triHexPlanarFiniteTriangleWiredBoundaryProbability
    (n : Nat) (p q : Real) : Real :=
  ∑ omega : ConfigSpace (Sym2 (TriHexPlanarFiniteTerminal n)),
    triHexPlanarFiniteTriangleBoundaryReachIndicator n
        (restrictActive (triHexPlanarFiniteTriangleGraph n) omega) *
      wiredFkProb (triHexPlanarFiniteTriangleGraph n)
        (triHexPlanarFiniteBoundary n) p q omega

/-- The finite-volume wired FK probability on the star graph that the root is connected to the
boundary. -/
noncomputable def triHexPlanarFiniteStarWiredBoundaryProbability
    (n : Nat) (p q : Real) : Real :=
  ∑ omega : ConfigSpace (Sym2 (TriHexPlanarFiniteStarVertex n)),
    triHexPlanarFiniteStarBoundaryReachIndicator n
        (restrictActive (triHexPlanarFiniteStarGraph n) omega) *
      wiredFkProb (triHexPlanarFiniteStarGraph n)
        (triHexPlanarFiniteStarBoundary n) p q omega

lemma triHexPlanarFiniteTriangleWiredBoundaryProbability_eq
    (n : Nat) {p y q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hodds : p = (1 - p) * y) :
    triHexPlanarFiniteTriangleWiredBoundaryProbability n p q =
      triangleFKFiniteWiredBoundaryReachRatio q y y y
        (triHexPlanarFiniteTerminalMap n)
        (triHexPlanarFiniteBoundary n)
        (triHexPlanarFiniteTerminalMap n
          (triHexPlanarFiniteRootCell n) 0) := by
  rw [triHexPlanarFiniteTriangleWiredBoundaryProbability,
    ← wiredActiveRatio_eq_wiredFkProb_lift
      (triHexPlanarFiniteTriangleGraph n)
      (triHexPlanarFiniteBoundary n) hp hp1 hq]
  exact triHexPlanarFiniteTriangle_wiredActiveRatio_eq n hp1.ne hodds

lemma triHexPlanarFiniteStarWiredBoundaryProbability_eq
    (n : Nat) {p y q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hodds : p = (1 - p) * y) :
    triHexPlanarFiniteStarWiredBoundaryProbability n p q =
      starFKFiniteWiredBoundaryReachRatio q y y y
        (triHexPlanarFiniteTerminalMap n)
        (triHexPlanarFiniteBoundary n)
        (triHexPlanarFiniteTerminalMap n
          (triHexPlanarFiniteRootCell n) 0) := by
  rw [triHexPlanarFiniteStarWiredBoundaryProbability,
    ← wiredActiveRatio_eq_wiredFkProb_lift
      (triHexPlanarFiniteStarGraph n)
      (triHexPlanarFiniteStarBoundary n) hp hp1 hq]
  exact triHexPlanarFiniteStar_wiredActiveRatio_eq n hp1.ne hodds

/-- Finite-volume star–triangle transformation of wired boundary connection: at the triangular
self-dual point, the hexagonal wired probability at `dualParam p q` that the root reaches the
boundary equals the triangular one at `p` (Grimmett, *The Random-Cluster Model*, §6.6). -/
theorem triHexPlanarFiniteWiredBoundaryProbability_eq_homogeneous
    (n : Nat) {q p : Real} (hq : 0 < q)
    (hp : p ∈ Set.Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0) :
    triHexPlanarFiniteStarWiredBoundaryProbability n
        (BeffaraDC.dualParam p q) q =
      triHexPlanarFiniteTriangleWiredBoundaryProbability n p q := by
  have hpStar := BeffaraDC.dualParam_mem_Ioo hp.1 hp.2 hq
  have hodds (r : Real) (hr1 : r < 1) :
      r = (1 - r) * FrontierA.fkEdgeOdds r := by
    rw [FrontierA.fkEdgeOdds]
    field_simp [sub_ne_zero.mpr (Ne.symm hr1.ne)]
  rw [triHexPlanarFiniteStarWiredBoundaryProbability_eq n
      hpStar.1 hpStar.2 hq (hodds _ hpStar.2),
    triHexPlanarFiniteTriangleWiredBoundaryProbability_eq n
      hp.1 hp.2 hq (hodds _ hp.2)]
  exact triHexPlanarFiniteWiredBoundaryReachRatio_eq_homogeneous
    n hq hp hsurface

end

end StatMech.FK.PeriodicPlanar
