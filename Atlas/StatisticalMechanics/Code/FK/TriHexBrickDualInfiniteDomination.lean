/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexBrickFreeCofinal





open Filter Finset MeasureTheory Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC

noncomputable section




theorem hexagonalFreeInfinite_faceDual_le_wiredTriangularBox
    (N : Nat) (hN : 1 ≤ N)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
    (hA : IsIncreasing A) :
    (hexagonal.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 HexVertex))).real
        (triHexFaceDualInnerEvent N A) ≤
      activeBCMean (triangularBoxGraph N)
        (boundaryCliqueGraph (triHexBrickInnerBoundary N))
        (fun _ => dualParam p q) q
        (A.indicator fun _ => (1 : Real)) := by
  let U : (m : Nat) →
      Finset (ConfigSpace (Sym2 (TriHexPlanarFiniteStarVertex m))) :=
    fun _ => Finset.univ
  let k : Nat → Nat := fun j => N + 3 + j
  let L : Nat → Nat := fun j =>
    triHexPlanarHexBufferedOuterStarLevel (k j)
  have hNL : ∀ j, N < L j := by
    intro j
    dsimp only [L, k]
    unfold triHexPlanarHexBufferedOuterStarLevel
    have hj : N + 3 + j ≤
        hexagonal.bufferedRadius (N + 3 + j + 1) :=
      (Nat.le_succ (N + 3 + j)).trans
        (hexagonal.id_le_bufferedRadius (N + 3 + j + 1))
    omega
  let s : Nat → Real := fun j =>
    ∑ rho ∈ U (L j),
      (triHexStarFaceDualInnerEvent
        (hNL j) A).indicator (fun _ => (1 : Real)) rho *
        fkProb (triHexPlanarFiniteStarGraph (L j)) p q rho
  have hs : Tendsto s atTop
      (nhds ((hexagonal.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 HexVertex))).real
        (triHexFaceDualInnerEvent N A))) := by
    simpa only [s, U, L, k] using
      triHexFreeOuterStarFaceDualInnerEvent_tendsto
        N hp hp1 hq A hA
  apply le_of_tendsto hs
  filter_upwards [] with j
  have hfinite :=
    triHexBrick_freeStarDual_inner_dominated_wiredTriangular
      (hNL j) hN hp hp1 hq hA
  have hvertexFintype :
      kwg_vertexFintype (triHexPlanarFiniteStarPlanar (L j)) =
        (inferInstance : Fintype
          (TriHexPlanarFiniteStarVertex (L j))) :=
    Subsingleton.elim _ _
  have hvertexDecidable :
      (triHexPlanarFiniteStarPlanar (L j)).decV =
        (inferInstance : DecidableEq
          (TriHexPlanarFiniteStarVertex (L j))) :=
    Subsingleton.elim _ _
  have hadjDecidable :
      kwg_adjDecidable (triHexPlanarFiniteStarPlanar (L j)) =
        triHexPlanarFiniteStarGraphDecidable (L j) :=
    Subsingleton.elim _ _
  rw [hvertexFintype, hvertexDecidable, hadjDecidable] at hfinite
  dsimp only [s]
  simpa only [U, triHexStarFaceDualInnerEvent, Set.indicator,
    Set.mem_setOf_eq, triHexPlanarFiniteStarPlanar_graph] using hfinite




theorem freeTriangularBox_le_hexagonalFreeInfinite_faceDual
    (N : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
    (hA : IsIncreasing A) :
    activeBCMean (triangularBoxGraph N) ⊥
        (fun _ => dualParam p q) q
        (A.indicator fun _ => (1 : Real)) ≤
      (hexagonal.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 HexVertex))).real
          (triHexFaceDualInnerEvent N A) := by
  let U : (m : Nat) →
      Finset (ConfigSpace (Sym2 (TriHexPlanarFiniteStarVertex m))) :=
    fun _ => Finset.univ
  let k : Nat → Nat := fun j => N + 3 + j
  let L : Nat → Nat := fun j =>
    triHexPlanarHexBufferedOuterStarLevel (k j)
  have hNL : ∀ j, N < L j := by
    intro j
    dsimp only [L, k]
    unfold triHexPlanarHexBufferedOuterStarLevel
    have hj : N + 3 + j ≤
        hexagonal.bufferedRadius (N + 3 + j + 1) :=
      (Nat.le_succ (N + 3 + j)).trans
        (hexagonal.id_le_bufferedRadius (N + 3 + j + 1))
    omega
  let s : Nat → Real := fun j =>
    ∑ rho ∈ U (L j),
      (triHexStarFaceDualInnerEvent
        (hNL j) A).indicator (fun _ => (1 : Real)) rho *
        fkProb (triHexPlanarFiniteStarGraph (L j)) p q rho
  have hs : Tendsto s atTop
      (nhds ((hexagonal.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 HexVertex))).real
        (triHexFaceDualInnerEvent N A))) := by
    simpa only [s, U, L, k] using
      triHexFreeOuterStarFaceDualInnerEvent_tendsto
        N hp hp1 hq A hA
  apply ge_of_tendsto hs
  filter_upwards [] with j
  have hfinite :=
    triHexBrick_freeTriangular_dominated_freeStarDual_inner
      (hNL j) hp hp1 hq hA
  have hvertexFintype :
      kwg_vertexFintype (triHexPlanarFiniteStarPlanar (L j)) =
        (inferInstance : Fintype
          (TriHexPlanarFiniteStarVertex (L j))) :=
    Subsingleton.elim _ _
  have hvertexDecidable :
      (triHexPlanarFiniteStarPlanar (L j)).decV =
        (inferInstance : DecidableEq
          (TriHexPlanarFiniteStarVertex (L j))) :=
    Subsingleton.elim _ _
  have hadjDecidable :
      kwg_adjDecidable (triHexPlanarFiniteStarPlanar (L j)) =
        triHexPlanarFiniteStarGraphDecidable (L j) :=
    Subsingleton.elim _ _
  rw [hvertexFintype, hvertexDecidable, hadjDecidable] at hfinite
  dsimp only [s]
  simpa only [U, triHexStarFaceDualInnerEvent, Set.indicator,
    Set.mem_setOf_eq, triHexPlanarFiniteStarPlanar_graph] using hfinite

end

end StatMech.FK.PeriodicPlanar
