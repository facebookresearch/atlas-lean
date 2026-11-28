/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.DataStructures.RangeTree.OrthogonalReporting
meta import Mathlib.Data.Int.Order.Basic

/-! # Orthogonal reporting fixtures -/

namespace Cslib.Algorithms.Lean.RangeTree.OrthogonalReporting

private abbrev Point := Int × Int × Int

private def axis (i : Nat) (p : Point) : Int :=
  match i with
  | 0 => p.1
  | 1 => p.2.1
  | _ => p.2.2

private def sample : List Point :=
  [(2, 2, 3), (1, 2, 1), (0, 2, 2), (1, 2, 1), (1, 3, 1), (1, 2, 2), (3, 2, 1)]

-- A non-power-of-two tree. The nodes are maximal, ordered and disjoint;
-- an empty, reversed or singleton query never follows an invalid edge.
example : positionCover 1 6 3 ⟨0, 7⟩ = [⟨1, 2⟩, ⟨3, 2⟩, ⟨5, 1⟩] := by decide
example : positionCover 4 2 3 ⟨0, 7⟩ = [] := by decide
example : positionCover 0 9 0 ⟨0, 0⟩ = [] := by decide
example : positionCover 1 2 0 ⟨1, 1⟩ = [⟨1, 1⟩] := by decide

-- Equal keys define distinct occurrences. The true prefix below key 2
-- is of length 2; its child rank is 1, even though one tie follows it.
private def tiedCatalog : List (Int × Nat) := [(1, 0), (1, 1), (2, 2), (2, 3), (5, 4)]
private def evenTag (p : Int × Nat) : Bool := p.2 % 2 == 0
private def belowTwo (p : Int × Nat) : Bool := decide (p.1 < 2)

example : (catalogCutoff tiedCatalog.toArray belowTwo).1 = 2 := by decide
#guard catalogTransfer tiedCatalog evenTag == #[0, 1, 1, 2, 2, 3]
#guard (catalogTransfer tiedCatalog evenTag)[5]? == some 3

-- Empty data, one input, coincident points, closed endpoints, inverted intervals.
#guard (OrdinaryIndex.build (fun _ (x : Int) => x) 0 []).cells == 0
#guard (LayeredIndex.build axis 0 []).cells == 0
#guard ((LayeredIndex.build axis 0 []).report [] (1, 1) (2, 2) rfl).points == []
#guard ((OrdinaryIndex.build (fun _ (x : Int) => x) 0 [4]).report [] (4, 4) rfl).points == [4]
#guard ((OrdinaryIndex.build (fun _ (x : Int) => x) 0 [4]).report [] (5, 2) rfl).points == []
#guard ((OrdinaryIndex.build (fun _ (x : Int) => x) 0 [4, 1, 3, 4, 2]).report [] (3, 4) rfl).points =
    [3, 4, 4]
#guard ((LayeredIndex.build axis 0 [(1, 2, 3)]).report [] (1, 1) (2, 2) rfl).points =
    [(1, 2, 3)]
#guard ((LayeredIndex.build axis 0 [(1, 2, 3)]).report [] (1, 1) (2, 1) rfl).points == []

-- The same three-dimensional box is answered with or without terminal cascading.
#guard ((OrdinaryIndex.build axis 2 sample).report [(1, 1), (2, 2)] (1, 2) rfl).points =
    [(1, 2, 1), (1, 2, 1), (1, 2, 2)]
#guard ((LayeredIndex.build axis 1 sample).report [(1, 1)] (2, 2) (1, 2) rfl).points =
    [(1, 2, 1), (1, 2, 1), (1, 2, 2)]
#guard ((LayeredIndex.build axis 1 sample).report [(0, 3)] (3, 1) (1, 2) rfl).points == []

example (p : Point) :
    p ∈ ((LayeredIndex.build axis 1 sample).report [(1, 1)] (2, 2) (1, 2) rfl).points ↔
      p ∈ sample.filter (inBox axis [(1, 1), (2, 2), (1, 2)]) :=
  (layeredRangeReporting axis sample [(1, 1)] (2, 2) (1, 2)).1.mem_iff

section PlanarCases
-- The payload distinguishes tied entries without becoming a third query axis.
private abbrev PlanarPoint := Int × Int × Nat
private def planarAxis (i : Nat) (p : PlanarPoint) : Int := if i = 0 then p.1 else p.2.1

private def ordinary (xs : List PlanarPoint) (qx qy : Int × Int) : Result PlanarPoint :=
  (OrdinaryIndex.build planarAxis 1 xs).report [qx] qy rfl

private def layered (xs : List PlanarPoint) (qx qy : Int × Int) : Result PlanarPoint :=
  (LayeredIndex.build planarAxis 0 xs).report [] qx qy rfl

-- Concentrated-output family: n = 2^(2m), x = i, y = 0 on [2^m,2^(m+1)) and at
-- 2^(m+1), …, 2^(2m-1), y = 1 elsewhere. Query [1,n-1] × [0,0].
-- At m = 3 the eight hits in [8,16) are in the left result of each of
-- [0,32) and [0,64), with one additional right hit at each join.
-- Reverse the input to ensure the oracle is about walk order, not input order.
private def concentrated : List PlanarPoint :=
  (List.range 64).reverse.map fun i =>
    (Int.ofNat i, if (8 ≤ i ∧ i < 16) ∨ i = 16 ∨ i = 32 then 0 else 1, i)

private def concentratedExpected : List PlanarPoint :=
  [(8,0,8), (9,0,9), (10,0,10), (11,0,11), (12,0,12), (13,0,13), (14,0,14),
   (15,0,15), (16,0,16), (32,0,32)]

private def concentratedO := ordinary concentrated (1,63) (0,0)
private def concentratedL := layered concentrated (1,63) (0,0)

#guard concentratedO.points == concentratedExpected
#guard concentratedL.points == concentratedExpected

-- [1,64) in x-rank space takes 13 visits and 13 x probes. The six
-- ordinary y subqueries add 65; layered adds only 13 root y probes.
#guard concentratedO.search ≤ 91
#guard concentratedL.search ≤ 39
#guard concentratedO.work == concentratedO.search + 10
#guard concentratedL.work == concentratedL.search + 10

-- x-rank spans [1,2), [2,4), [4,8), [8,16) yield 0, 1, 4, 2 hits.
-- The three equal x/y keys at x = 5 retain payload order 52,51,52;
-- the two copies of (5,1,52) are literally identical. At x = 0 there
-- is an in-y-band point outside the x interval; y = 0 and y = 3 miss.
private def tied : List PlanarPoint :=
  [(8,1,80), (5,1,52), (14,3,140), (4,2,40), (2,2,20), (0,1,0),
   (10,2,100), (5,1,51), (1,3,10), (3,0,30), (15,0,150), (12,3,120),
   (9,3,90), (5,1,52), (11,0,110), (13,0,130)]

-- Both planar APIs use left-to-right x-canonical order, then stable y
-- order within a node: ordinary sorts each x-span by y; layered restricts
-- the stable global y catalog to that span. Neither globally sorts the output by y.
private def tiedExpected : List PlanarPoint :=
  [(2,2,20), (5,1,52), (5,1,51), (5,1,52), (4,2,40), (8,1,80), (10,2,100)]

private def tiedO := ordinary tied (1,15) (1,2)
private def tiedL := layered tied (1,15) (1,2)

#guard tiedO.points == tiedExpected
#guard tiedL.points == tiedExpected
-- Nine outer visits + nine x probes; ordinary y adds 32, layered y adds 8.
#guard tiedO.search ≤ 50
#guard tiedL.search ≤ 26
#guard tiedO.work == tiedO.search + 7
#guard tiedL.work == tiedL.search + 7

-- A nonempty x cover with both y bounds at the final gap in every catalog.
private def missO := ordinary tied (1,15) (4,4)
private def missL := layered tied (1,15) (4,4)

#guard missO.points.isEmpty
#guard missL.points.isEmpty
#guard missO.search ≤ 36
#guard missL.search ≤ 26
#guard missO.work == missO.search
#guard missL.work == missL.search

-- Repair-only: check actual reported insertion counts against independent
-- literals, then the public work identity for both reporting paths.
#guard concentratedO.emitted == 10
#guard concentratedL.emitted == 10
#guard tiedO.emitted == 7
#guard tiedL.emitted == 7
#guard missO.emitted == 0
#guard missL.emitted == 0
#guard concentratedO.work == concentratedO.search + concentratedO.emitted
#guard concentratedL.work == concentratedL.search + concentratedL.emitted
#guard tiedO.work == tiedO.search + tiedO.emitted
#guard tiedL.work == tiedL.search + tiedL.emitted
#guard missO.work == missO.search + missO.emitted
#guard missL.work == missL.search + missL.emitted
end PlanarCases

end Cslib.Algorithms.Lean.RangeTree.OrthogonalReporting
