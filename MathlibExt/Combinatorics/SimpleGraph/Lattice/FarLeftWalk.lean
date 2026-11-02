/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.StraightWalk

/-!
# Walking to the far left around a finite set

A finite set `F` of sites of the square lattice lies to the right of some column `x = b`. From
any site `z` strictly left of that column, the straight horizontal walk further left to any
column `M ≤ z 0` stays in row `z 1` and never meets `F`. This is the elementary step used to
show that the far-left half-plane of `F`'s complement is connected and reachable.

The file does not prove that the complement of a finite set is connected; see
`StatMech.Lattice.unique_infinite_component` for the infinite component of the complement and
`StatMech.Lattice.arcns_farLeft_connected` for connectivity of the far-left half-plane.

## Main results

* `StatMech.Lattice.fcc_xLowerBound`: a finite set of sites has a lower bound on its first
  coordinate.
* `StatMech.Lattice.fcc_far_reach_off_finite`: there is a column `b` left of which every site
  reaches any further-left site `(M, z 1)` of its row by a walk avoiding `F`.
-/

@[expose] public section

open Set
open SimpleGraph

namespace StatMech

namespace Lattice

/-- A finite set of sites has a lower bound `b` on its first coordinate. -/
theorem fcc_xLowerBound (F : Set (Site 2)) (hF : F.Finite) :
    ∃ b : ℤ, ∀ q ∈ F, b ≤ q 0 := by
  have him : ((fun q : Site 2 => q 0) '' F).Finite := hF.image _
  obtain ⟨b, hb⟩ := him.bddBelow
  exact ⟨b, fun q hq => hb ⟨q, hq, rfl⟩⟩

/-- If every site of `F` has first coordinate at least `b` and `z 0 < b`, the horizontal walk
from `z` to `(M, z 1)` with `M ≤ z 0` avoids `F`. -/
theorem fcc_horizWalk_off_finite (F : Set (Site 2)) (b : ℤ)
    (hb : ∀ q ∈ F, b ≤ q 0) (z : Site 2) (hz : z 0 < b) (M : ℤ) (hM : M ≤ z 0) :
    ∀ w ∈ (sw_horizSeg (z 1) (z 0) M).support, w ∉ F := by
  intro w hw hwF
  rw [sw_horizSeg_mem_support] at hw
  obtain ⟨t, ht, rfl⟩ := hw
  rw [Set.uIcc_of_ge hM] at ht
  obtain ⟨_, htr⟩ := ht
  have hble : b ≤ (![t, z 1] : Site 2) 0 := hb _ hwF
  simp only [Matrix.cons_val_zero] at hble
  linarith

/-- For a finite set `F` there is a column `b` bounding `F` on the left such that every site `z`
with `z 0 ≤ b - 1` is joined to `(M, z 1)`, for any `M ≤ z 0`, by a walk avoiding `F`; the
endpoint is again left of all of `F`. -/
theorem fcc_far_reach_off_finite (F : Set (Site 2)) (hF : F.Finite) :
    ∃ b : ℤ, (∀ q ∈ F, b ≤ q 0) ∧
      ∀ z : Site 2, z 0 ≤ b - 1 → ∀ M : ℤ, M ≤ z 0 →
        ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
          (∀ w ∈ p.support, w ∉ F) ∧
          (∀ q ∈ F, z0 0 ≤ q 0) ∧
          z0 = ![M, z 1] := by
  obtain ⟨b, hb⟩ := fcc_xLowerBound F hF
  refine ⟨b, hb, fun z hz M hM => ?_⟩
  have hzb : z 0 < b := by linarith
  have hstart : (![z 0, z 1] : Site 2) = z := by
    funext i; fin_cases i <;> rfl
  refine ⟨![M, z 1],
    (sw_horizSeg (z 1) (z 0) M).copy hstart rfl, ?_, ?_, rfl⟩
  · intro w hw
    rw [Walk.support_copy] at hw
    exact fcc_horizWalk_off_finite F b hb z hzb M hM w hw
  · intro q hq
    have : b ≤ q 0 := hb q hq
    simp only [Matrix.cons_val_zero]
    linarith

end Lattice

end StatMech
