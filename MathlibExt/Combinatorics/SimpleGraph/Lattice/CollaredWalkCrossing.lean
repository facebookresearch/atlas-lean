/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanExteriorClosure
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TwoPathsCrossWinding
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.StraightWalk

/-!
# Crossing walks in a rectangle, completed by straight collars

In the rectangle `rect alpha beta bottom top` of the square lattice, a walk `H` that runs from the
left side to the right side and a walk `V` that runs from the bottom to the top must share a site.
This file proves a version for walks that do not reach the sides: `V` (from `x` to `y`) is
completed by vertical collars down to the bottom row and up to the top row, and `H` (from `a` to
`b`) by horizontal collars out to the left and right columns. If the collars of one walk meet the
other walk's completion only at sites of the original walk, then `H` and `V` themselves share a
site.

## Main definitions

* `StatMech.Lattice.horizontalWallExtension alpha beta W`: the walk `W` from `x` to `y` extended
  by horizontal segments from column `alpha` to `x` and from `y` to column `beta`.

## Main results

* `StatMech.Lattice.horizontalWallExtension_support_rect`: the extension of a walk in the
  rectangle stays in the rectangle.
* `StatMech.Lattice.collaredWalks_meet_on_original_supports`: the collared crossing theorem.
-/

@[expose] public section

open SimpleGraph

namespace StatMech.Lattice

open StatMech.RSW.Box

noncomputable section

/-- The walk `W` from `x` to `y` with horizontal collars added: the horizontal segment from
`(alpha, x 1)` to `x`, then `W`, then the horizontal segment from `y` to `(beta, y 1)`. -/
def horizontalWallExtension (alpha beta : Int) {x y : Site 2}
    (W : (hypercubicLattice 2).Walk x y) :
    (hypercubicLattice 2).Walk ![alpha, x 1] ![beta, y 1] :=
  let W' : (hypercubicLattice 2).Walk
      ![x 0, x 1] ![y 0, y 1] := W.copy (by
        ext i
        fin_cases i <;> simp) (by
        ext i
        fin_cases i <;> simp)
  ((sw_horizSeg (x 1) alpha (x 0)).append W').append
    (sw_horizSeg (y 1) (y 0) beta)

/-- A site of the extended walk lies on the left collar, on `W`, or on the right collar. -/
theorem horizontalWallExtension_mem_support_iff
    (alpha beta : Int) {x y z : Site 2}
    (W : (hypercubicLattice 2).Walk x y) :
    z ∈ (horizontalWallExtension alpha beta W).support ↔
      z ∈ (sw_horizSeg (x 1) alpha (x 0)).support ∨
        z ∈ W.support ∨
          z ∈ (sw_horizSeg (y 1) (y 0) beta).support := by
  simp only [horizontalWallExtension, Walk.mem_support_append_iff,
    Walk.support_copy]
  tauto

/-- If `W` and its endpoints lie in the rectangle `[alpha, beta] × [bottom, top]`, so does its
horizontal extension. -/
theorem horizontalWallExtension_support_rect
    {alpha beta bottom top : Int} {x y : Site 2}
    (W : (hypercubicLattice 2).Walk x y)
    (hxBox : x ∈ rect alpha beta bottom top)
    (hyBox : y ∈ rect alpha beta bottom top)
    (hWBox : ∀ z ∈ W.support, z ∈ rect alpha beta bottom top) :
    ∀ z ∈ (horizontalWallExtension alpha beta W).support,
      z ∈ rect alpha beta bottom top := by
  intro z hz
  rw [horizontalWallExtension_mem_support_iff] at hz
  rcases hz with hz | hz | hz
  · rw [sw_horizSeg_mem_support] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    rw [Set.mem_uIcc] at ht
    rw [mem_rect] at hxBox ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · exact hWBox z hz
  · rw [sw_horizSeg_mem_support] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    rw [Set.mem_uIcc] at ht
    rw [mem_rect] at hyBox ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega

/-- Collared crossing theorem. Let `V` be a walk from `x` to `y` and `H` a walk from `a` to `b`,
all inside the rectangle `[alpha, beta] × [bottom, top]` with `alpha < beta`. Complete `V` by the
vertical segments from `(x 0, bottom)` to `x` and from `y` to `(y 0, top)`, and `H` by the
horizontal segments from `(alpha, a 1)` to `a` and from `b` to `(beta, b 1)`. If every site where
the completed `H` meets a vertical collar of `V` is a site of `V`, and every site where `V` meets
a horizontal collar of `H` is a site of `H`, then `H` and `V` share a site.

When `V` already joins the bottom row to the top row and `H` joins the left column to the right
column, the collars are single sites and the four meeting hypotheses hold trivially; the
statement then reduces to the standard fact that a top-bottom crossing and a left-right crossing
of a rectangle of the square lattice share a site. -/
theorem collaredWalks_meet_on_original_supports
    {alpha beta bottom top : Int}
    (hab : alpha < beta) (hbt : bottom ≤ top)
    {x y a b : Site 2}
    (V : (hypercubicLattice 2).Walk x y)
    (H : (hypercubicLattice 2).Walk a b)
    (hxBox : x ∈ rect alpha beta bottom top)
    (hyBox : y ∈ rect alpha beta bottom top)
    (haBox : a ∈ rect alpha beta bottom top)
    (hbBox : b ∈ rect alpha beta bottom top)
    (hVBox : ∀ z ∈ V.support, z ∈ rect alpha beta bottom top)
    (hHBox : ∀ z ∈ H.support, z ∈ rect alpha beta bottom top)
    (hLower : ∀ z ∈ (horizontalWallExtension alpha beta H).support,
      z ∈ (sw_vertSeg (x 0) bottom (x 1)).support → z ∈ V.support)
    (hUpper : ∀ z ∈ (horizontalWallExtension alpha beta H).support,
      z ∈ (sw_vertSeg (y 0) (y 1) top).support → z ∈ V.support)
    (hLeft : ∀ z ∈ V.support,
      z ∈ (sw_horizSeg (a 1) alpha (a 0)).support → z ∈ H.support)
    (hRight : ∀ z ∈ V.support,
      z ∈ (sw_horizSeg (b 1) (b 0) beta).support → z ∈ H.support) :
    ∃ z ∈ H.support, z ∈ V.support := by
  have hxCoord : (![x 0, x 1] : Site 2) = x := by
    ext i
    fin_cases i <;> simp
  have hyCoord : (![y 0, y 1] : Site 2) = y := by
    ext i
    fin_cases i <;> simp
  let lower : (hypercubicLattice 2).Walk ![x 0, bottom] x :=
    (sw_vertSeg (x 0) bottom (x 1)).copy rfl hxCoord
  let upper : (hypercubicLattice 2).Walk y ![y 0, top] :=
    (sw_vertSeg (y 0) (y 1) top).copy hyCoord rfl
  let Vc : (hypercubicLattice 2).Walk
      ![x 0, bottom] ![y 0, top] := (lower.append V).append upper
  have hVcBox : ∀ z ∈ Vc.support,
      z ∈ rect alpha beta bottom top := by
    intro z hz
    dsimp only [Vc] at hz
    rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff] at hz
    rcases hz with (hzLower | hzV) | hzUpper
    · dsimp only [lower] at hzLower
      rw [Walk.support_copy, sw_vertSeg_mem_support] at hzLower
      obtain ⟨t, ht, rfl⟩ := hzLower
      rw [Set.mem_uIcc] at ht
      rw [mem_rect] at hxBox ⊢
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · exact hVBox z hzV
    · dsimp only [upper] at hzUpper
      rw [Walk.support_copy, sw_vertSeg_mem_support] at hzUpper
      obtain ⟨t, ht, rfl⟩ := hzUpper
      rw [Set.mem_uIcc] at ht
      rw [mem_rect] at hyBox ⊢
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  let Hc := horizontalWallExtension alpha beta H
  have hHcBox : ∀ z ∈ Hc.support,
      z ∈ rect alpha beta bottom top :=
    horizontalWallExtension_support_rect H haBox hbBox hHBox
  have hsep : ArcSeparatingSet {z | z ∈ Vc.support}
      alpha beta bottom top := by
    have hxBounds := mem_rect.mp hxBox
    have hyBounds := mem_rect.mp hyBox
    exact jec_arcSeparatingSet alpha beta bottom top (x 0) (y 0)
      hab hbt hxBounds.1 hxBounds.2.1 hyBounds.1 hyBounds.2.1
        Vc hVcBox {z | z ∈ Vc.support} (fun _ hz => hz)
  have hHcStart : (![alpha, a 1] : Site 2) ∈
      rect alpha beta bottom top := by
    rw [mem_rect] at haBox ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hHcEnd : (![beta, b 1] : Site 2) ∈
      rect alpha beta bottom top := by
    rw [mem_rect] at hbBox ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  obtain ⟨z, hzHc, hzVc⟩ := tpc_two_paths_cross_of_sep hsep
    hHcStart hHcEnd (by simp) (by simp) Hc hHcBox
  have hzV : z ∈ V.support := by
    change z ∈ ((lower.append V).append upper).support at hzVc
    rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff] at hzVc
    rcases hzVc with (hzLower | hzV) | hzUpper
    · apply hLower z hzHc
      simpa [lower, Walk.support_copy] using hzLower
    · exact hzV
    · apply hUpper z hzHc
      simpa [upper, Walk.support_copy] using hzUpper
  have hzHCases :
      z ∈ (sw_horizSeg (a 1) alpha (a 0)).support ∨
        z ∈ H.support ∨
          z ∈ (sw_horizSeg (b 1) (b 0) beta).support := by
    exact (horizontalWallExtension_mem_support_iff alpha beta H).mp hzHc
  rcases hzHCases with hzLeft | hzH | hzRight
  · exact ⟨z, hLeft z hzV hzLeft, hzV⟩
  · exact ⟨z, hzH, hzV⟩
  · exact ⟨z, hRight z hzV hzRight, hzV⟩

end

end StatMech.Lattice
