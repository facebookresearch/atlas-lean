/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters

/-!
# Crossings of rectangles in bond percolation on `ℤ²`

For integers `a, b`, the rectangle `[0, a] × [0, b] ⊆ ℤ²` has a horizontal (left–right) open
crossing if some site on its left side is joined to some site on its right side by an open path
staying inside the rectangle, and similarly for vertical crossings. Crossing events are
increasing.

## Main definitions

* `StatMech.TwoDim.rectangle`: the rectangle `[0, a] × [0, b]`.
* `StatMech.TwoDim.leftSide`, `rightSide`, `bottomSide`, `topSide`: its four sides.
* `StatMech.TwoDim.HorizontalCrossing`, `StatMech.TwoDim.VerticalCrossing` and the events
  `horizontalCrossingEvent`, `verticalCrossingEvent`.

## Main results

* `StatMech.TwoDim.horizontalCrossingEvent_increasing`,
  `StatMech.TwoDim.verticalCrossingEvent_increasing`: crossing events are increasing.

Rectangles with an arbitrary corner are in `MathlibExt.Probability.Percolation.RSW.Defs`
(`StatMech.RSW.Box.rect`); `StatMech.RSW.Box.horizontalCrossing_eq_twoDim` relates the two.
-/

@[expose] public section

open Set

namespace StatMech

namespace TwoDim

open StatMech.Lattice

variable {a b : ℤ}

/-- The rectangle `[0, a] × [0, b]` in `ℤ²`. -/
def rectangle (a b : ℤ) : Set (Site 2) :=
  {x | 0 ≤ x 0 ∧ x 0 ≤ a ∧ 0 ≤ x 1 ∧ x 1 ≤ b}

@[simp]
theorem mem_rectangle {x : Site 2} :
    x ∈ rectangle a b ↔ 0 ≤ x 0 ∧ x 0 ≤ a ∧ 0 ≤ x 1 ∧ x 1 ≤ b := Iff.rfl

theorem rectangle_finite (a b : ℤ) : (rectangle a b).Finite := by
  apply Set.Finite.subset
    (Set.Finite.pi (fun _ : Fin 2 => Set.finite_Icc (0 : ℤ) (max a b)))
  intro x hx i _
  fin_cases i
  · simpa only [Set.mem_Icc] using ⟨hx.1, le_trans hx.2.1 (le_max_left a b)⟩
  · simpa only [Set.mem_Icc] using ⟨hx.2.2.1, le_trans hx.2.2.2 (le_max_right a b)⟩

/-- The left side `{0} × [0, b]` of `rectangle a b`. -/
def leftSide (a b : ℤ) : Set (Site 2) := {x | x ∈ rectangle a b ∧ x 0 = 0}

/-- The right side `{a} × [0, b]` of `rectangle a b`. -/
def rightSide (a b : ℤ) : Set (Site 2) := {x | x ∈ rectangle a b ∧ x 0 = a}

/-- The bottom side `[0, a] × {0}` of `rectangle a b`. -/
def bottomSide (a b : ℤ) : Set (Site 2) := {x | x ∈ rectangle a b ∧ x 1 = 0}

/-- The top side `[0, a] × {b}` of `rectangle a b`. -/
def topSide (a b : ℤ) : Set (Site 2) := {x | x ∈ rectangle a b ∧ x 1 = b}

@[simp] theorem mem_leftSide {x : Site 2} :
    x ∈ leftSide a b ↔ x ∈ rectangle a b ∧ x 0 = 0 := Iff.rfl
@[simp] theorem mem_rightSide {x : Site 2} :
    x ∈ rightSide a b ↔ x ∈ rectangle a b ∧ x 0 = a := Iff.rfl
@[simp] theorem mem_bottomSide {x : Site 2} :
    x ∈ bottomSide a b ↔ x ∈ rectangle a b ∧ x 1 = 0 := Iff.rfl
@[simp] theorem mem_topSide {x : Site 2} :
    x ∈ topSide a b ↔ x ∈ rectangle a b ∧ x 1 = b := Iff.rfl

theorem leftSide_subset : leftSide a b ⊆ rectangle a b := fun _ hx => hx.1
theorem rightSide_subset : rightSide a b ⊆ rectangle a b := fun _ hx => hx.1
theorem bottomSide_subset : bottomSide a b ⊆ rectangle a b := fun _ hx => hx.1
theorem topSide_subset : topSide a b ⊆ rectangle a b := fun _ hx => hx.1

/-- `ω` has an open left–right crossing of `rectangle a b`: an open path inside the rectangle from
its left side to its right side. -/
def HorizontalCrossing (ω : ConfigSpace (Sym2 (Site 2))) (a b : ℤ) : Prop :=
  ∃ (x : leftSide a b) (y : rightSide a b),
    ConnectedWithin 2 ω (rectangle a b)
      ⟨(x : Site 2), leftSide_subset x.2⟩ ⟨(y : Site 2), rightSide_subset y.2⟩

/-- The event that `rectangle a b` has an open left–right crossing. -/
def horizontalCrossingEvent (a b : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | HorizontalCrossing ω a b}

@[simp]
theorem mem_horizontalCrossingEvent {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ horizontalCrossingEvent a b ↔ HorizontalCrossing ω a b := Iff.rfl

/-- `ω` has an open bottom–top crossing of `rectangle a b`: an open path inside the rectangle from
its bottom side to its top side. -/
def VerticalCrossing (ω : ConfigSpace (Sym2 (Site 2))) (a b : ℤ) : Prop :=
  ∃ (x : bottomSide a b) (y : topSide a b),
    ConnectedWithin 2 ω (rectangle a b)
      ⟨(x : Site 2), bottomSide_subset x.2⟩ ⟨(y : Site 2), topSide_subset y.2⟩

/-- The event that `rectangle a b` has an open bottom–top crossing. -/
def verticalCrossingEvent (a b : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | VerticalCrossing ω a b}

@[simp]
theorem mem_verticalCrossingEvent {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ verticalCrossingEvent a b ↔ VerticalCrossing ω a b := Iff.rfl

theorem HorizontalCrossing.connected {ω : ConfigSpace (Sym2 (Site 2))}
    (h : HorizontalCrossing ω a b) :
    ∃ (x y : Site 2), x ∈ leftSide a b ∧ y ∈ rightSide a b ∧ Connected 2 ω x y := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y, x.2, y.2, hxy.connected⟩

theorem VerticalCrossing.connected {ω : ConfigSpace (Sym2 (Site 2))}
    (h : VerticalCrossing ω a b) :
    ∃ (x y : Site 2), x ∈ bottomSide a b ∧ y ∈ topSide a b ∧ Connected 2 ω x y := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y, x.2, y.2, hxy.connected⟩

/-- The open subgraph is monotone in the configuration (`d = 2` case of
`StatMech.Universality.openSubgraph_mono_dim`). -/
theorem openSubgraph_mono {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω') :
    openSubgraph 2 ω ≤ openSubgraph 2 ω' := by
  intro x y hxy
  refine ⟨hxy.1, ?_⟩
  have hle := h s(x, y)
  rw [hxy.2] at hle
  exact top_le_iff.mp hle

theorem connectedWithin_mono {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω')
    {S : Set (Site 2)} {x y : S} (hxy : ConnectedWithin 2 ω S x y) :
    ConnectedWithin 2 ω' S x y := by
  refine hxy.mono ?_
  intro u v huv
  exact openSubgraph_mono h huv

theorem horizontalCrossingEvent_increasing {ω ω' : ConfigSpace (Sym2 (Site 2))}
    (h : ω ≤ ω') (hω : ω ∈ horizontalCrossingEvent a b) :
    ω' ∈ horizontalCrossingEvent a b := by
  obtain ⟨x, y, hxy⟩ := hω
  exact ⟨x, y, connectedWithin_mono h hxy⟩

theorem verticalCrossingEvent_increasing {ω ω' : ConfigSpace (Sym2 (Site 2))}
    (h : ω ≤ ω') (hω : ω ∈ verticalCrossingEvent a b) :
    ω' ∈ verticalCrossingEvent a b := by
  obtain ⟨x, y, hxy⟩ := hω
  exact ⟨x, y, connectedWithin_mono h hxy⟩

end TwoDim

end StatMech
