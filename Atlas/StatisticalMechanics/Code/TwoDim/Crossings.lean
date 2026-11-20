/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























import Mathlib
import Code.Lattice.Clusters
import Code.Lattice.PlanarDual

open Set

namespace StatMech

namespace TwoDim

open StatMech.Lattice

variable {a b : ℤ}





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




def leftSide (a b : ℤ) : Set (Site 2) := {x | x ∈ rectangle a b ∧ x 0 = 0}


def rightSide (a b : ℤ) : Set (Site 2) := {x | x ∈ rectangle a b ∧ x 0 = a}


def bottomSide (a b : ℤ) : Set (Site 2) := {x | x ∈ rectangle a b ∧ x 1 = 0}


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










def HorizontalCrossing (ω : ConfigSpace (Sym2 (Site 2))) (a b : ℤ) : Prop :=
  ∃ (x : leftSide a b) (y : rightSide a b),
    ConnectedWithin 2 ω (rectangle a b)
      ⟨(x : Site 2), leftSide_subset x.2⟩ ⟨(y : Site 2), rightSide_subset y.2⟩




def horizontalCrossingEvent (a b : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | HorizontalCrossing ω a b}

@[simp]
theorem mem_horizontalCrossingEvent {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ horizontalCrossingEvent a b ↔ HorizontalCrossing ω a b := Iff.rfl










def VerticalCrossing (ω : ConfigSpace (Sym2 (Site 2))) (a b : ℤ) : Prop :=
  ∃ (x : bottomSide a b) (y : topSide a b),
    ConnectedWithin 2 ω (rectangle a b)
      ⟨(x : Site 2), bottomSide_subset x.2⟩ ⟨(y : Site 2), topSide_subset y.2⟩



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
