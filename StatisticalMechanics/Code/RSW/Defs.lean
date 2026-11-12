/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































import Mathlib
import Code.Lattice.Clusters
import Code.Lattice.PlanarDual
import Code.TwoDim.Crossings

open Set

namespace StatMech

namespace RSW

namespace Box

open StatMech.Lattice
open StatMech.TwoDim










def rect (a b c d : ℤ) : Set (Site 2) :=
  {x | a ≤ x 0 ∧ x 0 ≤ b ∧ c ≤ x 1 ∧ x 1 ≤ d}

@[simp]
theorem mem_rect {a b c d : ℤ} {x : Site 2} :
    x ∈ rect a b c d ↔ a ≤ x 0 ∧ x 0 ≤ b ∧ c ≤ x 1 ∧ x 1 ≤ d := Iff.rfl



theorem rect_finite (a b c d : ℤ) : (rect a b c d).Finite := by
  apply Set.Finite.subset
    (Set.Finite.pi (fun i : Fin 2 => Set.finite_Icc (![a, c] i) (![b, d] i)))
  intro x hx i _
  fin_cases i
  · simpa only [Matrix.cons_val_zero, Set.mem_Icc] using ⟨hx.1, hx.2.1⟩
  · simpa only [Matrix.cons_val_one, Matrix.head_cons, Set.mem_Icc] using ⟨hx.2.2.1, hx.2.2.2⟩





def leftSide (a b c d : ℤ) : Set (Site 2) := {x | x ∈ rect a b c d ∧ x 0 = a}



def rightSide (a b c d : ℤ) : Set (Site 2) := {x | x ∈ rect a b c d ∧ x 0 = b}



def bottomSide (a b c d : ℤ) : Set (Site 2) := {x | x ∈ rect a b c d ∧ x 1 = c}



def topSide (a b c d : ℤ) : Set (Site 2) := {x | x ∈ rect a b c d ∧ x 1 = d}

@[simp] theorem mem_leftSide {a b c d : ℤ} {x : Site 2} :
    x ∈ leftSide a b c d ↔ x ∈ rect a b c d ∧ x 0 = a := Iff.rfl
@[simp] theorem mem_rightSide {a b c d : ℤ} {x : Site 2} :
    x ∈ rightSide a b c d ↔ x ∈ rect a b c d ∧ x 0 = b := Iff.rfl
@[simp] theorem mem_bottomSide {a b c d : ℤ} {x : Site 2} :
    x ∈ bottomSide a b c d ↔ x ∈ rect a b c d ∧ x 1 = c := Iff.rfl
@[simp] theorem mem_topSide {a b c d : ℤ} {x : Site 2} :
    x ∈ topSide a b c d ↔ x ∈ rect a b c d ∧ x 1 = d := Iff.rfl

theorem leftSide_subset {a b c d : ℤ} : leftSide a b c d ⊆ rect a b c d := fun _ hx => hx.1
theorem rightSide_subset {a b c d : ℤ} : rightSide a b c d ⊆ rect a b c d := fun _ hx => hx.1
theorem bottomSide_subset {a b c d : ℤ} : bottomSide a b c d ⊆ rect a b c d := fun _ hx => hx.1
theorem topSide_subset {a b c d : ℤ} : topSide a b c d ⊆ rect a b c d := fun _ hx => hx.1






def HorizontalCrossing (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) : Prop :=
  ∃ (x : leftSide a b c d) (y : rightSide a b c d),
    ConnectedWithin 2 ω (rect a b c d)
      ⟨(x : Site 2), leftSide_subset x.2⟩ ⟨(y : Site 2), rightSide_subset y.2⟩




def VerticalCrossing (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) : Prop :=
  ∃ (x : bottomSide a b c d) (y : topSide a b c d),
    ConnectedWithin 2 ω (rect a b c d)
      ⟨(x : Site 2), bottomSide_subset x.2⟩ ⟨(y : Site 2), topSide_subset y.2⟩



def horizontalCrossingEvent (a b c d : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | HorizontalCrossing ω a b c d}



def verticalCrossingEvent (a b c d : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | VerticalCrossing ω a b c d}

@[simp] theorem mem_horizontalCrossingEvent {a b c d : ℤ}
    {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ horizontalCrossingEvent a b c d ↔ HorizontalCrossing ω a b c d := Iff.rfl
@[simp] theorem mem_verticalCrossingEvent {a b c d : ℤ}
    {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ verticalCrossingEvent a b c d ↔ VerticalCrossing ω a b c d := Iff.rfl



theorem HorizontalCrossing.connected {a b c d : ℤ} {ω : ConfigSpace (Sym2 (Site 2))}
    (h : HorizontalCrossing ω a b c d) :
    ∃ x y : Site 2, x ∈ leftSide a b c d ∧ y ∈ rightSide a b c d ∧ Connected 2 ω x y := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y, x.2, y.2, hxy.connected⟩



theorem VerticalCrossing.connected {a b c d : ℤ} {ω : ConfigSpace (Sym2 (Site 2))}
    (h : VerticalCrossing ω a b c d) :
    ∃ x y : Site 2, x ∈ bottomSide a b c d ∧ y ∈ topSide a b c d ∧ Connected 2 ω x y := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y, x.2, y.2, hxy.connected⟩




theorem horizontalCrossingEvent_increasing {a b c d : ℤ}
    {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω')
    (hω : ω ∈ horizontalCrossingEvent a b c d) :
    ω' ∈ horizontalCrossingEvent a b c d := by
  obtain ⟨x, y, hxy⟩ := hω
  exact ⟨x, y, connectedWithin_mono h hxy⟩


theorem verticalCrossingEvent_increasing {a b c d : ℤ}
    {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω')
    (hω : ω ∈ verticalCrossingEvent a b c d) :
    ω' ∈ verticalCrossingEvent a b c d := by
  obtain ⟨x, y, hxy⟩ := hω
  exact ⟨x, y, connectedWithin_mono h hxy⟩



theorem horizontalCrossing_eq_twoDim (ω : ConfigSpace (Sym2 (Site 2))) (a b : ℤ) :
    HorizontalCrossing ω 0 a 0 b ↔ TwoDim.HorizontalCrossing ω a b := by
  have hrect : rect 0 a 0 b = TwoDim.rectangle a b := rfl
  rfl
















def DualHorizontalCrossing (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) : Prop :=
  HorizontalCrossing (dualConfig ω) a b c d





def DualVerticalCrossing (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) : Prop :=
  VerticalCrossing (dualConfig ω) a b c d


def dualHorizontalCrossingEvent (a b c d : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | DualHorizontalCrossing ω a b c d}


def dualVerticalCrossingEvent (a b c d : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | DualVerticalCrossing ω a b c d}

@[simp] theorem mem_dualHorizontalCrossingEvent {a b c d : ℤ}
    {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ dualHorizontalCrossingEvent a b c d ↔ DualHorizontalCrossing ω a b c d := Iff.rfl
@[simp] theorem mem_dualVerticalCrossingEvent {a b c d : ℤ}
    {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ dualVerticalCrossingEvent a b c d ↔ DualVerticalCrossing ω a b c d := Iff.rfl



theorem dualHorizontalCrossing_iff (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) :
    DualHorizontalCrossing ω a b c d ↔ HorizontalCrossing (dualConfig ω) a b c d := Iff.rfl



theorem dualVerticalCrossing_iff (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) :
    DualVerticalCrossing ω a b c d ↔ VerticalCrossing (dualConfig ω) a b c d := Iff.rfl





theorem dualHorizontalCrossingEvent_increasing {a b c d : ℤ}
    {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : dualConfig ω ≤ dualConfig ω')
    (hω : ω ∈ dualHorizontalCrossingEvent a b c d) :
    ω' ∈ dualHorizontalCrossingEvent a b c d :=
  horizontalCrossingEvent_increasing h hω


theorem dualVerticalCrossingEvent_increasing {a b c d : ℤ}
    {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : dualConfig ω ≤ dualConfig ω')
    (hω : ω ∈ dualVerticalCrossingEvent a b c d) :
    ω' ∈ dualVerticalCrossingEvent a b c d :=
  verticalCrossingEvent_increasing h hω










def annulus (z : Site 2) (n : ℕ) : Set (Site 2) :=
  (fun x => z + x) '' (box 2 (2 * n) \ box 2 n)

@[simp]
theorem mem_annulus {z x : Site 2} {n : ℕ} :
    x ∈ annulus z n ↔ ∃ y, (y ∈ box 2 (2 * n) ∧ y ∉ box 2 n) ∧ z + y = x := by
  simp only [annulus, Set.mem_image, Set.mem_diff, mem_box]


theorem annulus_finite (z : Site 2) (n : ℕ) : (annulus z n).Finite :=
  ((box_finite 2 (2 * n)).diff).image _



theorem annulus_subset_outer (z : Site 2) (n : ℕ) :
    annulus z n ⊆ (fun x => z + x) '' box 2 (2 * n) :=
  Set.image_mono Set.diff_subset











def IsAnnulusCircuit (ω : ConfigSpace (Sym2 (Site 2))) (z : Site 2) (n : ℕ)
    {v : Site 2} (w : (openSubgraph 2 ω).Walk v v) : Prop :=
  IsOpenCircuit 2 ω w ∧ ∀ u ∈ w.support, u ∈ annulus z n





def AnnulusCircuit (ω : ConfigSpace (Sym2 (Site 2))) (z : Site 2) (n : ℕ) : Prop :=
  ∃ (v : Site 2) (w : (openSubgraph 2 ω).Walk v v), IsAnnulusCircuit ω z n w


def annulusCircuitEvent (z : Site 2) (n : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | AnnulusCircuit ω z n}

@[simp] theorem mem_annulusCircuitEvent {z : Site 2} {n : ℕ}
    {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ annulusCircuitEvent z n ↔ AnnulusCircuit ω z n := Iff.rfl


def AnnulusCircuit0 (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ) : Prop :=
  AnnulusCircuit ω (fun _ => 0) n



















noncomputable def boxCrossingEvent (α : ℝ) (n : ℕ) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  horizontalCrossingEvent 0 (⌊α * n⌋.toNat) 0 n






def P5 (μ : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c ≤ μ n (boxCrossingEvent α n)






def P5c {Ξ : Type*} (μ : Ξ → ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ (ξ : Ξ) (n : ℕ),
    c ≤ μ ξ n (boxCrossingEvent α n) ∧ μ ξ n (boxCrossingEvent α n) ≤ 1 - c




theorem P5c.p5 {Ξ : Type*} {μ : Ξ → ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
    (h : P5c μ) (ξ : Ξ) : P5 (μ ξ) := by
  intro α hα
  obtain ⟨c, hc, hbound⟩ := h α hα
  exact ⟨c, hc, fun n => (hbound ξ n).1⟩

end Box

end RSW

end StatMech
