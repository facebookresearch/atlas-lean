/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-LAYER MULTIPLE MODULE ROUTING: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 381-395,
doi:10.1016/0196-6774(82)90032-3, problem [7] TWO-LAYER MULTIPLE MODULE ROUTING (reference:
T. G. Szymanski, "Dogleg channel routing is NP-complete", manuscript (1982); transformation from
3SAT) and the reserved-layer model of Section 2.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TwoLayerChannelRoutingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoLayerMultipleModuleRouting

open TwoLayerChannelRouting (toInt IsLeaf RunsVertically RunsHorizontally)

/-- An instance: the modules, each given by the coordinates `x₁, y₁, x₂, y₂` of its lower-left
and upper-right corners; the terminals, each given by its coordinates and its net label; the
number `m` of nets; and the area bound `B`. -/
abbrev TwoLayerMultipleModuleRoutingInstance :=
  List ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × List (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ × ℕ

/-- An axis-parallel rectangle as its corner coordinates `(x₁, y₁, x₂, y₂)`. -/
abbrev Rect := ℤ × ℤ × ℤ × ℤ

/-- The rectangle of an encoded module. -/
def moduleRect (M : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : Rect :=
  (toInt M.1, toInt M.2.1, toInt M.2.2.1, toInt M.2.2.2)

/-- The point `v` lies in the closed region of the rectangle `r`. -/
def InRect (r : Rect) (v : StatMech.Lattice.Site 2) : Prop :=
  r.1 ≤ v 0 ∧ v 0 ≤ r.2.2.1 ∧ r.2.1 ≤ v 1 ∧ v 1 ≤ r.2.2.2

/-- The point `v` lies on the perimeter of the rectangle `r`. -/
def OnPerimeter (r : Rect) (v : StatMech.Lattice.Site 2) : Prop :=
  InRect r v ∧ (v 0 = r.1 ∨ v 0 = r.2.2.1 ∨ v 1 = r.2.1 ∨ v 1 = r.2.2.2)

/-- The closed regions of the rectangles `r` and `s` are disjoint. -/
def RectsDisjoint (r s : Rect) : Prop :=
  r.2.2.1 < s.1 ∨ s.2.2.1 < r.1 ∨ r.2.2.2 < s.2.1 ∨ s.2.2.2 < r.2.1

/-- The rectangle `s` is included in the rectangle `r`. -/
def RectIncluded (s r : Rect) : Prop :=
  r.1 ≤ s.1 ∧ s.2.2.1 ≤ r.2.2.1 ∧ r.2.1 ≤ s.2.1 ∧ s.2.2.2 ≤ r.2.2.2

/-- The labeled grid points of `P`: `((x, y), k)` for a terminal at `(x, y)` in net `k`. -/
def terminals (i : TwoLayerMultipleModuleRoutingInstance) :
    List (StatMech.Lattice.Site 2 × ℕ) :=
  i.2.1.map fun t => (![toInt t.1.1, toInt t.1.2], t.2)

/-- Well-formedness of an instance: every module is a rectangle with `x₁ < x₂` and `y₁ < y₂`,
two different modules do not intersect, the terminals are distinct points, every terminal lies on
the perimeter of a module, every net label is below `m`, and every net is non-empty. -/
def WellFormed (i : TwoLayerMultipleModuleRoutingInstance) : Prop :=
  (∀ M ∈ i.1, (moduleRect M).1 < (moduleRect M).2.2.1 ∧
    (moduleRect M).2.1 < (moduleRect M).2.2.2) ∧
    (∀ a b : Fin i.1.length, a ≠ b →
      RectsDisjoint (moduleRect (i.1.get a)) (moduleRect (i.1.get b))) ∧
    ((terminals i).map Prod.fst).Nodup ∧
    (∀ e ∈ terminals i, ∃ M ∈ i.1, OnPerimeter (moduleRect M) e.1) ∧
    (∀ e ∈ terminals i, e.2 < i.2.2.1) ∧ ∀ k < i.2.2.1, ∃ e ∈ terminals i, e.2 = k

/-- Some trees `T₀, ..., Tₘ₋₁` and some rectangle `R` of area at most `B` route the nets: `R`
includes every module and every segment, no segment is contained in a module, each `Tₖ` is a
finite tree in the grid whose leaves are exactly the points of net `k`, and two different trees
meet only in orthogonal intersections. -/
def TwoLayerMultipleModuleRoutingFeasible (i : TwoLayerMultipleModuleRoutingInstance) : Prop :=
  ∃ T : Fin i.2.2.1 → (StatMech.Lattice.hypercubicLattice 2).Subgraph, ∃ R : Rect,
    R.1 ≤ R.2.2.1 ∧ R.2.1 ≤ R.2.2.2 ∧ (R.2.2.1 - R.1) * (R.2.2.2 - R.2.1) ≤ (i.2.2.2 : ℤ) ∧
    (∀ M ∈ i.1, RectIncluded (moduleRect M) R) ∧
    (∀ k u v, (T k).Adj u v → InRect R u ∧ InRect R v ∧
      ∀ M ∈ i.1, ¬ (InRect (moduleRect M) u ∧ InRect (moduleRect M) v)) ∧
    (∀ k, (T k).verts.Finite ∧ (T k).coe.IsTree ∧
      ∀ v, IsLeaf (T k) v ↔ (v, (k : ℕ)) ∈ terminals i) ∧
    ∀ k l, k ≠ l → ∀ v ∈ (T k).verts, v ∈ (T l).verts →
      (RunsVertically (T k) v ∧ RunsHorizontally (T l) v) ∨
        (RunsHorizontally (T k) v ∧ RunsVertically (T l) v)

open Classical in
/-- TWO-LAYER MULTIPLE MODULE ROUTING as a decision problem over bitstrings. -/
noncomputable def twoLayerMultipleModuleRoutingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoLayerMultipleModuleRoutingInstance) x with
  | some i => decide (WellFormed i ∧ TwoLayerMultipleModuleRoutingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoLayerMultipleModuleRouting
