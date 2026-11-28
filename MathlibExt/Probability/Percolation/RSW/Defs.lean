/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarDual
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.WhitneyBridge
public import MathlibExt.Probability.Percolation.TwoDimensional.Crossings
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import MathlibExt.Combinatorics.SimpleGraph.Lattice.CrossingParity
import Mathlib.Tactic.FinCases

/-!
# Rectangles, crossings, annuli and the box-crossing property on `ℤ²`

Basic objects of Russo–Seymour–Welsh theory for bond percolation on `ℤ²`: rectangles
`[a, b] × [c, d]`, their open and dual crossings, open circuits in the annulus
`z + (Λ_{2n} \ Λ_n)`, and the box-crossing property (crossing probabilities of `αn × n` boxes
bounded away from `0`, or from `0` and `1`, uniformly in `n`). This file contains definitions and
elementary facts only; no RSW inequality is proved here.

## Main definitions

* `StatMech.RSW.Box.rect` and its sides `leftSide`, `rightSide`, `bottomSide`, `topSide`.
* `StatMech.RSW.Box.HorizontalCrossing`, `StatMech.RSW.Box.VerticalCrossing` and their events.
* `StatMech.RSW.Box.DualHorizontalCrossing`, `StatMech.RSW.Box.DualVerticalCrossing` and their
  events: left–right and bottom–top crossings on the shifted dual lattice.
* `StatMech.RSW.Box.annulus`, `StatMech.RSW.Box.AnnulusCircuit`: open circuits in an annulus.
* `StatMech.RSW.Box.boxCrossingEvent`: the left–right crossing of `[0, ⌊αn⌋] × [0, n]`.
* `StatMech.RSW.Box.P5`, `StatMech.RSW.Box.P5c`: the box-crossing property for one family of
  measures, and uniformly with two-sided bounds for an indexed family.

## Main results

* `StatMech.RSW.Box.horizontalCrossingEvent_increasing`,
  `StatMech.RSW.Box.verticalCrossingEvent_increasing`: primal crossing events are increasing.
* `StatMech.RSW.Box.dualHorizontalCrossing_iff`, `StatMech.RSW.Box.dualVerticalCrossing_iff`:
  dual crossings are paths that step across closed primal edges.
* `StatMech.RSW.Box.dualHorizontalCrossingEvent_antitone`,
  `StatMech.RSW.Box.dualVerticalCrossingEvent_antitone`: dual crossing events are antitone
  in primal openness.
* `StatMech.RSW.Box.horizontalCrossing_eq_twoDim`: agreement with
  `StatMech.TwoDim.HorizontalCrossing` for rectangles with a corner at the origin.

## References

* L. Russo, *A note on percolation*, Z. Wahrsch. Verw. Gebiete 43 (1978), 39–48.
* P. D. Seymour, D. J. A. Welsh, *Percolation probabilities on the square lattice*, Ann. Discrete
  Math. 3 (1978), 227–245.
* V. Tassion, *Crossing probabilities for Voronoi percolation*, Ann. Probab. 44 (2016), 3385–3398.
-/

@[expose] public section

open Set

namespace StatMech

namespace RSW

namespace Box

open StatMech.Lattice
open StatMech.TwoDim

/-- The rectangle `[a, b] × [c, d]` in `ℤ²`. -/
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

private lemma measurableSet_inducedAdj {d : ℕ} (S : Set (Site d)) (x y : S) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) |
      (openSubgraphInduce d ω S).Adj x y} := by
  by_cases hxy : (hypercubicLattice d).Adj (x : Site d) (y : Site d)
  · have heq : {ω : ConfigSpace (Sym2 (Site d)) |
        (openSubgraphInduce d ω S).Adj x y} = {ω | ω s((x : Site d), y) = true} := by
      ext ω
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, openSubgraphInduce_adj, openSubgraph_adj]
      exact and_iff_right hxy
    rw [heq]
    exact measurableSet_eq_fun (measurable_pi_apply s((x : Site d), y)) measurable_const
  · have heq : {ω : ConfigSpace (Sym2 (Site d)) |
        (openSubgraphInduce d ω S).Adj x y} = ∅ := by
      ext ω
      rw [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, openSubgraphInduce_adj,
        openSubgraph_adj]
      exact fun h => hxy h.1
    rw [heq]
    exact MeasurableSet.empty

private lemma measurableSet_isChainWithin {d : ℕ} (S : Set (Site d)) (l : List S) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) |
      List.IsChain (openSubgraphInduce d ω S).Adj l} := by
  induction l with
  | nil =>
      have heq : {ω : ConfigSpace (Sym2 (Site d)) |
          List.IsChain (openSubgraphInduce d ω S).Adj []} = Set.univ := by
        ext ω
        simp only [List.IsChain.nil, Set.mem_ofPred_eq, Set.mem_univ]
      rw [heq]
      exact MeasurableSet.univ
  | cons x l ih =>
      cases l with
      | nil =>
          have heq : {ω : ConfigSpace (Sym2 (Site d)) |
              List.IsChain (openSubgraphInduce d ω S).Adj [x]} = Set.univ := by
            ext ω
            simp only [List.IsChain.singleton, Set.mem_ofPred_eq, Set.mem_univ]
          rw [heq]
          exact MeasurableSet.univ
      | cons y l =>
          simpa only [List.isChain_cons_cons, Set.ofPred_and] using
            (measurableSet_inducedAdj S x y).inter ih

private lemma connectedWithin_iff_chain {d : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    (S : Set (Site d)) (x y : S) :
    ConnectedWithin d ω S x y ↔ ∃ l : List S,
      List.IsChain (openSubgraphInduce d ω S).Adj (x :: l) ∧
        (x :: l).getLast (List.cons_ne_nil _ _) = y := by
  unfold ConnectedWithin
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    obtain ⟨l, hchain, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen h
    exact ⟨l, hchain, hlast⟩
  · rintro ⟨l, hchain, hlast⟩
    exact List.relationReflTransGen_of_exists_isChain_cons l hchain hlast

/-- The event that two vertices are connected by an open path inside `S` is measurable. -/
theorem measurableSet_connectedWithin {d : ℕ} (S : Set (Site d)) (x y : S) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | ConnectedWithin d ω S x y} := by
  classical
  have heq : {ω : ConfigSpace (Sym2 (Site d)) | ConnectedWithin d ω S x y} =
      ⋃ l : List S, ({ω | List.IsChain (openSubgraphInduce d ω S).Adj (x :: l)} ∩
        if (x :: l).getLast (List.cons_ne_nil _ _) = y then Set.univ else ∅) := by
    ext ω
    rw [Set.mem_ofPred_eq, connectedWithin_iff_chain]
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨l, hchain, hlast⟩
      exact ⟨l, hchain, by rw [ite_eq_left hlast]; trivial⟩
    · rintro ⟨l, hchain, hlast⟩
      refine ⟨l, hchain, ?_⟩
      by_cases h : (x :: l).getLast (List.cons_ne_nil _ _) = y
      · exact h
      · rw [ite_eq_right h] at hlast
        exact absurd hlast (Set.notMem_empty _)
  rw [heq]
  apply MeasurableSet.iUnion
  intro l
  apply (measurableSet_isChainWithin S (x :: l)).inter
  by_cases h : (x :: l).getLast (List.cons_ne_nil _ _) = y
  · rw [ite_eq_left h]
    exact MeasurableSet.univ
  · rw [ite_eq_right h]
    exact MeasurableSet.empty

/-- The left side `{a} × [c, d]` of `rect a b c d`. -/
def leftSide (a b c d : ℤ) : Set (Site 2) := {x | x ∈ rect a b c d ∧ x 0 = a}

/-- The right side `{b} × [c, d]` of `rect a b c d`. -/
def rightSide (a b c d : ℤ) : Set (Site 2) := {x | x ∈ rect a b c d ∧ x 0 = b}

/-- The bottom side `[a, b] × {c}` of `rect a b c d`. -/
def bottomSide (a b c d : ℤ) : Set (Site 2) := {x | x ∈ rect a b c d ∧ x 1 = c}

/-- The top side `[a, b] × {d}` of `rect a b c d`. -/
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

/-- An open left–right crossing of `rect a b c d` by a path inside the rectangle. -/
def HorizontalCrossing (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) : Prop :=
  ∃ (x : leftSide a b c d) (y : rightSide a b c d),
    ConnectedWithin 2 ω (rect a b c d)
      ⟨(x : Site 2), leftSide_subset x.2⟩ ⟨(y : Site 2), rightSide_subset y.2⟩

/-- An open bottom–top crossing of `rect a b c d` by a path inside the rectangle. -/
def VerticalCrossing (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) : Prop :=
  ∃ (x : bottomSide a b c d) (y : topSide a b c d),
    ConnectedWithin 2 ω (rect a b c d)
      ⟨(x : Site 2), bottomSide_subset x.2⟩ ⟨(y : Site 2), topSide_subset y.2⟩

/-- The event that `rect a b c d` has an open left–right crossing. -/
def horizontalCrossingEvent (a b c d : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | HorizontalCrossing ω a b c d}

/-- The event that `rect a b c d` has an open bottom–top crossing. -/
def verticalCrossingEvent (a b c d : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | VerticalCrossing ω a b c d}

@[simp] theorem mem_horizontalCrossingEvent {a b c d : ℤ}
    {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ horizontalCrossingEvent a b c d ↔ HorizontalCrossing ω a b c d := Iff.rfl
@[simp] theorem mem_verticalCrossingEvent {a b c d : ℤ}
    {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ verticalCrossingEvent a b c d ↔ VerticalCrossing ω a b c d := Iff.rfl

/-- A left–right crossing event of a rectangle is measurable. -/
theorem measurableSet_horizontalCrossingEvent (a b c d : ℤ) :
    MeasurableSet (horizontalCrossingEvent a b c d) := by
  have heq : horizontalCrossingEvent a b c d =
      ⋃ x : leftSide a b c d, ⋃ y : rightSide a b c d,
        {ω | ConnectedWithin 2 ω (rect a b c d)
          ⟨(x : Site 2), leftSide_subset x.2⟩ ⟨(y : Site 2), rightSide_subset y.2⟩} := by
    ext ω
    simp only [horizontalCrossingEvent, HorizontalCrossing, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [heq]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun y =>
    measurableSet_connectedWithin _
      ⟨(x : Site 2), leftSide_subset x.2⟩ ⟨(y : Site 2), rightSide_subset y.2⟩

/-- A bottom–top crossing event of a rectangle is measurable. -/
theorem measurableSet_verticalCrossingEvent (a b c d : ℤ) :
    MeasurableSet (verticalCrossingEvent a b c d) := by
  have heq : verticalCrossingEvent a b c d =
      ⋃ x : bottomSide a b c d, ⋃ y : topSide a b c d,
        {ω | ConnectedWithin 2 ω (rect a b c d)
          ⟨(x : Site 2), bottomSide_subset x.2⟩ ⟨(y : Site 2), topSide_subset y.2⟩} := by
    ext ω
    simp only [verticalCrossingEvent, VerticalCrossing, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [heq]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun y =>
    measurableSet_connectedWithin _
      ⟨(x : Site 2), bottomSide_subset x.2⟩ ⟨(y : Site 2), topSide_subset y.2⟩

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
    HorizontalCrossing ω 0 a 0 b ↔ TwoDim.HorizontalCrossing ω a b :=
  Iff.rfl

private theorem faceRegion_openSubgraph_adj (ω : ConfigSpace (Sym2 (Site 2))) (f g : Site 2) :
    (whb_faceRegion (openSubgraph 2 ω)).Adj f g ↔
      dualLattice.Adj f g ∧ ω (sharedPrimalEdge f g) = false := by
  rw [whb_faceRegion_adj]
  change dualLattice.Adj f g ∧ _ ↔ _
  refine and_congr_right fun hfg => ?_
  obtain ⟨p, q, hpq, hadj⟩ := sharedPrimalEdge_isLatticeEdge hfg
  rw [hpq, SimpleGraph.mem_edgeSet, openSubgraph_adj, and_iff_right hadj]
  cases ω s(p, q) <;> simp

/-- An open left–right crossing of `(1/2, 1/2) + ([a, b] × [c, d])` on the dual lattice.
The integer labels are the lower left corners of the faces, and a step is open exactly when
its crossed primal edge (`sharedPrimalEdge`) is closed in `ω`. The path stays inside the shifted
rectangle; it may have length zero when the two sides coincide. -/
def DualHorizontalCrossing (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) : Prop :=
  ∃ (x : leftSide a b c d) (y : rightSide a b c d),
    ((whb_faceRegion (openSubgraph 2 ω)).induce (rect a b c d)).Reachable
      ⟨(x : Site 2), leftSide_subset x.2⟩ ⟨(y : Site 2), rightSide_subset y.2⟩

/-- **Dual bottom–top crossing.** There is an open path in the shifted dual rectangle
`(1/2, 1/2) + ([a, b] × [c, d])` from its bottom side to its top side. Integer vertex labels
are the lower left corners of the faces, and each step crosses a primal edge
(`sharedPrimalEdge`) closed in `ω`. The path may have length zero when the sides coincide
(Duminil-Copin, *Introduction to Bernoulli percolation*, 2018, §4.1 for duality). -/
def DualVerticalCrossing (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) : Prop :=
  ∃ (x : bottomSide a b c d) (y : topSide a b c d),
    ((whb_faceRegion (openSubgraph 2 ω)).induce (rect a b c d)).Reachable
      ⟨(x : Site 2), bottomSide_subset x.2⟩ ⟨(y : Site 2), topSide_subset y.2⟩

/-- The event `DualHorizontalCrossing`. -/
def dualHorizontalCrossingEvent (a b c d : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | DualHorizontalCrossing ω a b c d}

/-- **Dual bottom–top crossing event.** The set of primal configurations for which the shifted
rectangle has an open bottom–top crossing on the dual lattice. -/
def dualVerticalCrossingEvent (a b c d : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | DualVerticalCrossing ω a b c d}

@[simp] theorem mem_dualHorizontalCrossingEvent {a b c d : ℤ}
    {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ dualHorizontalCrossingEvent a b c d ↔ DualHorizontalCrossing ω a b c d := Iff.rfl
@[simp] theorem mem_dualVerticalCrossingEvent {a b c d : ℤ}
    {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ dualVerticalCrossingEvent a b c d ↔ DualVerticalCrossing ω a b c d := Iff.rfl

private theorem faceRegion_openSubgraph_induce_reachable_iff (ω : ConfigSpace (Sym2 (Site 2)))
    {S : Set (Site 2)} (x y : S) :
    ((whb_faceRegion (openSubgraph 2 ω)).induce S).Reachable x y ↔
      Relation.ReflTransGen (fun f g : S =>
        dualLattice.Adj f g ∧ ω (sharedPrimalEdge f g) = false) x y := by
  have hsteps : ((whb_faceRegion (openSubgraph 2 ω)).induce S).Adj =
      (fun f g : S => dualLattice.Adj f g ∧ ω (sharedPrimalEdge f g) = false) := by
    funext f g
    exact propext (faceRegion_openSubgraph_adj ω f g)
  rw [SimpleGraph.reachable_iff_reflTransGen, hsteps]

/-- **Dual left–right crossing steps.** A dual left–right crossing is a sequence of adjacent
faces in the rectangle, from the left side to the right side, with each crossed primal edge
closed. -/
theorem dualHorizontalCrossing_iff (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) :
    DualHorizontalCrossing ω a b c d ↔
      ∃ (x : leftSide a b c d) (y : rightSide a b c d),
        Relation.ReflTransGen (fun f g : rect a b c d =>
          dualLattice.Adj f g ∧ ω (sharedPrimalEdge f g) = false)
          ⟨(x : Site 2), leftSide_subset x.2⟩ ⟨(y : Site 2), rightSide_subset y.2⟩ := by
  simp only [DualHorizontalCrossing, faceRegion_openSubgraph_induce_reachable_iff]

/-- **Dual bottom–top crossing steps.** A dual bottom–top crossing is a sequence of adjacent
faces in the rectangle, from the bottom side to the top side, with each crossed primal edge
closed. -/
theorem dualVerticalCrossing_iff (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) :
    DualVerticalCrossing ω a b c d ↔
      ∃ (x : bottomSide a b c d) (y : topSide a b c d),
        Relation.ReflTransGen (fun f g : rect a b c d =>
          dualLattice.Adj f g ∧ ω (sharedPrimalEdge f g) = false)
          ⟨(x : Site 2), bottomSide_subset x.2⟩ ⟨(y : Site 2), topSide_subset y.2⟩ := by
  simp only [DualVerticalCrossing, faceRegion_openSubgraph_induce_reachable_iff]

private theorem faceRegion_openSubgraph_induce_le {ω ω' : ConfigSpace (Sym2 (Site 2))}
    (h : ω' ≤ ω) (S : Set (Site 2)) :
    (whb_faceRegion (openSubgraph 2 ω)).induce S ≤
      (whb_faceRegion (openSubgraph 2 ω')).induce S := by
  intro f g
  simp only [SimpleGraph.induce_adj, faceRegion_openSubgraph_adj]
  rintro ⟨hfg, hclosed⟩
  exact ⟨hfg, le_antisymm (by simpa only [hclosed] using h (sharedPrimalEdge f g))
    (Bool.false_le _)⟩

/-- **Antitonicity of dual left–right crossings.** Closing more primal edges preserves a dual
left–right crossing event. -/
theorem dualHorizontalCrossingEvent_antitone {a b c d : ℤ}
    {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω' ≤ ω)
    (hω : ω ∈ dualHorizontalCrossingEvent a b c d) :
    ω' ∈ dualHorizontalCrossingEvent a b c d := by
  obtain ⟨x, y, hxy⟩ := hω
  exact ⟨x, y, hxy.mono (faceRegion_openSubgraph_induce_le h _)⟩

/-- **Antitonicity of dual bottom–top crossings.** Closing more primal edges preserves a dual
bottom–top crossing event. -/
theorem dualVerticalCrossingEvent_antitone {a b c d : ℤ}
    {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω' ≤ ω)
    (hω : ω ∈ dualVerticalCrossingEvent a b c d) :
    ω' ∈ dualVerticalCrossingEvent a b c d := by
  obtain ⟨x, y, hxy⟩ := hω
  exact ⟨x, y, hxy.mono (faceRegion_openSubgraph_induce_le h _)⟩

private theorem le_of_dualConfig_le {ω ω' : ConfigSpace (Sym2 (Site 2))}
    (h : dualConfig ω ≤ dualConfig ω') : ω' ≤ ω := by
  intro e
  have he := h (crossEdge e)
  change (!(ω (crossEdge.symm (crossEdge e)))) ≤
    (!(ω' (crossEdge.symm (crossEdge e)))) at he
  rw [Equiv.symm_apply_apply] at he
  cases hωe : ω e <;> cases hω'e : ω' e <;> simp_all

/-- **Dual left–right crossings under rotated-complement order.** Increasing the rotated
complement `dualConfig ω` preserves a dual left–right crossing event. -/
theorem dualHorizontalCrossingEvent_increasing {a b c d : ℤ}
    {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : dualConfig ω ≤ dualConfig ω')
    (hω : ω ∈ dualHorizontalCrossingEvent a b c d) :
    ω' ∈ dualHorizontalCrossingEvent a b c d :=
  dualHorizontalCrossingEvent_antitone (le_of_dualConfig_le h) hω

/-- **Dual bottom–top crossings under rotated-complement order.** Increasing the rotated
complement `dualConfig ω` preserves a dual bottom–top crossing event. -/
theorem dualVerticalCrossingEvent_increasing {a b c d : ℤ}
    {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : dualConfig ω ≤ dualConfig ω')
    (hω : ω ∈ dualVerticalCrossingEvent a b c d) :
    ω' ∈ dualVerticalCrossingEvent a b c d :=
  dualVerticalCrossingEvent_antitone (le_of_dualConfig_le h) hω

/-- The annulus `z + (Λ_{2n} \ Λ_n)`, where `Λ_n = [-n, n]²`. -/
def annulus (z : Site 2) (n : ℕ) : Set (Site 2) :=
  (fun x => z + x) '' (box 2 (2 * n) \ box 2 n)

@[simp]
theorem mem_annulus {z x : Site 2} {n : ℕ} :
    x ∈ annulus z n ↔ ∃ y, (y ∈ box 2 (2 * n) ∧ y ∉ box 2 n) ∧ z + y = x := by
  simp only [annulus, Set.mem_image, Set.mem_sdiff, mem_box]

theorem annulus_finite (z : Site 2) (n : ℕ) : (annulus z n).Finite :=
  ((box_finite 2 (2 * n)).sdiff).image _

theorem annulus_subset_outer (z : Site 2) (n : ℕ) :
    annulus z n ⊆ (fun x => z + x) '' box 2 (2 * n) :=
  Set.image_mono Set.sdiff_subset

/-- The closed walk `w` is an open circuit all of whose vertices lie in `annulus z n`. -/
def IsAnnulusCircuit (ω : ConfigSpace (Sym2 (Site 2))) (z : Site 2) (n : ℕ)
    {v : Site 2} (w : (openSubgraph 2 ω).Walk v v) : Prop :=
  IsOpenCircuit 2 ω w ∧ ∀ u ∈ w.support, u ∈ annulus z n

/-- There is an open circuit inside `annulus z n`. -/
def AnnulusCircuit (ω : ConfigSpace (Sym2 (Site 2))) (z : Site 2) (n : ℕ) : Prop :=
  ∃ (v : Site 2) (w : (openSubgraph 2 ω).Walk v v), IsAnnulusCircuit ω z n w

/-- The event `AnnulusCircuit`. -/
def annulusCircuitEvent (z : Site 2) (n : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | AnnulusCircuit ω z n}

@[simp] theorem mem_annulusCircuitEvent {z : Site 2} {n : ℕ}
    {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ annulusCircuitEvent z n ↔ AnnulusCircuit ω z n := Iff.rfl

/-- There is an open circuit inside the annulus `Λ_{2n} \ Λ_n` centered at the origin. -/
def AnnulusCircuit0 (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ) : Prop :=
  AnnulusCircuit ω (fun _ => 0) n

/-- The left–right open crossing of the box `[0, ⌊αn⌋] × [0, n]` (aspect ratio `α`). -/
noncomputable def boxCrossingEvent (α : ℝ) (n : ℕ) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  horizontalCrossingEvent 0 (⌊α * n⌋.toNat) 0 n

/-- The box-crossing property for a sequence of set functions `μ n`: for every aspect ratio
`α > 0` there is `c > 0` with `μ n (boxCrossingEvent α n) ≥ c` for all `n`. -/
def P5 (μ : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c ≤ μ n (boxCrossingEvent α n)

/-- The uniform two-sided box-crossing property for a family `μ ξ n`: for every `α > 0` there is
`c > 0` with `c ≤ μ ξ n (boxCrossingEvent α n) ≤ 1 - c` for all `ξ` and `n`. -/
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
