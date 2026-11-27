/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Path
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Orientation
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Data.Set.Basic
import Mathlib.Order.BooleanAlgebra.Set

/-!
# Configuration spaces for motion planning

This module covers configuration spaces: the obstacle region (`cObs`), free space
(`cFree`), path problems (`PathProblem`), and the planar rigid body with
configuration space `V × Real.Angle`.

Touching an obstacle counts as a collision (the placed body meets the obstacle set).
A planar placement rotates the body by `θ` and then translates it by `t`.
A path problem asks for a continuous path from the start to the goal inside the free
set, and solvability is equivalent to `JoinedIn`.
The helper instances (`PathConnectedSpace Real.Angle` and the dimension fact for
`EuclideanSpace ℝ (Fin 2)`) are local to this file.

## References
* S. M. LaValle, *Planning Algorithms*, Cambridge University Press, 2006,
  Chapter 4 (Sections 4.2.1 and 4.3.1, Formulation 4.1).
-/
@[expose] public section

namespace Cslib.Planning.MotionPlanning

/-- The obstacle region: configurations where the placed body meets the obstacle set. -/
def cObs (C W : Type*) (A : C → Set W) (O : Set W) : Set C :=
  {q | (A q ∩ O).Nonempty}

/-- The free space: the complement of the obstacle region. -/
def cFree (C W : Type*) (A : C → Set W) (O : Set W) : Set C :=
  (cObs C W A O)ᶜ

/-- Membership in the obstacle region unfolds to the placed body meeting the obstacles. -/
theorem mem_cObs (C W : Type*) (A : C → Set W) (O : Set W) (q : C) :
    q ∈ cObs C W A O ↔ (A q ∩ O).Nonempty :=
  Iff.rfl

/-- Membership in free space unfolds to the placed body being disjoint from the obstacles. -/
theorem mem_cFree (C W : Type*) (A : C → Set W) (O : Set W) (q : C) :
    q ∈ cFree C W A O ↔ A q ∩ O = ∅ := by
  change q ∈ (cObs C W A O)ᶜ ↔ _
  rw [Set.mem_compl_iff, mem_cObs, Set.not_nonempty_iff_eq_empty]

/-- The obstacle region grows monotonically with the obstacle set. -/
theorem cObs_mono (C W : Type*) (A : C → Set W) (O O' : Set W) (h : O ⊆ O') :
    cObs C W A O ⊆ cObs C W A O' := by
  intro q hq
  rw [mem_cObs] at hq ⊢
  obtain ⟨y, hyA, hyO⟩ := hq
  exact ⟨y, hyA, h hyO⟩

/-- Free space shrinks monotonically as the obstacle set grows. -/
theorem cFree_anti (C W : Type*) (A : C → Set W) (O O' : Set W) (h : O ⊆ O') :
    cFree C W A O' ⊆ cFree C W A O := by
  change (cObs C W A O')ᶜ ⊆ (cObs C W A O)ᶜ
  exact Set.compl_subset_compl.mpr (cObs_mono C W A O O' h)

/-- With no obstacles, the obstacle region is empty. -/
theorem cObs_empty (C W : Type*) (A : C → Set W) : cObs C W A ∅ = ∅ := by
  ext q
  simp [mem_cObs]

/-- With no obstacles, free space is everything. -/
theorem cFree_empty (C W : Type*) (A : C → Set W) : cFree C W A ∅ = Set.univ := by
  change (cObs C W A ∅)ᶜ = _
  rw [cObs_empty, Set.compl_empty]

/-- The obstacle region of a union is the union of the obstacle regions. -/
theorem cObs_union (C W : Type*) (A : C → Set W) (O O' : Set W) :
    cObs C W A (O ∪ O') = cObs C W A O ∪ cObs C W A O' := by
  ext q
  simp only [mem_cObs, Set.mem_union]
  constructor
  · rintro ⟨y, hyA, hyO⟩
    rcases hyO with h | h
    · exact Or.inl ⟨y, hyA, h⟩
    · exact Or.inr ⟨y, hyA, h⟩
  · rintro (⟨y, hyA, hyO⟩ | ⟨y, hyA, hyO⟩)
    · exact ⟨y, hyA, Or.inl hyO⟩
    · exact ⟨y, hyA, Or.inr hyO⟩

/-- A path problem: free set, start and goal configurations lying in it. -/
structure PathProblem (C : Type*) [TopologicalSpace C] where
  free : Set C
  qI : C
  qG : C
  qI_mem : qI ∈ free
  qG_mem : qG ∈ free

/-- A path solves a problem when it stays inside the free set. -/
def PathProblem.IsSolution (C : Type*) [TopologicalSpace C] (P : PathProblem C)
    (γ : Path P.qI P.qG) : Prop :=
  ∀ t, γ t ∈ P.free

/-- A problem is solvable when some path from start to goal solves it. -/
def PathProblem.Solvable (C : Type*) [TopologicalSpace C] (P : PathProblem C) : Prop :=
  ∃ γ : Path P.qI P.qG, PathProblem.IsSolution C P γ

/-- Solvability is equivalent to start and goal being joined in the free set. -/
theorem PathProblem.solvable_iff_joinedIn (C : Type*) [TopologicalSpace C]
    (P : PathProblem C) : P.Solvable ↔ JoinedIn P.free P.qI P.qG :=
  Iff.rfl

local instance : PathConnectedSpace Real.Angle := by
  refine Function.Surjective.pathConnectedSpace (f := ((↑) : ℝ → Real.Angle)) ?_
    Real.Angle.continuous_coe
  intro θ
  exact Real.Angle.induction_on θ (fun x => ⟨x, rfl⟩)

/-- Planar placement: rotate the body by `θ`, then translate it by `t`. -/
noncomputable def planarPlacement (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)]
    (o : Orientation ℝ V (Fin 2)) (A₀ : Set V) : V × Real.Angle → Set V :=
  fun (t, θ) => (fun x => o.rotation θ x + t) '' A₀

/-- A planar configuration collides iff some body point lands in the obstacle set. -/
theorem mem_cObs_planarPlacement (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)]
    (o : Orientation ℝ V (Fin 2)) (A₀ : Set V) (O : Set V) (t : V) (θ : Real.Angle) :
    (t, θ) ∈ cObs (V × Real.Angle) V (planarPlacement V o A₀) O ↔
      ∃ a ∈ A₀, o.rotation θ a + t ∈ O := by
  rw [mem_cObs]
  change ((fun x => o.rotation θ x + t) '' A₀ ∩ O).Nonempty ↔ _
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, hy⟩
    exact ⟨a, ha, hy⟩
  · rintro ⟨a, ha, hy⟩
    exact ⟨_, ⟨a, ha, rfl⟩, hy⟩

/-- The planar configuration space `V × Real.Angle` is path-connected. -/
theorem pathConnectedSpace_planar (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)] :
    PathConnectedSpace (V × Real.Angle) :=
  @Prod.instPathConnectedSpace V Real.Angle inferInstance inferInstance
    IsTopologicalAddGroup.pathConnectedSpace inferInstance

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The standard plane, `EuclideanSpace ℝ (Fin 2)`. -/
abbrev plane : Type := EuclideanSpace ℝ (Fin 2)

/-- The standard orientation of the plane. -/
noncomputable def planeOrientation : Orientation ℝ plane (Fin 2) :=
  Module.Basis.orientation (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis

end Cslib.Planning.MotionPlanning
