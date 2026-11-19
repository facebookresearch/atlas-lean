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

@[expose] public section

namespace Cslib.Planning.MotionPlanning

def cObs (C W : Type*) (A : C → Set W) (O : Set W) : Set C :=
  {q | (A q ∩ O).Nonempty}

def cFree (C W : Type*) (A : C → Set W) (O : Set W) : Set C :=
  (cObs C W A O)ᶜ

theorem mem_cObs (C W : Type*) (A : C → Set W) (O : Set W) (q : C) :
    q ∈ cObs C W A O ↔ (A q ∩ O).Nonempty :=
  Iff.rfl

theorem mem_cFree (C W : Type*) (A : C → Set W) (O : Set W) (q : C) :
    q ∈ cFree C W A O ↔ A q ∩ O = ∅ := by
  change q ∈ (cObs C W A O)ᶜ ↔ _
  rw [Set.mem_compl_iff, mem_cObs, Set.not_nonempty_iff_eq_empty]

theorem cObs_mono (C W : Type*) (A : C → Set W) (O O' : Set W) (h : O ⊆ O') :
    cObs C W A O ⊆ cObs C W A O' := by
  intro q hq
  rw [mem_cObs] at hq ⊢
  obtain ⟨y, hyA, hyO⟩ := hq
  exact ⟨y, hyA, h hyO⟩

theorem cFree_anti (C W : Type*) (A : C → Set W) (O O' : Set W) (h : O ⊆ O') :
    cFree C W A O' ⊆ cFree C W A O := by
  change (cObs C W A O')ᶜ ⊆ (cObs C W A O)ᶜ
  exact Set.compl_subset_compl.mpr (cObs_mono C W A O O' h)

theorem cObs_empty (C W : Type*) (A : C → Set W) : cObs C W A ∅ = ∅ := by
  ext q
  simp [mem_cObs]

theorem cFree_empty (C W : Type*) (A : C → Set W) : cFree C W A ∅ = Set.univ := by
  change (cObs C W A ∅)ᶜ = _
  rw [cObs_empty, Set.compl_empty]

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

structure PathProblem (C : Type*) [TopologicalSpace C] where
  free : Set C
  qI : C
  qG : C
  qI_mem : qI ∈ free
  qG_mem : qG ∈ free

def PathProblem.IsSolution (C : Type*) [TopologicalSpace C] (P : PathProblem C)
    (γ : Path P.qI P.qG) : Prop :=
  ∀ t, γ t ∈ P.free

def PathProblem.Solvable (C : Type*) [TopologicalSpace C] (P : PathProblem C) : Prop :=
  ∃ γ : Path P.qI P.qG, PathProblem.IsSolution C P γ

theorem PathProblem.solvable_iff_joinedIn (C : Type*) [TopologicalSpace C]
    (P : PathProblem C) : P.Solvable ↔ JoinedIn P.free P.qI P.qG :=
  Iff.rfl

local instance : PathConnectedSpace Real.Angle := by
  refine Function.Surjective.pathConnectedSpace (f := ((↑) : ℝ → Real.Angle)) ?_
    Real.Angle.continuous_coe
  intro θ
  exact Real.Angle.induction_on θ (fun x => ⟨x, rfl⟩)

noncomputable def planarPlacement (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)]
    (o : Orientation ℝ V (Fin 2)) (A₀ : Set V) : V × Real.Angle → Set V :=
  fun (t, θ) => (fun x => o.rotation θ x + t) '' A₀

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

theorem pathConnectedSpace_planar (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)] :
    PathConnectedSpace (V × Real.Angle) :=
  @Prod.instPathConnectedSpace V Real.Angle inferInstance inferInstance
    IsTopologicalAddGroup.pathConnectedSpace inferInstance

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

abbrev plane : Type := EuclideanSpace ℝ (Fin 2)

noncomputable def planeOrientation : Orientation ℝ plane (Fin 2) :=
  Module.Basis.orientation (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis

end Cslib.Planning.MotionPlanning
