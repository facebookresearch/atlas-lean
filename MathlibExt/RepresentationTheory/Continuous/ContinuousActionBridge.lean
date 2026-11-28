/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.RepresentationTheory.Continuous.TopRep
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Separation.Connected
public import Mathlib.Topology.Separation.Regular

/-!
# Continuity and fixed vectors of topological representations

Let k be a topological ring and G a topological monoid. For a topological representation X,
the continuous-action condition on its associated action is continuity of (g,x) ↦ ρ(g)x. When
G is a group, forgetting coefficient topology gives the algebraic representation with the same
linear action.

For discrete coefficients and a continuous action, each vector has an open stabilizer. If G is
also compact and totally disconnected, any open normal subgroup can be refined to an open
normal subgroup fixing a prescribed finite set of vectors.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

universe u v w

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]

section LiteralAction

variable {G : Type v} [Monoid G] [TopologicalSpace G]

/-- Joint continuity of the representation action.

For a topological monoid G and a topological representation X over k, the continuous-action
property of the associated action implies continuity of G × X → X, (g,x) ↦ ρ(g)x. -/
theorem continuous_action
    {X : TopRep.{w} k G}
    (hX : ((TopRep.toActionTopModFunc (k := k) (G := G)).obj X).IsContinuous) :
    Continuous (fun p : G × X ↦ X.ρ p.1 p.2) := by
  let A := (TopRep.toActionTopModFunc (k := k) (G := G)).obj X
  let e : ((forget₂ _ TopCat).obj A) ≃ₜ X :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_id
      continuous_invFun := continuous_id }
  have hA : Continuous (fun p : G × (forget₂ _ TopCat).obj A ↦
      (forget₂ (TopModuleCat k) TopCat).map (A.ρ p.1).asHom p.2) :=
    (Action.isContinuous_def A).mp hX
  have h := e.continuous.comp
    (hA.comp (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))
  change Continuous (fun p : G × X ↦ X.ρ p.1 p.2) at h
  exact h

end LiteralAction

variable {G : Type v} [Group G] [TopologicalSpace G]

/-- The algebraic representation underlying a topological representation.

For a topological group G and topological ring k, this functor sends X to its k-linear
representation and sends each continuous intertwiner to the same linear intertwiner. The
coefficient carrier and group action are retained. -/
def forgetToRep : TopRep.{w} k G ⥤ Rep.{w} k G where
  obj X := Rep.of X.ρ.toRepresentation
  map f := Rep.ofHom f.hom.toIntertwiningMap
  map_id _ := by
    apply Rep.hom_ext
    rfl
  map_comp _ _ := by
    apply Rep.hom_ext
    rfl

/-- Additivity of forgetting coefficient topology.

The functor from topological representations to algebraic representations preserves sums of
morphisms, since it sends continuous intertwiners to their underlying linear maps. -/
instance forgetToRep_additive :
    (forgetToRep (k := k) (G := G)).Additive where
  map_add {X Y} {f g} := by
    apply Rep.hom_ext
    rfl

/-- Open stabilizers of discrete coefficient vectors.

If X has discrete topology and its associated G-action is continuous, then for each x ∈ X the
subset of g with ρ(g)x = x is open in G. -/
theorem isOpen_fixedBy_of_action_isContinuous
    {X : TopRep.{w} k G} [DiscreteTopology X]
    (hX : ((TopRep.toActionTopModFunc (k := k) (G := G)).obj X).IsContinuous)
    (x : X) : IsOpen {g : G | X.ρ g x = x} := by
  let A := (TopRep.toActionTopModFunc (k := k) (G := G)).obj X
  let xA : (forget₂ _ TopCat).obj A := x
  let _ : DiscreteTopology ((forget₂ _ TopCat).obj A) :=
    (inferInstance : DiscreteTopology X)
  let _ : ContinuousSMul G ((forget₂ _ TopCat).obj A) := hX
  have hopen : IsOpen (MulAction.stabilizer G xA : Set G) :=
    stabilizer_isOpen G xA
  change IsOpen {g : G |
    ((forget₂ (TopModuleCat k) TopCat).map (A.ρ g).asHom) xA = xA} at hopen
  change IsOpen {g : G | X.ρ g x = x}
  exact hopen

/-- An open normal subgroup fixing finitely many vectors.

Let G be a compact totally disconnected topological group acting continuously on a discrete
coefficient representation X. For every open normal subgroup U and finite set s ⊆ X, there is
an open normal subgroup V ≤ U such that ρ(v)x = x for all v ∈ V and x ∈ s. -/
theorem exists_openNormal_le_fix_finset_of_action_isContinuous
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {X : TopRep.{w} k G} [DiscreteTopology X]
    (hX : ((TopRep.toActionTopModFunc (k := k) (G := G)).obj X).IsContinuous)
    (U : OpenNormalSubgroup G) (s : Finset X) :
    ∃ V : OpenNormalSubgroup G, V ≤ U ∧
      ∀ (v : V) (x : X), x ∈ s → X.ρ (v : G) x = x := by
  let W : Set G := ⋂ x ∈ s, {g : G | X.ρ g x = x}
  have hWopen : IsOpen W := by
    exact isOpen_biInter_finset fun x _ ↦
      isOpen_fixedBy_of_action_isContinuous hX x
  have hWone : (1 : G) ∈ W := by
    simp [W]
  obtain ⟨N, hN⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWopen hWone
  refine ⟨N ⊓ U, inf_le_right, ?_⟩
  intro v x hx
  have hvN : (v : G) ∈ N := (inf_le_left : N ⊓ U ≤ N) v.property
  have hvW : (v : G) ∈ W := hN hvN
  exact Set.mem_iInter.mp (Set.mem_iInter.mp hvW x) hx

end TopRep
