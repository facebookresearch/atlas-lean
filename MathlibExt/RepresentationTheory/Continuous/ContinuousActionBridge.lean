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
# Algebraic and continuous-action bridges for topological representations

This file gives three small bridges from `TopRep` to existing Mathlib APIs.
`TopRep.forgetToRep` forgets coefficient topology while retaining the same
linear group action.  The standard `Action.IsContinuous` property on
`TopRep.toActionTopModFunc` gives continuity of the literal `TopRep` action
function.  For a discrete coefficient carrier, it also makes fixed sets open
and therefore lets one refine an open normal subgroup so that it fixes any
prescribed finite set.

No parallel continuity predicate or global action, topology, or continuity
instance is introduced.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

universe u v w

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]

section LiteralAction

variable {G : Type v} [Monoid G] [TopologicalSpace G]

/-- The standard continuous-action property gives continuity of the literal
`TopRep` action function. -/
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

/-- Forget the coefficient topology of a topological representation while
retaining its algebraic linear group action. -/
def forgetToRep : TopRep.{w} k G ⥤ Rep.{w} k G where
  obj X := Rep.of X.ρ.toRepresentation
  map f := Rep.ofHom f.hom.toIntertwiningMap
  map_id _ := by
    apply Rep.hom_ext
    rfl
  map_comp _ _ := by
    apply Rep.hom_ext
    rfl

instance forgetToRep_additive :
    (forgetToRep (k := k) (G := G)).Additive where
  map_add {X Y} {f g} := by
    apply Rep.hom_ext
    rfl

/-- Under the standard continuous-action property, the subgroup fixing one
vector of a discrete topological representation is open. -/
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

/-- In a profinite group, one can refine an open normal subgroup so that it
fixes every vector in a prescribed finite set. -/
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
