/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Euclidean.DiscreteGroups
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-!
# Tests for discrete subgroups of the Euclidean plane

The point group preserves the translation lattice (trivial and whole-group
cases), conjugation of a translation is translation by the transported
vector, and the classification of discrete additive subgroups of the plane
applies to the trivial subgroup, to cyclic subgroups, and to arbitrary
discrete subgroups.
-/

@[expose] public section

namespace MathlibExtTest.Geometry.Euclidean.DiscreteGroups

-- `_root_` disambiguates from this file's own `...Euclidean.DiscreteGroups` namespace.
open _root_.DiscreteGroups

/-- Conjugating a translation by the identity isometry does nothing. -/
example (v : E2) :
    (1 : M₂) * (AffineIsometryEquiv.constVAdd ℝ E2 v) * (1 : M₂)⁻¹ =
      AffineIsometryEquiv.constVAdd ℝ E2 v := by
  simp

/-- The point group of the trivial isometry group preserves its (trivial)
translation lattice, at the identity linear part and the zero vector. -/
example : (LinearIsometryEquiv.refl ℝ E2) (0 : E2) ∈
    translationLattice (⊥ : Subgroup M₂) :=
  point_group_preserves_lattice ⊥ (LinearIsometryEquiv.refl ℝ E2)
    ⟨1, Subgroup.mem_bot.mpr rfl, by rfl⟩ 0
    (by
      show (AffineIsometryEquiv.constVAdd ℝ E2 (0 : E2) : M₂) ∈ (⊥ : Subgroup M₂)
      rw [show (AffineIsometryEquiv.constVAdd ℝ E2 (0 : E2) : M₂) = 1 from by
        ext x; simp]
      exact Subgroup.mem_bot.mpr rfl)

/-- The point group of the whole isometry group preserves its (whole)
translation lattice, at an arbitrary linear part and vector. -/
example (A : E2 ≃ₗᵢ[ℝ] E2) (v : E2) :
    A v ∈ translationLattice (⊤ : Subgroup M₂) :=
  point_group_preserves_lattice ⊤ A
    ⟨A.toAffineIsometryEquiv, Subgroup.mem_top _,
      by simp [linearPart, LinearIsometryEquiv.toAffineIsometryEquiv_linearIsometryEquiv]⟩
    v (by
      show (AffineIsometryEquiv.constVAdd ℝ E2 v : M₂) ∈ (⊤ : Subgroup M₂)
      exact Subgroup.mem_top _)

/-- The classification applies to the trivial additive subgroup. -/
example :
    (⊥ : AddSubgroup E2) = ⊥ ∨
    (∃ α : E2, α ≠ 0 ∧ (⊥ : AddSubgroup E2) = AddSubgroup.zmultiples α) ∨
    (∃ a b : E2, LinearIndependent ℝ ![a, b] ∧
      (⊥ : AddSubgroup E2) = AddSubgroup.zmultiples a ⊔ AddSubgroup.zmultiples b) :=
  discrete_subgroup_R2_classification ⊥

/-- The classification applies to every cyclic additive subgroup. -/
example (α : E2) :
    AddSubgroup.zmultiples α = ⊥ ∨
    (∃ β : E2, β ≠ 0 ∧ AddSubgroup.zmultiples α = AddSubgroup.zmultiples β) ∨
    (∃ a b : E2, LinearIndependent ℝ ![a, b] ∧
      AddSubgroup.zmultiples α = AddSubgroup.zmultiples a ⊔ AddSubgroup.zmultiples b) :=
  discrete_subgroup_R2_classification (AddSubgroup.zmultiples α)

/-- The classification applies to every discrete additive subgroup. -/
example (G : AddSubgroup E2) [DiscreteTopology G] :
    G = ⊥ ∨
    (∃ α : E2, α ≠ 0 ∧ G = AddSubgroup.zmultiples α) ∨
    (∃ a b : E2, LinearIndependent ℝ ![a, b] ∧
      G = AddSubgroup.zmultiples a ⊔ AddSubgroup.zmultiples b) :=
  discrete_subgroup_R2_classification G

/-- A rank-two lattice satisfies the third alternative of the classification. -/
example (a b : E2) (h : LinearIndependent ℝ ![a, b])
    (G : AddSubgroup E2) (hG : G = AddSubgroup.zmultiples a ⊔ AddSubgroup.zmultiples b)
    [DiscreteTopology G] :
    G = ⊥ ∨
    (∃ α : E2, α ≠ 0 ∧ G = AddSubgroup.zmultiples α) ∨
    (∃ a' b' : E2, LinearIndependent ℝ ![a', b'] ∧
      G = AddSubgroup.zmultiples a' ⊔ AddSubgroup.zmultiples b') :=
  Or.inr (Or.inr ⟨a, b, h, hG⟩)

end MathlibExtTest.Geometry.Euclidean.DiscreteGroups
