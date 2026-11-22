/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.IntervalCylinder
import MathlibExt.CategoryTheory.Limits.Types.BinaryCofan
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# The native whole marked interval boundary is monic

Forgetting marks and evaluating each original degree preserves the actual
binary coproduct. The two original endpoint images are injective and
disjoint, as witnessed by their distinct original interval coordinates.
Hence the same whole marked cylinder boundary is a monomorphism, without
assuming that marked carriers are adhesive or already form a model category.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite HomotopicalAlgebra MonoidalCategory
open scoped Simplicial

namespace SSet.Marked

/-- The original pointwise marked interval boundary has no identifications between its two endpoint copies. -/
theorem intervalCylinder_boundary_mono (X : Marked.{u}) : Mono (intervalCylinder.{u}.app X).i := by
  let d : X ⨿ X ⟶ prod X (max (Δ[1] : SSet.{u})) := (intervalCylinder.app X).i
  let _ : ∀ n : SimplexCategoryᵒᵖ, Mono (d.hom.app n) := fun n => by
    let G : Marked.{u} ⥤ Type u := forget ⋙ (CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type u)).obj n
    let _ : PreservesColimitsOfSize.{0, 0} forget.{u} := forgetPreservesColimits
    let c : BinaryCofan (X.toSSet.obj n) (X.toSSet.obj n) :=
      BinaryCofan.mk (G.map (coprod.inl : X ⟶ X ⨿ X)) (G.map (coprod.inr : X ⟶ X ⨿ X))
    let hc : IsColimit c := isColimitOfHasBinaryCoproductOfPreservesColimit G X X
    let g : c.pt ⟶ (X.toSSet ⊗ (Δ[1] : SSet.{u})).obj n := d.hom.app n
    have h₀ : c.inl ≫ g = (SSet.ι₀ (X := X.toSSet)).app n :=
      congrArg (fun (f : X ⟶ prod X (max (Δ[1] : SSet.{u}))) => f.hom.app n)
        (intervalCylinder.app X).inl_i
    have h₁ : c.inr ≫ g = (SSet.ι₁ (X := X.toSSet)).app n :=
      congrArg (fun (f : X ⟶ prod X (max (Δ[1] : SSet.{u}))) => f.hom.app n)
        (intervalCylinder.app X).inr_i
    apply Types.binaryCofan_mono_of_disjoint hc g
    · rw [h₀]
      intro x y h
      exact congrArg (fun (q : X.toSSet.obj n × (Δ[1] : SSet.{u}).obj n) => q.1) h
    · rw [h₁]
      intro x y h
      exact congrArg (fun (q : X.toSSet.obj n × (Δ[1] : SSet.{u}).obj n) => q.1) h
    · apply Set.disjoint_left.mpr
      rintro z ⟨x, hx⟩ ⟨y, hy⟩
      have h := hx.trans hy.symm
      rw [h₀, h₁] at h
      have h' := congrArg (fun (q : X.toSSet.obj n × (Δ[1] : SSet.{u}).obj n) =>
        SSet.stdSimplex.asOrderHom q.2 0) h
      change (0 : Fin 2) = 1 at h'
      exact (by decide : (0 : Fin 2) ≠ 1) h'
  let _ : Mono d.hom := NatTrans.mono_of_mono_app _
  exact Hom.mono_of_underlying d

end SSet.Marked
