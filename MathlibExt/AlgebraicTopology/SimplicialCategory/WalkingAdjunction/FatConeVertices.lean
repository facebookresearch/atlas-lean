/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatCone
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Original vertices of the actual fat cone

Evaluation preserves the native fat-cone pushout. Consequently every
vertex is represented by an original cylinder vertex or the original
apex. The two literal interval values identify the cylinder vertices
with the base or apex. No higher-simplex or strict-nerve identification
is inferred from this vertex statement.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.WalkingAdjunction.FatCone

/-- Every original fat-cone vertex comes from the actual cylinder or its actual apex. -/
theorem vertex_cylinder_or_apex (X : SSet.{u}) (x : (obj X) _⦋0⦌) :
    (∃ a : (X ⊗ (Δ[1] : SSet.{u})) _⦋0⦌, (cylinder X).app _ a = x) ∨
      ∃ z : (Δ[0] : SSet.{u}) _⦋0⦌, (apex X).app _ z = x := by
  let h : IsPushout (one X) (SSet.stdSimplex.isTerminalObj₀.from X) (cylinder X) (apex X) :=
    IsPushout.of_hasPushout _ _
  have he := h.map ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌))
  exact Types.eq_or_eq_of_isPushout he x

/-- Every fat-cone vertex is an original base vertex or the original apex vertex. -/
theorem vertex_base_or_apex (X : SSet.{u}) (x : (obj X) _⦋0⦌) :
    (∃ a : X _⦋0⦌, (base X).app _ a = x) ∨
      ∃ z : (Δ[0] : SSet.{u}) _⦋0⦌, (apex X).app _ z = x := by
  obtain ⟨a, ha⟩ | ⟨z, hz⟩ := vertex_cylinder_or_apex X x
  · generalize ht : SSet.stdSimplex.obj₀Equiv a.2 = t
    fin_cases t
    · left
      refine ⟨a.1, ?_⟩
      have he : a = (SSet.ι₀ : X ⟶ X ⊗ (Δ[1] : SSet.{u})).app _ a.1 := by
        apply Prod.ext
        · rfl
        · apply SSet.stdSimplex.obj₀Equiv.injective
          exact ht
      exact (congrArg (fun b => (cylinder X).app _ b) he).symm.trans ha
    · right
      refine ⟨(SSet.stdSimplex.isTerminalObj₀.from X).app _ a.1, ?_⟩
      have he : a = (one X).app _ a.1 := by
        apply Prod.ext
        · rfl
        · apply SSet.stdSimplex.obj₀Equiv.injective
          exact ht
      have hc := ConcreteCategory.congr_hom (NatTrans.congr_app (one_cylinder X) (op ⦋0⦌)) a.1
      exact hc.symm.trans ((congrArg (fun b => (cylinder X).app _ b) he).symm.trans ha)
  · exact Or.inr ⟨z, hz⟩

end SSet.WalkingAdjunction.FatCone
