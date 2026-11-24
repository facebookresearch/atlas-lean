/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
# Genuine descent of a nondegenerate simplex factor

An original nondegenerate epi factor descends through any other actual
epi factor of the SAME complete source simplex. The map is the actual
native ordinal section composite; its whole simplex and vertex formulas
are proved using native degeneracy uniqueness.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalSimplexDescent

variable {K : SSet.{u}} {n m l : ℕ}

/-- The SAME native ordinal section composite for a pair of original epi factors. -/
noncomputable def operator (F : ⦋n⦌ ⟶ ⦋m⦌) (G : ⦋n⦌ ⟶ ⦋l⦌) [Epi G] : ⦋l⦌ ⟶ ⦋m⦌ := by
  let := isSplitEpi_of_epi G
  exact section_ G ≫ F

/-- The whole original nondegenerate simplex factor pulls back to the SAME second input simplex. -/
theorem simplex_factor (s : K _⦋n⦌) (F : ⦋n⦌ ⟶ ⦋m⦌) (G : ⦋n⦌ ⟶ ⦋l⦌)
    [Epi G] (σ : K _⦋m⦌) (τ : K _⦋l⦌)
    (hF : s = K.map F.op σ) (hG : s = K.map G.op τ) :
    K.map (operator F G).op σ = τ := by
  let := isSplitEpi_of_epi G
  change K.map (section_ G ≫ F).op σ = τ
  rw [op_comp, CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply, ← hF, hG,
    ← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp, ← op_comp,
    IsSplitEpi.id, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The SAME original whole operator factorization is proved from the native nondegenerate simplex. -/
theorem operator_factor (s : K _⦋n⦌) (F : ⦋n⦌ ⟶ ⦋m⦌) [Epi F]
    (G : ⦋n⦌ ⟶ ⦋l⦌) [Epi G] (σ : K.nonDegenerate m) (τ : K _⦋l⦌)
    (hF : s = K.map F.op σ) (hG : s = K.map G.op τ) :
    G ≫ operator F G = F := by
  apply (SSet.unique_nonDegenerate_map K s F σ hF (G ≫ operator F G) σ ?_).symm
  rw [op_comp, CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply,
    simplex_factor s F G σ τ hF hG]
  exact hG

/-- The native descended original operator is itself epi. -/
theorem operator_epi (s : K _⦋n⦌) (F : ⦋n⦌ ⟶ ⦋m⦌) [Epi F]
    (G : ⦋n⦌ ⟶ ⦋l⦌) [Epi G] (σ : K.nonDegenerate m) (τ : K _⦋l⦌)
    (hF : s = K.map F.op σ) (hG : s = K.map G.op τ) : Epi (operator F G) := by
  rw [SimplexCategory.epi_iff_surjective]
  intro j
  obtain ⟨i, hi⟩ := (SimplexCategory.epi_iff_surjective (f := F)).mp inferInstance j
  refine ⟨G.toOrderHom i, ?_⟩
  exact (SimplexCategory.congr_toOrderHom_apply (operator_factor s F G σ τ hF hG) i).trans hi

/-- The SAME original nondegenerate factor is constant on every actual fibre of the second epi. -/
theorem vertex_fibre_constant (s : K _⦋n⦌) (F : ⦋n⦌ ⟶ ⦋m⦌) [Epi F]
    (G : ⦋n⦌ ⟶ ⦋l⦌) [Epi G] (σ : K.nonDegenerate m) (τ : K _⦋l⦌)
    (hF : s = K.map F.op σ) (hG : s = K.map G.op τ)
    (i j : Fin (n + 1)) (hij : G.toOrderHom i = G.toOrderHom j) :
    F.toOrderHom i = F.toOrderHom j := by
  have h := operator_factor s F G σ τ hF hG
  exact (SimplexCategory.congr_toOrderHom_apply h i).symm.trans
    ((congrArg (operator F G).toOrderHom hij).trans (SimplexCategory.congr_toOrderHom_apply h j))

end SSet.OriginalSimplexDescent
