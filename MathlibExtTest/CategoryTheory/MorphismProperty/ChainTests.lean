/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.CategoryTheory.MorphismProperty.Chain

/-!
# Weak-equivalence chain tests

These tests pin the vacuous and one-arrow carriers, inclusion and
evaluation, arbitrary transitions, and the skip/degeneracy orientations of
simplex reindexing.
-/

open CategoryTheory

universe v u

namespace MathlibExtTest.CategoryTheory.MorphismProperty.ChainTests

variable {C : Type u} [Category.{v} C]
variable (P : MorphismProperty C)

/-- Degree zero imposes no transition condition. -/
example (X : ComposableArrows C 0) :
    morphismPropertyChainProperty P 0 X := by
  intro i
  exact Fin.elim0 i

/-- A one-arrow chain belongs exactly when its unique arrow belongs. -/
example {X Y : C} (f : X ⟶ Y) :
    morphismPropertyChainProperty P 1 (ComposableArrows.mk₁ f) ↔ P f := by
  constructor
  · intro h
    have h₀ := h (0 : Fin 1)
    change P f at h₀
    exact h₀
  · intro hf i
    fin_cases i
    change P f
    exact hf

private def chainOne {X Y : C} (f : X ⟶ Y) (hf : P f) :
    MorphismPropertyChain P 1 :=
  ⟨ComposableArrows.mk₁ f, by
    intro i
    fin_cases i
    change P f
    exact hf⟩

private def chainTwo {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : P f) (hg : P g) : MorphismPropertyChain P 2 :=
  ⟨ComposableArrows.mk₂ f g, by
    intro i
    fin_cases i
    · change P f
      exact hf
    · change P g
      exact hg⟩

example {X Y : C} (f : X ⟶ Y) (hf : P f) :
    (morphismPropertyChainInclusion P 1).obj (chainOne P f hf) =
      ComposableArrows.mk₁ f :=
  rfl

example {X Y : C} (f : X ⟶ Y) (hf : P f) :
    (morphismPropertyChainEval P 1 (0 : Fin 2)).obj
        (chainOne P f hf) = X :=
  rfl

example {X Y : C} (f : X ⟶ Y) (hf : P f) :
    (morphismPropertyChainEval P 1 (1 : Fin 2)).obj
        (chainOne P f hf) = Y :=
  rfl

section Multiplicative

variable [P.IsMultiplicative]

/-- Multiplicativity promotes adjacent membership to a skipped transition. -/
example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : P f) (hg : P g) :
    P ((chainTwo P f g hf hg).obj.map' 0 2) := by
  exact morphismPropertyChain_map_mem P 2 (chainTwo P f g hf hg)
    (homOfLE (by omega) : (0 : Fin 3) ⟶ (2 : Fin 3))

/-- The middle face skips vertex one and therefore composes the two arrows
in their original order. -/
example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : P f) (hg : P g) :
    ((reindexMorphismPropertyChain P
        (SimplexCategory.δ (1 : Fin 3))).obj
          (chainTwo P f g hf hg)).obj.map' 0 1 = f ≫ g := by
  rfl

/-- The zeroth degeneracy repeats the first vertex, so its first transition
is an identity. -/
example {X Y : C} (f : X ⟶ Y) (hf : P f) :
    ((reindexMorphismPropertyChain P
        (SimplexCategory.σ (0 : Fin 2))).obj
          (chainOne P f hf)).obj.map' 0 1 (by decide) (by decide) = 𝟙 X := by
  rfl

example {a b : SimplexCategory} (α : a ⟶ b)
    (X : MorphismPropertyChain P b.len) :
    ((reindexMorphismPropertyChain P α).obj X).obj =
      X.obj.whiskerLeft (SimplexCategory.toCat.map α).toFunctor :=
  reindexMorphismPropertyChain_obj P α X

example (a : SimplexCategory) :
    reindexMorphismPropertyChain P (𝟙 a) =
      𝟭 (MorphismPropertyChain P a.len) :=
  reindexMorphismPropertyChain_id P a

example {a b c : SimplexCategory} (α : a ⟶ b) (β : b ⟶ c) :
    reindexMorphismPropertyChain P (α ≫ β) =
      reindexMorphismPropertyChain P β ⋙
        reindexMorphismPropertyChain P α :=
  reindexMorphismPropertyChain_comp P α β

end Multiplicative

end MathlibExtTest.CategoryTheory.MorphismProperty.ChainTests
