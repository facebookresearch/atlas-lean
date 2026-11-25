/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Chains of morphisms in a multiplicative property

For a morphism property `P`, this file bundles composable chains whose
successive arrows lie in `P`.  When `P` is multiplicative, every transition
in such a chain lies in `P`, so precomposition by a simplex-category map
again gives a chain of the same kind.

Morphisms of chains remain arbitrary natural transformations.  No exact,
additive, stage, nerve, realization, or K-theory structure is added.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Object property on composable arrows requiring every successive arrow
to satisfy `P`. -/
def morphismPropertyChainProperty (P : MorphismProperty C) (k : ℕ) :
    ObjectProperty (ComposableArrows C k) :=
  fun X => ∀ i : Fin k, P (X.map' i.val (i.val + 1))

/-- The full subcategory of composable chains whose successive arrows
satisfy `P`.  Its morphisms are all natural transformations. -/
abbrev MorphismPropertyChain (P : MorphismProperty C) (k : ℕ) :=
  (morphismPropertyChainProperty P k).FullSubcategory

/-- Fully faithful inclusion of `P`-chains into all composable arrows. -/
abbrev morphismPropertyChainInclusion (P : MorphismProperty C) (k : ℕ) :
    MorphismPropertyChain P k ⥤ ComposableArrows C k :=
  (morphismPropertyChainProperty P k).ι

/-- Evaluation of a `P`-chain at one vertex. -/
def morphismPropertyChainEval (P : MorphismProperty C) (k : ℕ)
    (i : Fin (k + 1)) : MorphismPropertyChain P k ⥤ C :=
  morphismPropertyChainInclusion P k ⋙ (evaluation _ _).obj i

@[simp]
theorem morphismPropertyChainEval_obj (P : MorphismProperty C) (k : ℕ)
    (i : Fin (k + 1)) (X : MorphismPropertyChain P k) :
    (morphismPropertyChainEval P k i).obj X = X.obj.obj i :=
  rfl

@[simp]
theorem morphismPropertyChainEval_map (P : MorphismProperty C) (k : ℕ)
    (i : Fin (k + 1)) {X Y : MorphismPropertyChain P k} (f : X ⟶ Y) :
    (morphismPropertyChainEval P k i).map f = f.hom.app i :=
  rfl

private theorem morphismPropertyChain_map'_mem
    (P : MorphismProperty C) [P.IsMultiplicative] (k : ℕ)
    (X : MorphismPropertyChain P k) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ k) :
    P (X.obj.map' i j hij hj) := by
  revert hj
  induction j, hij using Nat.le_induction with
  | base =>
      intro hi
      rw [X.obj.map'_self i]
      exact P.id_mem _
  | succ j hij ih =>
      intro hj
      rw [X.obj.map'_comp i j (j + 1)]
      exact P.comp_mem _ _ (ih (by omega))
        (X.property ⟨j, by omega⟩)

/-- Every transition in a chain lies in `P` when `P` contains identities
and is closed under composition. -/
theorem morphismPropertyChain_map_mem
    (P : MorphismProperty C) [P.IsMultiplicative] (k : ℕ)
    (X : MorphismPropertyChain P k)
    {i j : Fin (k + 1)} (f : i ⟶ j) :
    P (X.obj.map f) := by
  have hij : i.val ≤ j.val := by
    simpa only [Fin.le_iff_val_le_val] using leOfHom f
  have h := morphismPropertyChain_map'_mem P k X i.val j.val hij
    (Nat.le_of_lt_succ j.isLt)
  rw [← homOfLE_leOfHom f]
  exact h

/-- Contravariant reindexing of `P`-chains along a simplex-category map. -/
def reindexMorphismPropertyChain
    (P : MorphismProperty C) [P.IsMultiplicative]
    {a b : SimplexCategory} (α : a ⟶ b) :
    MorphismPropertyChain P b.len ⥤ MorphismPropertyChain P a.len :=
  (morphismPropertyChainProperty P a.len).lift
    (morphismPropertyChainInclusion P b.len ⋙
      ComposableArrows.whiskerLeftFunctor
        (SimplexCategory.toCat.map α).toFunctor)
    (fun X i => by
      let h :
          (⟨i.val, by omega⟩ : Fin (a.len + 1)) ⟶
            ⟨i.val + 1, by omega⟩ :=
        homOfLE (by simp only [Fin.mk_le_mk]; omega)
      exact morphismPropertyChain_map_mem P b.len X
        ((SimplexCategory.toCat.map α).toFunctor.map h))

/-- Reindexing precomposes the underlying chain with the finite monotone map
represented by the simplex morphism. -/
@[simp]
theorem reindexMorphismPropertyChain_obj
    (P : MorphismProperty C) [P.IsMultiplicative]
    {a b : SimplexCategory} (α : a ⟶ b)
    (X : MorphismPropertyChain P b.len) :
    ((reindexMorphismPropertyChain P α).obj X).obj =
      X.obj.whiskerLeft (SimplexCategory.toCat.map α).toFunctor :=
  rfl

/-- Reindexing left-whiskers every natural transformation by the finite
monotone map represented by the simplex morphism. -/
@[simp]
theorem reindexMorphismPropertyChain_map
    (P : MorphismProperty C) [P.IsMultiplicative]
    {a b : SimplexCategory} (α : a ⟶ b)
    {X Y : MorphismPropertyChain P b.len} (f : X ⟶ Y) :
    ((reindexMorphismPropertyChain P α).map f).hom =
      Functor.whiskerLeft (SimplexCategory.toCat.map α).toFunctor f.hom :=
  rfl

/-- Reindexing by an identity simplex morphism is strictly the identity
functor. -/
@[simp]
theorem reindexMorphismPropertyChain_id
    (P : MorphismProperty C) [P.IsMultiplicative]
    (a : SimplexCategory) :
    reindexMorphismPropertyChain P (𝟙 a) =
      𝟭 (MorphismPropertyChain P a.len) := by
  rfl

/-- Reindexing reverses composition of simplex morphisms strictly. -/
@[simp]
theorem reindexMorphismPropertyChain_comp
    (P : MorphismProperty C) [P.IsMultiplicative]
    {a b c : SimplexCategory} (α : a ⟶ b) (β : b ⟶ c) :
    reindexMorphismPropertyChain P (α ≫ β) =
      reindexMorphismPropertyChain P β ⋙
        reindexMorphismPropertyChain P α := by
  rfl

end CategoryTheory

end
