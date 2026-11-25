/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.ModuleProductExact

/-!
# Exact finite biproducts of sequences

The objectwise finite biproduct keeps every original differential through
`biproduct.map`. Its adjacent short complexes are the literal biproduct short
complexes, so component exactness gives exactness at every interior object.
The construction allows arbitrary sequence length and finite index universe.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory.Limits

universe u v

namespace CategoryTheory.ComposableArrows

variable {R : Type u} [Ring R] {I : Type v} [Finite I] {n : ℕ}
  (S : I → ComposableArrows (ModuleCat.{max u v} R) n)

/-- The actual finite objectwise biproduct with its original component maps. -/
def moduleBiproduct : ComposableArrows (ModuleCat.{max u v} R) n where
  obj j := ⨁ (fun i : I => (S i).obj j)
  map f := biproduct.map (fun i : I => (S i).map f)
  map_id j := by
    apply biproduct.hom_ext
    intro i
    simp only [biproduct.map_π, Functor.map_id, Category.comp_id, Category.id_comp]
  map_comp f g := by
    apply biproduct.hom_ext
    intro i
    simp only [Category.assoc, biproduct.map_π, biproduct.map_π_assoc, Functor.map_comp]

/-- The original component complex equations give the literal biproduct equations. -/
theorem moduleBiproduct_isComplex (hS : ∀ i, (S i).IsComplex) :
    (moduleBiproduct S).IsComplex where
  zero j hj := by
    change biproduct.map (fun i : I => (S i).map' j (j + 1)) ≫
      biproduct.map (fun i : I => (S i).map' (j + 1) (j + 2)) = 0
    apply biproduct.hom_ext
    intro i
    simp only [Category.assoc, biproduct.map_π, zero_comp]
    rw [← Category.assoc, biproduct.map_π, Category.assoc, (hS i).zero j hj, comp_zero]

/-- Exactness is inherited from the original component sequences at every interior object. -/
theorem moduleBiproduct_exact (hS : ∀ i, (S i).Exact) :
    (moduleBiproduct S).Exact where
  toIsComplex := moduleBiproduct_isComplex S (fun i => (hS i).toIsComplex)
  exact j hj := by
    change (ShortComplex.moduleBiproduct
      (fun i : I => (S i).sc (hS i).toIsComplex j hj)).Exact
    exact ShortComplex.moduleBiproduct_exact _ (fun i => (hS i).exact j hj)

end CategoryTheory.ComposableArrows
