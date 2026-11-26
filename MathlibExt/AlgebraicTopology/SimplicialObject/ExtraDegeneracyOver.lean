/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.AugmentedOver
public import MathlibExt.AlgebraicTopology.SimplicialObject.ExtraDegeneracyPointBaseChange
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# Left extra degeneracies in an augmentation slice

Let X be augmented in a category C, with ε : X.left → const(B), a left extra degeneracy ed and
a : B → A. Its arrows s' : B → X₀ and s_n : X_n → X_{n+1} preserve augmentation: s' ≫ ε₀ =
id_B and s_n ≫ ε_{n+1} = ε_n.

They therefore define the same extra-degeneracy data on the augmented object in Over A whose
structural maps are ε_n ≫ a. All face and degeneracy identities remain true there. The
associated homotopy components have the same underlying arrows and commute with the structural
maps to A in every degree. The category worlds remain independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy

variable {C : Type u} [Category.{v} C] {X : SimplicialObject.Augmented C}
  (ed : ExtraDegeneracy X) {A : C}

/-- Left extra degeneracy lifted to a slice over the augmentation target.

For a left extra degeneracy ed on X and a : X.right → A, use its arrows s',s_n as morphisms in
Over A for Augmented.overPoint X a. Their augmentation equations provide the slice
compatibility, and the given face and degeneracy identities define the lifted extra
degeneracy. -/
def overPoint (a : X.right ⟶ A) : ExtraDegeneracy (Augmented.overPoint X a) where
  s' := Over.homMk ed.s' (by
    change ed.s' ≫ (X.hom.app (op ⦋0⦌) ≫ a) = a
    rw [← Category.assoc, ed.s'_comp_ε, Category.id_comp])
  s n := Over.homMk (ed.s n) (by
    change ed.s n ≫ (X.hom.app (op ⦋n + 1⦌) ≫ a) = X.hom.app (op ⦋n⦌) ≫ a
    rw [← Category.assoc, ed.s_comp_augmentation])
  s'_comp_ε := by
    apply Over.OverMorphism.ext
    exact ed.s'_comp_ε
  s₀_comp_δ₁ := by
    apply Over.OverMorphism.ext
    exact ed.s₀_comp_δ₁
  s_comp_δ₀ n := by
    apply Over.OverMorphism.ext
    exact ed.s_comp_δ₀ n
  s_comp_δ n i := by
    apply Over.OverMorphism.ext
    exact ed.s_comp_δ n i
  s_comp_σ n i := by
    apply Over.OverMorphism.ext
    exact ed.s_comp_σ n i

/-- Underlying homotopy components of a lifted extra degeneracy.

For a : X.right → A and i ∈ Fin(n+1), the underlying arrow of the i-th homotopy component
associated to ed.overPoint a equals ed.homotopy.h i. -/
theorem overPoint_homotopy_h_left (a : X.right ⟶ A) {n : ℕ} (i : Fin (n + 1)) :
    ((ed.overPoint a).homotopy.h i).left = ed.homotopy.h i := by
  dsimp only [ExtraDegeneracy.homotopy, ExtraDegeneracy.homotopy.h, overPoint,
    Augmented.overPoint, SimplicialObject.δ₀Iter, SimplicialObject.σ₀Iter]
  rfl

/-- Augmentation compatibility of lifted extra-degeneracy homotopies.

For each homotopy component h_{n,i} of ed lifted to Over A, its underlying map satisfies
h_{n,i} ≫ (ε_{n+1} ≫ a) = ε_n ≫ a. Thus every component remains a morphism over the same
target A. -/
@[reassoc]
theorem overPoint_homotopy_augmentation (a : X.right ⟶ A) {n : ℕ} (i : Fin (n + 1)) :
    ((ed.overPoint a).homotopy.h i).left ≫ (X.hom.app (op ⦋n + 1⦌) ≫ a) =
      X.hom.app (op ⦋n⦌) ≫ a :=
  ((ed.overPoint a).homotopy.h i).w

end CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy

end
