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
# Original left extra degeneracies in the augmentation slice

The existing native left extra degeneracy preserves the actual augmentation
by its original distinguished zeroth face. It therefore lifts through the
existing Augmented.overPoint functor. All face, degeneracy and actual prism
operators are preserved, including the original point map.

This is a general transport of actual native operator data, not an assertion
that arbitrary free resolutions have a contraction. The polynomial-model
application constructs its extra degeneracy from the native standard simplex.
No desired cotangent comparison, exactness or IsIso certificate is input.
Source UNEXECUTED; all frozen V12/V13 source and metadata bytes kept.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy

variable {C : Type u} [Category.{v} C] {X : SimplicialObject.Augmented C}
  (ed : ExtraDegeneracy X) {A : C}

/-- The original native left operators are actual morphisms over the original target. -/
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

/-- The slice prism is the original algebra prism on its original carriers. -/
theorem overPoint_homotopy_h_left (a : X.right ⟶ A) {n : ℕ} (i : Fin (n + 1)) :
    ((ed.overPoint a).homotopy.h i).left = ed.homotopy.h i := by
  dsimp only [ExtraDegeneracy.homotopy, ExtraDegeneracy.homotopy.h, overPoint,
    Augmented.overPoint, SimplicialObject.δ₀Iter, SimplicialObject.σ₀Iter]
  rfl

/-- Every actual original prism operator retains the complete point map. -/
@[reassoc]
theorem overPoint_homotopy_augmentation (a : X.right ⟶ A) {n : ℕ} (i : Fin (n + 1)) :
    ((ed.overPoint a).homotopy.h i).left ≫ (X.hom.app (op ⦋n + 1⦌) ≫ a) =
      X.hom.app (op ⦋n⦌) ≫ a :=
  ((ed.overPoint a).homotopy.h i).w

end CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy

end
