/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.WeakHomotopySingularHomology

/-!
# Tests for weak-homotopy invariance of ordinary singular homology
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open AlgebraicTopology CategoryTheory HomologicalComplex Limits

universe w v u

namespace MathlibExtTest.WeakHomotopySingularHomology

#check @TopCat.weakHomotopyEquivalences.isIso_singularHomologyFunctor_map

section Generic

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C] [CategoryWithHomology C]
variable {X Y : TopCat.{w}} {f : X ⟶ Y}
variable (hf : TopCat.weakHomotopyEquivalences f) (A : C) (n : ℕ)

example : IsIso (((singularHomologyFunctor C n).obj A).map f) :=
  hf.isIso_singularHomologyFunctor_map A n

example : IsIso (((singularHomologyFunctor C 0).obj A).map f) :=
  hf.isIso_singularHomologyFunctor_map A 0

example : IsIso (((singularHomologyFunctor C (n + 1)).obj A).map f) :=
  hf.isIso_singularHomologyFunctor_map A (n + 1)

example (Z : TopCat.{w}) :
    IsIso (((singularHomologyFunctor C n).obj A).map (𝟙 Z)) :=
  (TopCat.weakHomotopyEquivalences.of_isIso (𝟙 Z))
    |>.isIso_singularHomologyFunctor_map A n

example {Z W : TopCat.{w}} (e : Z ≅ W) :
    IsIso (((singularHomologyFunctor C n).obj A).map e.hom) :=
  (TopCat.weakHomotopyEquivalences.of_isIso e.hom)
    |>.isIso_singularHomologyFunctor_map A n

end Generic

end MathlibExtTest.WeakHomotopySingularHomology

end
