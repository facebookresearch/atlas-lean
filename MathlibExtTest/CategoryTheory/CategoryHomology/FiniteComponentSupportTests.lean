/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.CategoryHomology.FiniteComponentSupport
import MathlibExt.CategoryTheory.Monoidal.SInverseSCoreGrade

noncomputable section

open CategoryTheory Limits Algebra

universe u v

#check @CategoryTheory.categoryHomology_exists_finite_component_sum
#print axioms CategoryTheory.categoryHomology_exists_finite_component_sum

example (J : Type u) [Category.{v} J] (A : AddCommGrpCat.{max u v}) (q : ℕ)
    (y : (nerve J).homology (C := AddCommGrpCat.{max u v}) A q) :
    ∃ (s : Finset (ConnectedComponents J))
      (x : ∀ c : ConnectedComponents J, (nerve c.Component).homology (C := AddCommGrpCat.{max u v})
          A q),
      y = ∑ c ∈ s, SSet.homologyMap (nerveMap c.ι) A q (x c) :=
  categoryHomology_exists_finite_component_sum J A q y

example {C : Type u} [Category.{u} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (g : GrothendieckAddGroup (Skeleton C)) (A : AddCommGrpCat.{u}) (q : ℕ)
    (y : (nerve (SInverseS.CoreGrade (C := C) g)).homology (C := AddCommGrpCat.{u}) A q) :
    ∃ (s : Finset (ConnectedComponents (SInverseS.CoreGrade (C := C) g)))
      (x : ∀ c : ConnectedComponents (SInverseS.CoreGrade (C := C) g),
        (nerve c.Component).homology (C := AddCommGrpCat.{u}) A q),
      y = ∑ c ∈ s, SSet.homologyMap (nerveMap c.ι) A q (x c) :=
  categoryHomology_exists_finite_component_sum (SInverseS.CoreGrade (C := C) g) A q y

example {J : Type 1} [Category.{2} J] (A : AddCommGrpCat.{2}) (q : ℕ)
    (y : (nerve J).homology (C := AddCommGrpCat.{2}) A q) :
    ∃ (s : Finset (ConnectedComponents J))
      (x : ∀ c : ConnectedComponents J, (nerve c.Component).homology (C := AddCommGrpCat.{2}) A q),
      y = ∑ c ∈ s, SSet.homologyMap (nerveMap c.ι) A q (x c) :=
  categoryHomology_exists_finite_component_sum J A q y

example {J : Type 2} [Category.{1} J] (A : AddCommGrpCat.{2}) (q : ℕ)
    (y : (nerve J).homology (C := AddCommGrpCat.{2}) A q) :
    ∃ (s : Finset (ConnectedComponents J))
      (x : ∀ c : ConnectedComponents J, (nerve c.Component).homology (C := AddCommGrpCat.{2}) A q),
      y = ∑ c ∈ s, SSet.homologyMap (nerveMap c.ι) A q (x c) :=
  categoryHomology_exists_finite_component_sum J A q y

end
