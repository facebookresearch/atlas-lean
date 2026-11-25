/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.StrongDeformationWeakEquivalence

/-!
# Tests for weak equivalences from strong deformation data
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe v u

open CategoryTheory CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.Precylinder.StrongDeformationWeakEquivalenceTest

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {P : Precylinder (𝟭 C)} {K L : C} {i : K ⟶ L}

/-- The generic consumer needs only the selected target projection, with no
cofibrancy, fibrancy or good-cylinder input. -/
example (D : P.StrongDeformationData i)
    (hπ : weakEquivalences C (P.app L).π) :
    weakEquivalences C i :=
  D.weakEquivalence_of_projection hπ

end HomotopicalAlgebra.Precylinder.StrongDeformationWeakEquivalenceTest
