/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.HomologicalAlgebra.FilteredCochainSpectralSequence
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Tests for the spectral sequence of a filtered cochain complex

The E1 indices are checked at a negative filtration index and positive total degree, and the
first page is compared with the cone of the consecutive filtration step.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExtTest.HomologicalAlgebra.FilteredCochainSpectralSequence

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MathlibExt.HomologicalAlgebra.FilteredCochainSpectralSequence

example : coreE1.i₀ 3 (-2, 3) = OrderDual.toDual (1 : ℤ) := rfl
example : coreE1.i₁ (-2, 3) = OrderDual.toDual (-1 : ℤ) := rfl
example : coreE1.i₂ (-2, 3) = OrderDual.toDual (-2 : ℤ) := rfl
example : coreE1.i₃ 3 (-2, 3) = OrderDual.toDual (-4 : ℤ) := rfl
example : coreE1.deg (-2, 3) = (1 : ℤ) := rfl

example (F : FilteredObject (CochainComplex (ModuleCat ℚ) ℤ) ℤᵒᵖ) :
    ((spectralSequence F).page 1).X (-2, 3) ≅
      ((HomotopyCategory.homologyFunctor (ModuleCat ℚ) (.up ℤ)
        0).shift (1 : ℤ)).obj
        ((HomotopyCategory.quotient (ModuleCat ℚ) (.up ℤ)).obj
          (CochainComplex.mappingCone (F.filtration.diagram.map
            ((homOfLE (show (-2 : ℤ) ≤ -1 by norm_num)).op)))) :=
  firstPageIso F (-2) 3

end MathlibExtTest.HomologicalAlgebra.FilteredCochainSpectralSequence
