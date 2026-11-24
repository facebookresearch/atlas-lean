/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Homology.TotalComplexDownNat

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

example (n : ℕ) :
    Finite ((ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) ⁻¹' {n}) :=
  inferInstance

example {C : Type u} [Category.{v} C] [Preadditive C]
    [HasFiniteCoproducts C]
    (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    B.HasTotal (ComplexShape.down ℕ) :=
  inferInstance

end
