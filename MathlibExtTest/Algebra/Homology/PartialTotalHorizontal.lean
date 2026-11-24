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

public import MathlibExt.Algebra.Homology.PartialTotalFirstPageDifferential
public import MathlibExt.Algebra.Homology.PartialTotalHorizontal

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

local instance : HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example (p q : ℕ) :
    (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩).Rel
      (p + 1, q) (p, q) :=
  HomologicalComplex₂.coreE₁IncreasingHomologicalNat_rel_succ p q

example (p q : ℕ) :
    B.d₁ (ComplexShape.down ℕ) (p + 1) q (p + q) =
      (B.d (p + 1) p).f q ≫
        B.ιTotal (ComplexShape.down ℕ) p q (p + q) rfl :=
  B.d₁_succ_eq_horizontal p q

example (q n : ℕ) :
    B.d₁ (ComplexShape.down ℕ) 0 q n = 0 :=
  B.d₁_zero_eq_zero q n

end HomologicalComplex₂

end
