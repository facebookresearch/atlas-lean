/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHomologyBicomplex

/-! # Tests for the Bousfield--Kan homology bicomplex -/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe w vA uA

namespace SSet.BousfieldKanHomologyBicomplexTests

variable {J : Type w} [Category.{0} J]
  {A : Type uA} [Category.{vA} A] [Preadditive A]
  [HasCoproducts.{w} A]
  (R : A) (D : J ⥤ SSet.{w})

example (p q : ℕ) :
    ((bkAlternatingBicomplex A R D).X p).X q =
      ∐ fun _ : ((bkBarBisimplicial D).obj (op ⦋p⦌)).obj
        (op ⦋q⦌) => R :=
  bkAlternatingBicomplex_X_X A R D p q

example {E : J ⥤ SSet.{w}} (alpha : D ⟶ E) :
    bkAlternatingBicomplex A R D ⟶
      bkAlternatingBicomplex A R E :=
  (bkAlternatingBicomplexFunctor A R).map alpha

section

variable [Limits.HasCountableCoproducts A]

example (p q : ℕ) :
    (∐ fun _ : ((bkBarBisimplicial D).obj (op ⦋p⦌)).obj
      (op ⦋q⦌) => R) ⟶
        (bkAlternatingTotalComplex A R D).X (p + q) :=
  bkAlternatingTotalι A R D p q

end
end SSet.BousfieldKanHomologyBicomplexTests

end
