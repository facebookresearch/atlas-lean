/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialAlternating

/-! # Tests for alternating bicomplexes of bisimplicial objects -/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Simplicial

universe v u

namespace AlgebraicTopology.BisimplicialAlternatingTests

variable {A : Type u} [Category.{v} A] [Preadditive A]
  (B : SimplicialObject (SimplicialObject A))

example (p q : ℕ) :
    ((bisimplicialAlternatingBicomplex A B).X p).X q =
      (B.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) :=
  bisimplicialAlternatingBicomplex_X_X A B p q

example (p q : ℕ) :
    ((bisimplicialAlternatingBicomplex A B).d (p + 1) p).f q =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        (B.δ i).app (Opposite.op ⦋q⦌) :=
  bisimplicialAlternatingBicomplex_horizontal_d_f_eq_sum A B p q

example (p : ℕ) :
    (bisimplicialAlternatingBicomplex A B).d (p + 1) p =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        (alternatingFaceMapComplex A).map (B.δ i) :=
  bisimplicialAlternatingBicomplex_horizontal_d_eq_sum A B p

section

variable [Limits.HasCountableCoproducts A]

example (p q : ℕ) :
    (B.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶
      (bisimplicialAlternatingTotalComplex A B).X (p + q) :=
  bisimplicialAlternatingTotalι A B p q

end
end AlgebraicTopology.BisimplicialAlternatingTests

end
