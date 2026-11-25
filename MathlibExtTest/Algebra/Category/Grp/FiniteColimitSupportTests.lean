/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

import MathlibExt.Algebra.Category.Grp.FiniteColimitSupport

noncomputable section

open CategoryTheory Limits

universe u v

#check @CategoryTheory.Limits.IsColimit.exists_finite_sum
#print axioms CategoryTheory.Limits.IsColimit.exists_finite_sum

example {I : Type u} {F : I → AddCommGrpCat.{max u v}}
    {V : AddCommGrpCat.{max u v}} {ι : ∀ i, F i ⟶ V}
    (hι : IsColimit (Cofan.mk V ι)) (y : V) :
    ∃ (s : Finset I) (x : ∀ i, F i), y = ∑ i ∈ s, ι i (x i) :=
  hι.exists_finite_sum y

end
