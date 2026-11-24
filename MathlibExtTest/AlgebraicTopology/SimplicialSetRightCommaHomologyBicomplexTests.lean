/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaHomologyBicomplex

/-! # Tests for the right-comma homology bicomplex -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u vA uA

namespace SSet.RightCommaHomologyBicomplexTests

variable {C D : Type u} [Category.{0} C] [Category.{0} D]
  (F : C ⥤ D)

example {p q : ℕ} (x : RightCommaBidegreeGenerator F p q)
    (i : Fin (q + 1)) :
    F.map (x.totalChain.map' i.val q) ≫ x.terminalAnchor =
      (x.comma.obj i).hom :=
  x.map'_terminalAnchor i

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
  [HasCoproducts.{u} A] (R : A)

example (p q : ℕ) :
    ((rightCommaAlternatingBicomplex A R F).X p).X q ≅
      ∐ fun _ : RightCommaBidegreeGenerator F p q => R :=
  rightCommaAlternatingBidegreeIso A R F p q

end SSet.RightCommaHomologyBicomplexTests

end
