/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHomologyBicomplex
public import MathlibExt.AlgebraicTopology.SimplicialSet.Homology.Coproducts

/-!
# Vertical homology of the Bousfield--Kan bicomplex

In a fixed outer degree, the Bousfield--Kan alternating bicomplex is the
simplicial chain complex of a coproduct of coefficient simplicial sets.
Since `AddCommGrpCat` coproducts are exact, its vertical homology is the
coproduct of the coefficient homologies.

The isomorphism here is objectwise in the outer degree.  Compatibility with
the horizontal differential is a separate gate, so no spectral-sequence
page is asserted.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe w v

namespace SSet

variable {J : Type w} [Category.{v} J]

/-- A fixed outer column of the Bousfield--Kan alternating bicomplex is the
simplicial chain complex of the corresponding weighted-bar degree. -/
theorem bkAlternatingBicomplex_X_eq_chainComplex
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v}) (p : ℕ) :
    (bkAlternatingBicomplex AddCommGrpCat.{max w v} R D).X p =
      (StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit J) D p).chainComplex R :=
  rfl

/-- Vertical homology in bidegree `(p,q)` is the coproduct, over weighted
base chains of degree `p`, of the degree-`q` homology of the coefficient
simplicial set at the left endpoint. -/
noncomputable def bkAlternatingVerticalHomologyIso
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v}) (p q : ℕ) :
    ((bkAlternatingBicomplex AddCommGrpCat.{max w v} R D).X p).homology q ≅
      ∐ fun x : StrictOrdinaryWeightedBar.WIdx J
        (CategoryBar.replUnit J) p =>
          (D.obj x.1.left).homology R q :=
  homologySigmaIso
    (fun x : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) p => D.obj x.1.left) R q

end SSet

end
