/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Category.TopCat.ProdMapPointwise

@[expose] public section

/-!
# TopCat product pointwise helpers client

Direct-import clients for the fixed-left `prodIsoProd` inverse transport
and product-point extensionality. No quotient/pushout preservation,
fixed-right theorem, DeltaGenerated, realization, or model-category result.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopCat

universe u

namespace MathlibExtTest.Topology.ProdMapPointwiseTests

/-- Client restating fixed-left `prodIsoProd` inverse transport. -/
theorem prodMap_prodIso_inv_apply_client {K X Y : TopCat.{u}} (f : X ⟶ Y)
    (k : ↑K) (x : ↑X) :
    (Limits.prod.map (𝟙 K) f) ((prodIsoProd K X).inv (k, x)) =
      (prodIsoProd K Y).inv (k, f x) :=
  TopCat.prodMap_prodIso_inv_apply f k x

/-- Client restating product-point extensionality. -/
theorem prod_point_ext_client {X Y : TopCat.{u}} {p q : ↑(X ⨯ Y)}
    (hfst : (Limits.prod.fst : X ⨯ Y ⟶ X) p =
      (Limits.prod.fst : X ⨯ Y ⟶ X) q)
    (hsnd : (Limits.prod.snd : X ⨯ Y ⟶ Y) p =
      (Limits.prod.snd : X ⨯ Y ⟶ Y) q) :
    p = q :=
  TopCat.prod_point_ext hfst hsnd

#check @TopCat.prodMap_prodIso_inv_apply
#check @TopCat.prod_point_ext
#print axioms TopCat.prodMap_prodIso_inv_apply
#print axioms TopCat.prod_point_ext
#print axioms prodMap_prodIso_inv_apply_client
#print axioms prod_point_ext_client

end MathlibExtTest.Topology.ProdMapPointwiseTests
