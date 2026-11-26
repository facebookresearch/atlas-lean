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

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Basic.UnivLE

/-!
# Exact coproducts under an indexing-universe bound

Let R be a commutative ring in universe u and let w be an indexing universe such that every
w-type admits a representative in u. Coproducts indexed by w-types exist in the category of
R-modules with carriers in u and preserve short exact sequences.

This gives AB4 of size w: for a w-indexed family of short exact module rows, the coproduct row
is short exact with the same coefficient universe. Filtered-colimit exactness and finite
biproducts supply this coproduct exactness.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicTopology

/-- Let R be a commutative ring in universe u and w an indexing universe with UnivLE(w,u), meaning
every w-type has a representative in u. Then ModuleCat_u(R) has AB4 of size w. For any I in w
and short exact rows 0→A_i→B_i→C_i→0, the coproduct row 0→⊕_i A_i→⊕_i B_i→⊕_i C_i→0 is short
exact. -/
public theorem moduleCatAB4OfSizeOfUnivLE
    (R : Type u) [CommRing R] [UnivLE.{w, u}] :
    AB4OfSize.{w} (ModuleCat.{u} R) := by
  let _ : HasFilteredColimitsOfSize.{w, w} (ModuleCat.{u} R) :=
    hasFilteredColimitsOfSize_of_univLE
  let _ : UnivLE.{u, u} := inferInstance
  let _ : AB5OfSize.{w, w} (ModuleCat.{u} R) :=
    AB5OfSize_of_univLE.{w, w, u, u} (ModuleCat.{u} R)
  let _ : HasFiniteBiproducts (ModuleCat.{u} R) :=
    Abelian.hasFiniteBiproducts
  exact AB4.of_AB5 (ModuleCat.{u} R)

end AlgebraicTopology

end
