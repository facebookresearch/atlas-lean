/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.CategoryTheory.NerveHomotopy

/-!
# Constant-simplex nerve homotopy tests

These checks exercise the generic constant-simplex computation on the
identity `1`-simplex of `Δ[1]`, whose order map contains the load-bearing
`0 → 1` transition.

No relative homotopy, stationarity, Waldhausen, realization, or additivity
claim is made here.
-/

open CategoryTheory Opposite Simplicial
open scoped Simplicial

universe v u w

namespace MathlibExtTest.CategoryTheory.NerveHomotopyConstantTests

private def crossingTime :
    (Δ[1] : SSet.{w}).obj (op ⦋1⦌) :=
  SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)

/-- The chosen interval simplex takes the two vertices to `0` and `1`. -/
example :
    SSet.stdSimplex.asOrderHom crossingTime.{w} (0 : Fin 2) = 0 ∧
      SSet.stdSimplex.asOrderHom crossingTime.{w} (1 : Fin 2) = 1 :=
  ⟨rfl, rfl⟩

variable {C : Type u} [Category.{v} C]

/-- The theorem applies to a genuine crossing interval simplex, not only to
the two constant endpoint simplices. -/
example (c : C) :
    (NatTrans.nerveHomotopyMap (𝟙 (𝟭 C))).app (op ⦋1⦌)
        ⟨(Functor.const (Fin 2)).obj c, crossingTime.{max u v}⟩ =
      (nerveMap (𝟭 C)).app (op ⦋1⦌)
        ((Functor.const (Fin 2)).obj c) :=
  NatTrans.nerveHomotopyMap_const_apply_of_app_eqToHom
    (𝟙 (𝟭 C)) c rfl rfl crossingTime.{max u v}

end MathlibExtTest.CategoryTheory.NerveHomotopyConstantTests
