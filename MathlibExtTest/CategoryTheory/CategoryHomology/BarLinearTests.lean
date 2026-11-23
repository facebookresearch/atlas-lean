/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.CategoryHomology.BarLinear

/-!
# Weak-hypothesis public clients of additive and linear coefficient bars

The first client combines subtraction with a nontrivial integer scalar and
checks an actual degree map. The second forms the native mapLinearMap, so it
requires both the additive and the scalar-linear instances under preadditivity.
-/

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryHomology

universe wS uJ vJ uV vV

namespace CategoryHomologyBarLinearTests

variable {J : Type uJ} [Category.{vJ} J]
  {V : Type uV} [Category.{vV} V] [Preadditive V]
  [HasCoproducts.{max uJ vJ} V]
  {M N : J ⥤ V}

/-- Integer subtraction is respected by every actual coefficient-bar degree map. -/
example (α β : M ⟶ N) (n : ℕ) :
    coefficientBarMap ((2 : ℤ) • α - β) n =
      (2 : ℤ) • coefficientBarMap α n - coefficientBarMap β n := by
  fail_if_success
    have : Abelian V := inferInstance
  have h :
      (coefficientBarSimplicialFunctor (C := J) (A := V)).map ((2 : ℤ) • α - β) =
        (2 : ℤ) • (coefficientBarSimplicialFunctor (C := J) (A := V)).map α -
          (coefficientBarSimplicialFunctor (C := J) (A := V)).map β := by
    rw [Functor.map_sub, Functor.map_zsmul]
  exact congrArg (fun η ↦ η.app (op (SimplexCategory.mk n))) h

/-- The native linear map exists and respects actual coefficient combinations. -/
example {S : Type wS} [Semiring S] [CategoryTheory.Linear S V]
    (α β : M ⟶ N) (s t : S) :
    ((coefficientBarSimplicialFunctor (C := J) (A := V)).mapLinearMap S)
        (s • α + t • β) =
      s • (coefficientBarSimplicialFunctor (C := J) (A := V)).map α +
        t • (coefficientBarSimplicialFunctor (C := J) (A := V)).map β := by
  change (coefficientBarSimplicialFunctor (C := J) (A := V)).map (s • α + t • β) = _
  rw [Functor.map_add, Functor.map_smul, Functor.map_smul]

end CategoryHomologyBarLinearTests

end
