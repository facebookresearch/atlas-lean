/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.RationalPermutationGroupDisplacementKourovka20Problem98
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Rat.Denumerable

open MathlibExt.GroupTheory.RationalPermutationGroupDisplacementKourovka20Problem98Wanted

-- In the regular action of the rationals, some translation has infinitely many displacements
-- when points are numbered by the natural numbers.
example : ∃ q : ℚ, {d : ℤ | ∃ a : ℕ,
    (a : ℤ) - (Denumerable.eqv ℚ (q + (Denumerable.eqv ℚ).symm a) : ℤ) = d}.Infinite := by
  let e := (@Multiplicative.toAdd ℚ).trans (Denumerable.eqv ℚ)
  let φ := e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom (Multiplicative ℚ) _)
  have hφ : Function.Injective φ := e.permCongrHom.injective.comp MulAction.toPerm_injective
  obtain ⟨_, ⟨q, rfl⟩, h⟩ := rationalPermutationGroupInfiniteDisplacement_holds φ.range
    ⟨(MonoidHom.ofInjective hφ).symm⟩
  exact ⟨q.toAdd, h⟩
