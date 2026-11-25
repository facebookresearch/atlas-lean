/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.IntegralOperationalClasses

/-!
# Tests for integral operational classes

The cup product of classes of degrees `q` and `r` has degree `q + r` and caps
by `B` first, then `A`; the unit class caps by the identity. Both are classes
without further hypotheses.
-/

open AlgebraicGeometry IntegerSchemeChow IntegralOperationalChow IntegralGysinRecipes
open IntegralOperationalClasses

/-- The cup product caps by `B`, then by `A`, landing in degree `d - (q + r)`. -/
example {k : Type} [Field k] (O : CycleOperations (k := k)) (X : FieldScheme k) {q r : ℤ}
    (A : Class O X q) (B : Class O X r) (T : TestScheme X) (d : ℤ)
    (a : ChowGroup T.source d) :
    ((cupClass O X A B).val T d a : ChowGroup T.source (d - (q + r))) =
      chowCast T.source (by omega) (A.val T (d - r) (B.val T d a)) :=
  rfl

/-- The unit class caps by the identity. -/
example {k : Type} [Field k] (O : CycleOperations (k := k)) (X : FieldScheme k)
    (T : TestScheme X) (d : ℤ) (a : ChowGroup T.source d) :
    ((unitClass O X).val T d a : ChowGroup T.source (d - 0)) = chowCast T.source (by omega) a :=
  rfl

/-- Cup product with the unit, then a degree cast, is the identity. -/
example {k : Type} [Field k] (O : CycleOperations (k := k)) (X : FieldScheme k) {q : ℤ}
    (A : Class O X q) (T : TestScheme X) (d : ℤ) (a : ChowGroup T.source d) :
    chowCast T.source (by omega) ((cupClass O X A (unitClass O X)).val T d a) = A.val T d a := by
  simp only [cupClass, unitClass, cupFamily, identityFamily, AddMonoidHom.comp_apply,
    action_chowCast, chowCast_chowCast]
  rfl
