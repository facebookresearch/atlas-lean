/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Languages.LambdaCalculus.SystemF.Parametricity

/-! # Arbitrary-inhabitant free-theorem and non-vacuity consumers -/

namespace Cslib.Languages.LambdaCalculus.SystemF

private def redexId : Tm 0 0 :=
  .tabs (.lam (.var 0) (.app (.lam (.var 0) (.var 0)) (.var 0)))

private theorem redexId_typed : Typing Fin.elim0 redexId polyIdType :=
  .tabs (.lam (.app (.lam (.var 0)) (.var 0)))

-- A distinct program, not just literal polyId, uses the general theorem.
example (x : Model) :
    BetaEq (Model.app (Tm.eraseModel (.tapp redexId polyIdType)) x) x :=
  polymorphic_identity redexId_typed polyIdType x

-- The second type is distinct and also contains quantified types.
example (x : Model) : BetaEq
    (Model.app
      (Tm.eraseModel (.tapp redexId (.arr polyIdType polyIdType))) x) x :=
  polymorphic_identity redexId_typed (.arr polyIdType polyIdType) x

-- Arbitrary binary relations connect the different type instantiations.
example (R : Rel) {x y : Model} (hxy : R.holds x y) :
    R.holds (Model.app (Tm.eraseModel (.tapp redexId polyIdType)) x)
      (Model.app
        (Tm.eraseModel (.tapp redexId (.arr polyIdType polyIdType))) y) :=
  polymorphic_related redexId_typed polyIdType
    (.arr polyIdType polyIdType) R hxy

example : (polyIdType : Ty 0) ≠ .arr polyIdType polyIdType := by
  intro h
  cases h

-- A True/equality-only universal semantics could not pass this probe.
example (x : Model) :
    ¬ ((Ty.all (.var 0) : Ty 0).interpret Fin.elim0).holds x x := by
  intro h
  exact h Rel.empty

example (t : Tm 0 0) : ¬ Typing Fin.elim0 t (.all (.var 0)) :=
  forall_var_uninhabited t

end Cslib.Languages.LambdaCalculus.SystemF
