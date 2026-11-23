/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Languages.LambdaCalculus.SystemF.ErasureSimulation
import CSLibExt.Languages.LambdaCalculus.SystemF.Parametricity

/-! # Actual CBV substitution and erasure simulation probes -/

namespace Cslib.Languages.LambdaCalculus.SystemF

private def appliedId : Tm 0 0 := .app (.tapp polyId polyIdType) polyId

private theorem appliedId_steps : Steps appliedId polyId :=
  (Relation.ReflTransGen.single (.appFun .tyBeta)).tail (.beta .tabs)

example : Typing Fin.elim0 appliedId polyIdType :=
  .app (.tapp (polyId_typed Fin.elim0)) (polyId_typed Fin.elim0)

-- The actual two-step CBV computation maps to the existing upstream conversion.
example : BetaEq (Tm.eraseModel appliedId) (Tm.eraseModel (polyId : Tm 0 0)) :=
  erasure_steps appliedId_steps Fin.elim0

-- An open term beta step keeps an older variable out of the new lambda's scope.
example (x : Model) : BetaEq
    (Tm.close (fun _ : Fin 1 => x)
      (.app (.lam (.arr (.var 0) (.var 0)) (.var 1))
        (.lam (.var 0) (.var 0)) : Tm 1 1)) x :=
  erasure_step (.beta .lam) (fun _ : Fin 1 => x)

-- Both sides of the binder cutoff, and a locally bound variable, are exercised.
example : shiftAt 0 (.bvar 0) = .bvar 1 := rfl
example : shiftAt 1 (.bvar 0) = .bvar 0 := rfl
example : shiftAt 0 (.abs (.bvar 0)) = .abs (.bvar 0) := rfl

-- CBV evaluates the argument only after the function is a value.
example : Step
    (.app (.lam (.arr polyIdType polyIdType) (.var 0))
      (.tapp (polyId : Tm 0 0) polyIdType))
    (.app (.lam (.arr polyIdType polyIdType) (.var 0))
      (.lam polyIdType (.var 0))) := .appArg .lam .tyBeta

-- Type application evaluates its function position before type beta.
example : Step
    (.tapp (.app (.lam polyIdType (.var 0)) (polyId : Tm 0 0)) polyIdType)
    (.tapp (polyId : Tm 0 0) polyIdType) := .tappFun (.beta .tabs)

-- Weak CBV never steps inside either value form.
example (t : Tm 0 0) : ¬ Step (polyId : Tm 0 0) t := by
  intro h
  cases h

end Cslib.Languages.LambdaCalculus.SystemF
