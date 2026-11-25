/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Languages.LambdaCalculus.CoC.Typing

open MathlibExt.TheoryOfComputation.CoCStrongNormalizationWanted.ProgramVerification.CoCStrongNormalization

-- Looking up index 1 lifts the stored type by 2, not 1.
example (h : Wf [.srt .prop, .var 0, .srt .prop]) :
    Typing [.srt .prop, .var 0, .srt .prop] (.var 1) (.var 2) :=
  Typing.var (A := .var 0) h rfl

-- Conversion still uses the reduction relation exported by the typing module.
example (A b a : Tm) : Conv (.app (.lam A b) a) (subst 0 a b) :=
  Conv.fwd (Conv.refl _) (Step.beta A b a)

example :
    Typing [] (.lam (.srt .prop) (.lam (.var 0) (.var 0)))
      (.pi (.srt .prop) (.pi (.var 0) (.var 1))) :=
  typing_polyId
