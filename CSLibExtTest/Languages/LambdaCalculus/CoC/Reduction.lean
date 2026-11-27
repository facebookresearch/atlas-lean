/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Languages.LambdaCalculus.CoC.Reduction

open MathlibExt.TheoryOfComputation.CoCStrongNormalizationWanted.ProgramVerification.CoCStrongNormalization

-- The substitution replaces the domain of the inner lambda but not its bound variable.
example :
    subst 0 (.pi (.srt .prop) (.var 0)) (.lam (.var 0) (.var 0)) =
      .lam (.pi (.srt .prop) (.var 0)) (.var 0) := rfl

-- Under a binder, substituting an open argument must lift it to avoid capture.
-- The bound variable stays at 0, and an index above the substitution is lowered.
example :
    subst 0 (.var 1) (.pi (.var 0) (.app (.var 0) (.app (.var 1) (.var 3)))) =
      .pi (.var 1) (.app (.var 0) (.app (.var 2) (.var 2))) := rfl
