/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Sort.QuickExpectedRecurrence

namespace Cslib.Algorithms.Lean.TimeM

/-- Boundary check: `E 2 = 1` by the closed form (the value that
refuted the earlier draft closed form), and `E 0 = 0`. -/
example : qsExpected 0 = 0 ∧ qsExpected 2 = 1 :=
  ⟨rfl, by norm_num [qsExpected, qsPair]⟩

end Cslib.Algorithms.Lean.TimeM
