/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.InfiniteRieselRepdigits

namespace MetaMathlibExt

-- With digit and base differing by one, the one-digit repdigit is the digit itself.
example : repstring 509204 509203 0 1 = 509203 := by norm_num [repstring]

-- The infinitude theorem supplies a Riesel repdigit, whose value at n = 1 is composite.
example : ∃ N : ℕ, IsRieselNumber N ∧ ¬ (N * 2 - 1).Prime := by
  obtain ⟨N, hN⟩ := (infinite_riesel_repdigits (b := 509204) (by norm_num)).nonempty
  obtain ⟨k, t, -, -, -, -, hR⟩ := hN
  exact ⟨N, hR, by simpa using hR.2 1 le_rfl⟩

end MetaMathlibExt
