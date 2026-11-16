/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.RootsFilter

@[expose] public section

/-- For `ζ = 1`, every term is `1` and the sum is the period. -/
example : (∑ j ∈ Finset.range 3, ((1 : ℂ) ^ 2) ^ j) = 3 := by
  have h := roots_filter (ζ := (1 : ℂ)) (k := 3) (by norm_num) (by norm_num) 2
  simpa using h

end
