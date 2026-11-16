/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Crypto.GGM

@[expose] public section

/-- Empty input returns the seed. -/
example (step : Bool → ℕ → ℕ) (s : ℕ) : ggmEval step s [] = s := rfl

end
