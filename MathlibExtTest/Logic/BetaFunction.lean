/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.BetaFunction

@[expose] public section

/-- Beta values are bounded by the modulus. -/
example (c d : ℕ) : beta c d 3 < 1 + 4 * d := beta_lt c d 3

end
