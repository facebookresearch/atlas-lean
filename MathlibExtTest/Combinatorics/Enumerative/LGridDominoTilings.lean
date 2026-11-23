/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.LGridDominoTilings

/-! # Tests for Tauraso's Cassini-type identity -/

open MetaMathlibExt

-- The least permitted index and the next index cover both signs of Fibonacci Cassini.
example : (3 : ℕ) ^ 2 = 4 * 2 + 1 :=
  domino_tilings_L_grid_via_fibonacci.2.2 2 (by decide)

example : (7 : ℕ) ^ 2 = 12 * 4 + 1 :=
  domino_tilings_L_grid_via_fibonacci.2.2 3 (by decide)
