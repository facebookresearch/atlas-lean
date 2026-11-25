/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LeonardoPTilings
import Mathlib.Tactic.NormNum

/-!
# Tests for Leonardo tilings and hyper Lucas–Leonardo numbers
-/

open MetaMathlibExt

-- At the first admissible triple the corrected binomial term is one.
example : hyperLucasLeonardoP 1 2 1 = 9 ∧
    hyperLeonardoP 1 2 1 = 5 ∧ hyperLeonardoP 1 1 1 = 2 := by
  norm_num [hyperLucasLeonardoP, hyperLeonardoP, Finset.sum_range_succ, Nat.choose]

-- Order two, with the same summation cutoff at both indices.
example : hyperLucasLeonardoP 2 4 2 = 75 := by
  rw [hyperLucasLeonardoP_eq_hyperLeonardoP 2 4 2 (by decide) (by decide) (by decide)]
  norm_num [hyperLeonardoP, Finset.sum_range_succ, Nat.choose]

-- The special branches use the initial value at index zero and the ordinary sequence at order zero.
example : hyperLucasLeonardoP 2 0 3 = 7 ∧ hyperLucasLeonardoP 2 3 0 = 10 := by
  norm_num [hyperLucasLeonardoP, lucasLeonardoP, lucasTypeSeq]

-- A colored tile of length p + 1 is allowed initially and has a phase on the circular board.
example : (some (0, 3), []) ∈ leonardoPTilings 2 3 := by
  simp [leonardoPTilings]

example : (.shortTile 0 1, []) ∈ lucasLeonardoBracelets 2 3 ∧
    (.longTile 0 3, []) ∉ lucasLeonardoBracelets 2 3 := by
  simp [lucasLeonardoBracelets, BraceletFirstTile.length]
