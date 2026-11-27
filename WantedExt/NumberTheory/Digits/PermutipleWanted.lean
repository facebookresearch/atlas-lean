/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Logic.Equiv.Fin.Rotate
public import MathlibExt.NumberTheory.Digits.HoeySloaneCycles
public import MathlibExt.NumberTheory.Digits.Permutiple
public import MathlibExt.NumberTheory.Digits.PermutipleCarryBound
public import MathlibExt.NumberTheory.Digits.PermutipleCycleRefinement
public import MathlibExt.NumberTheory.Digits.PermutiplePermutipleGraphEdgesUnionCycles

/-!
# Permutiples with a fixed set of digits (Holt)

Statements from B. V. Holt, *A Method for Finding All Permutiples with a Fixed
Set of Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88
(arXiv:2312.02056).

A `(k+1)`-digit base-`b` numeral `(d_k, …, d_0)_b` is a digit function
`d : Fin (k + 1) → ℕ` (digit `d j` has weight `b ^ j`); for a permutation `π`,
the numeral `(d_{π(k)}, …, d_{π(0)})_b` is `d ∘ π`.
-/

namespace MetaMathlibExt

@[expose] public section

end

end MetaMathlibExt
