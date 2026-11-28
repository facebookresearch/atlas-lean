/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.BuchstabTaylor
public import MathlibExt.Combinatorics.Enumerative.GeneralizedBuchstabTaylor
public import MathlibExt.Combinatorics.Enumerative.SmallestCycleMoment
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Data.Fintype.Perm

/-!
# Gravel–Panario, smallest cycles and the (generalized) Buchstab function — wishlist

Statement-only records for Gravel and Panario, INTEGERS 24 (2024), Article A7
(source: arXiv:2212.12847v2 TeX). `X_n` is the length of the smallest cycle of
a uniformly random permutation of `Fin n`, written as
`⨅ x, Function.minimalPeriod σ x` (the cycle through `x` has length
`minimalPeriod σ x`); moments are averages over `Equiv.Perm (Fin n)`.

The Buchstab function `ω` and the generalized Buchstab function `Ω_K` enter as
hypotheses: any `ω : ℝ → ℝ` with `ω x = 1/x` on `[1, 2]` and
`x ω(x) = 1 + ∫_1^{x-1} ω` for `x ≥ 2` (the integrated form of
`(x ω(x))' = ω(x - 1)`), and any `Ω` with `Ω = 1` on `[1, 2)` and
`Ω(x) = 1 + K ∫_2^x Ω(u - 1)/(u - 1) du` for `x ≥ 2`. Both systems determine the
function on `[1, ∞)` interval by interval.
-/

open Real

namespace MetaMathlibExt

@[expose] public section

end

end MetaMathlibExt
