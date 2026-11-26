/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import MathlibExt.Combinatorics.Enumerative.StirlingSecondGy
public import MathlibExt.Combinatorics.Enumerative.StirlingTripleProduct

/-!
# Triple products of Stirling numbers and of symmetric polynomials (statements)

Statement-only targets from René Gy, *On Certain Products of Three Stirling Numbers*,
INTEGERS 26 (2026), Article A108. `Nat.stirlingFirst` is the unsigned Stirling number of the
first kind `[n, k]` and `Nat.stirlingSecond` the Stirling number of the second kind `{n, k}`.
For a sequence `x : ℕ → ℝ` indexed from `1`, `e_k(x_m)` and `h_k(x_m)` are the elementary and
complete homogeneous symmetric polynomials of degree `k` evaluated at `(x_1, …, x_m)`, written
with `MvPolynomial.esymm` and `MvPolynomial.hsymm` over `Fin m`.
-/

namespace MetaMathlibExt

@[expose] public section

end

end MetaMathlibExt
