/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.LSeries.HurwitzZeta

/-! # Lerch's formulas for the Hurwitz zeta function -/

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators

/-- **Lerch's formula for the Hurwitz zeta function at $s = 0$.** For every real $a > 0$,
the Hurwitz zeta function has value $1/2-a$ and complex derivative
$\log \Gamma(a)-\log(2\pi)/2$ at $s = 0$.

Mathlib's `HurwitzZeta.hurwitzZeta` takes a parameter modulo $1$. To recover the Hurwitz zeta
function for arbitrary positive $a$, write $a=b+k$ with $k=\lceil a\rceil-1\in\mathbb N$ and
$0<b\le1$. Subtract $\sum_{j=0}^{k-1}(b+j)^{-s}$ from the function with parameter $b$.
For $a=1$, this gives the value and derivative of the Riemann zeta function at zero.

Source: *NIST Digital Library of Mathematical Functions*, Chapter 25, equations 25.11.4,
25.11.13 and 25.11.18, <https://dlmf.nist.gov/25.11>. -/
public theorem_wanted hurwitzZeta_zero_and_deriv (a : ℝ) (ha : 0 < a) :
    let k := Nat.ceil a - 1
    let b := a - (k : ℝ)
    let zeta : ℂ → ℂ := fun s ↦
      HurwitzZeta.hurwitzZeta (b : UnitAddCircle) s -
        ∑ j ∈ Finset.range k, ((b + (j : ℝ) : ℝ) : ℂ) ^ (-s)
    zeta 0 = (1 : ℂ) / 2 - (a : ℂ) ∧
      HasDerivAt zeta ((Real.log (Real.Gamma a) - Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) 0

end

end MetaMathlibExt
