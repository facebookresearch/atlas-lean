/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta

@[expose] public section

namespace MathlibExt.NumberTheory.ZetaClassicalZeroFreeRegionWanted

/-!
# The classical zero-free region of the Riemann zeta function

There is an absolute constant `c > 0` such that the Riemann zeta function has no zero
`s = σ + i t` with `σ > 1 - c / log (2 + |t|)`.
-/

/-- **Classical zero-free region for the Riemann zeta function.** There is a constant `c > 0`
such that `ζ(s) ≠ 0` for every complex number `s ≠ 1` with `Re s > 1 - c / log (2 + |Im s|)`.
The point `s = 1`, where `ζ` has its pole, is excluded.

Source: T. Tao, *254A, Notes 2: Complex-analytic multiplicative number theory* (2014),
Proposition 38,
<https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/>.
Its proof combines the inequality `3 + 4 cos θ + cos 2θ ≥ 0` with the approximate formula for
`ζ'/ζ` near a zero (Proposition 19 there), which rests on Jensen's formula and the
Borel–Carathéodory theorem. -/
theorem_wanted riemannZeta_ne_zero_of_classical_zero_free_region :
    ∃ c : ℝ, 0 < c ∧
      ∀ s : ℂ, s ≠ 1 → 1 - c / Real.log (2 + |s.im|) < s.re → riemannZeta s ≠ 0

end MathlibExt.NumberTheory.ZetaClassicalZeroFreeRegionWanted
