/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Exp
public import MathlibExt.NumberTheory.ImaginaryQuadraticDiscriminant
public import WantedExt.NumberTheory.QuadraticForms.KroneckerFormSumsWanted

namespace MetaMathlibExt

/-- **Fowler's bound on imaginary quadratic order discriminants.** Let $D<0$ be congruent to
$0$ or $1$ modulo $4$ and let $k$ be a positive integer. If the class number $h(D)$ of the
order of discriminant $D$ is at most $k$, then $\sqrt{|D|} \le 2k^2\exp(21000k^2)$.

The class number is counted by primitive positive-definite Gauss-reduced binary quadratic forms,
using the unique reduced representative of each proper class. In particular, $D$ need not be
fundamental and this is not the weighted Hurwitz class number.

Source: Guy Fowler, *Some uniform effective results on André–Oort for sums of powers in*
$\mathbb{C}^n$, Math. Proc. Cambridge Philos. Soc. 180 (2026), 607–641,
[Proposition 2.7, p. 615](https://doi.org/10.1017/S0305004125101825). -/
public theorem_wanted sqrt_abs_discriminant_le_of_gaussClassNumber_le (D : ℤ) (k : ℕ)
    (hD : ImaginaryQuadraticDiscriminant.IsImaginaryQuadraticDiscriminant D)
    (hk : 0 < k) (hClass : gaussClassNumber D ≤ k) :
    Real.sqrt |(D : ℝ)| ≤ 2 * (k : ℝ) ^ 2 * Real.exp (21000 * (k : ℝ) ^ 2)

end MetaMathlibExt
