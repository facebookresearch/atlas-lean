/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.ArithmeticFunction.Antimultiplicative
public import MathlibExt.NumberTheory.ArithmeticFunction.ArithmeticFunctionPerpendicularity
public import MathlibExt.NumberTheory.ArithmeticFunction.DirichletRealPower

/-!
# Perpendicularities of arithmetical functions

Statements from Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33.

Arithmetical functions are real-valued (`ArithmeticFunction ℝ`, whose multiplication is the
Dirichlet convolution and whose unit `1` is the paper's `δ`). `U` is the unit group, `U₁` the units
with `f 1 = 1`, `U_M` the multiplicative functions (Mathlib's `IsMultiplicative`) and `U_A` the
antimultiplicative functions (`IsAntimultiplicative`). The paper's real power `f^{(α)} = E(α Lf)`
(Rearick) is pinned by `L(f^{(α)}) = α L(f)`, with `L` the MathlibExt `rearickLog`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Unique splitting into multiplicative and antimultiplicative parts.** Every real
arithmetical function $f$ with $f(1) = 1$ can be written in exactly one way as a Dirichlet
convolution $f = g * h$ of a multiplicative real arithmetical function $g$ and an
antimultiplicative real arithmetical function $h$.

In the source, writing $U_1$, $U_M$ and $U_A$ for the real arithmetical functions $f$ with
$f(1) = 1$, the multiplicative ones and the antimultiplicative ones, this is written
$U_1 = U_M \oplus U_A$.

Source: Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33, Proposition 2 (`integers-2025-A33-prop-2`). -/
public theorem_wanted existsUnique_multiplicative_mul_antimultiplicative
    (f : ArithmeticFunction ℝ) (hf : f 1 = 1) :
    ∃! gh : ArithmeticFunction ℝ × ArithmeticFunction ℝ,
      gh.1.IsMultiplicative ∧ IsAntimultiplicative gh.2 ∧ gh.1 * gh.2 = f

end

end MetaMathlibExt
