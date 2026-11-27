/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Batteries.Util.ProofWanted

@[expose] public section

namespace MetaMathlibExt

/-!
## Platt–Trudgian RH verification to height 3.0e12

Every zero `ρ` of `ζ` with `0 < Im ρ ≤ 3000175332800` satisfies
`Re ρ = 1/2` (the lowest 12363153437138 nontrivial zeros). The
universal quantifier over all `ρ` with `ζ ρ = 0` captures both the
critical-line claim and the completeness of the verified list
(Turing's method). This height covers the `H = 2445999556030` input
to Dusart's tables with room to spare, repairing the one
non-rigorous input (Gourdon–Demichel 2004) behind them.

Source: David Platt and Tim Trudgian, *The Riemann hypothesis is
true up to 3·10¹²*, Bull. Lond. Math. Soc. 53 (2021), 792–797,
Theorem `bank`, TeX line 62, arXiv:2004.09765,
<https://arxiv.org/html/2004.09765>.
-/

/-- **Platt–Trudgian verification of the Riemann hypothesis to height $3 \cdot 10^{12}$.** Every
zero $\rho$ of the Riemann zeta function with $0 < \operatorname{Im} \rho \le 3000175332800$
satisfies $\operatorname{Re} \rho = 1/2$. -/
public theorem_wanted platt_trudgian_rh_to_height (ρ : ℂ)
    (hzero : riemannZeta ρ = 0) (hpos : 0 < ρ.im)
    (hlt : ρ.im ≤ 3000175332800) :
    ρ.re = 1 / 2

end MetaMathlibExt
