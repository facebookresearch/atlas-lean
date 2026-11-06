/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 7: Berndt's `φ_r(x)`

The function `φ_r(x)` of B. C. Berndt, *Ramanujan's Notebooks, Part I* (Springer, 1985),
Chapter 7, shared by several entries of that chapter.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

/-- **Arguments of Berndt's $\varphi_r(x)$.** The open interval $(-1, 0)$ of real numbers, that
is, the set of real $x$ with $-1 < x < 0$.

On this interval $x + 1$ lies in $(0, 1)$, so the Hurwitz zeta function at parameter $x + 1$ is
not affected by reduction modulo $1$. -/
def Chapter7PhiArgument := Set.Ioo (-1 : ℝ) 0

/-- **Berndt's function $\varphi_r(x)$ on $(-1, 0)$.** For a complex number $r$ and a real number
$x$ with $-1 < x < 0$, $\varphi_r(x) = \zeta(-r) - \zeta(-r, x + 1)$, where $\zeta$ is the
Riemann zeta function and $\zeta(s, a)$ is the Hurwitz zeta function, both analytically continued
in $s$. At $r = -1$, where both have a pole, $\zeta(1)$ and $\zeta(1, x + 1)$ denote the finite
values that the formal definitions assign at the pole.

On this interval $x + 1$ lies in $(0, 1)$, so the Hurwitz zeta function at parameter $x + 1$ is
not affected by reduction modulo $1$.

Source: Bruce C. Berndt, *Ramanujan's Notebooks, Part I*, Chapter 7,
equation (2.4), p. 152. -/
noncomputable def chapter7Phi (r : ℂ) (x : Chapter7PhiArgument) : ℂ :=
  riemannZeta (-r) -
    HurwitzZeta.hurwitzZeta (((x : ℝ) + 1 : ℝ) : UnitAddCircle) (-r)

end MathlibExt.Analysis.Ramanujan.Part1Ch7
