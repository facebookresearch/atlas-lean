/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 7: power-difference series

The parametrized sum `φ_r(x) = ∑_{j ≥ 0} ((j + 1)ʳ - (j + 1 + x)ʳ)` of
B. C. Berndt, *Ramanujan's Notebooks, Part I* (Springer, 1985), Chapter 7,
shared by Entries 9 and 10 of that chapter.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

noncomputable section

/-- **Admissible parameters for the power-difference series.** A complex number $x$ is admissible
when $j + 1 + x \ne 0$ for every natural number $j$, that is, when $x$ is not one of
$-1, -2, -3, \dots$. -/
def chapter7Admissible (x : ℂ) : Prop :=
  ∀ j : ℕ, (j + 1 : ℂ) + x ≠ 0

/-- **Terms of the power-difference series.** For complex numbers $r$ and $x$ and a natural number
$j$, the $j$-th term is $(j + 1)^r - (j + 1 + x)^r$, where $w^r = e^{r \log w}$ is the principal
power for $w \ne 0$, while $0^r = 0$ for $r \ne 0$ and $0^0 = 1$. -/
def chapter7PowerDifferenceTerm (r x : ℂ) (j : ℕ) : ℂ :=
  Complex.cpow (j + 1 : ℂ) r - Complex.cpow ((j + 1 : ℂ) + x) r

/-- **The power-difference series.** For complex numbers $r$ and $x$,
$\varphi_r(x) = \sum_{j \ge 0} \bigl((j + 1)^r - (j + 1 + x)^r\bigr)$ (principal powers), where
the sum is taken to be $0$ when the series is not summable. -/
def chapter7PowerDifferenceSum (r x : ℂ) : ℂ :=
  ∑' j : ℕ, chapter7PowerDifferenceTerm r x j

@[simp]
theorem chapter7Admissible_zero : chapter7Admissible 0 := by
  intro j
  rw [add_zero]
  exact_mod_cast Nat.succ_ne_zero j

@[simp]
theorem chapter7PowerDifferenceTerm_zero_left (x : ℂ) (j : ℕ) :
    chapter7PowerDifferenceTerm 0 x j = 0 := by
  simp [chapter7PowerDifferenceTerm]

@[simp]
theorem chapter7PowerDifferenceTerm_zero_right (r : ℂ) (j : ℕ) :
    chapter7PowerDifferenceTerm r 0 j = 0 := by
  simp [chapter7PowerDifferenceTerm]

end

end MathlibExt.Analysis.Ramanujan.Part1Ch7
