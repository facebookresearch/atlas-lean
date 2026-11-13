/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The equation `x^x y^y = z^z` (Erdős Problem 674)

Erdős Problem 674: are there any integer solutions to `x^x y^y = z^z` with `x, y, z > 1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Basic.Finite.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.SelfPowerEquationErdosProblem674Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #674, https://www.erdosproblems.com/674 (status PROVED
(LEAN)). UnsolvedMath record UM-30006978 (`EP-674`), dataset ulamai/UnsolvedMath v1.8.0.

The target states the stronger fact recorded on the problem page, that there are infinitely many
solutions: a single solution is a finite check of the explicit example. Compared with the
formal-conjectures statement `ErdosProblems/674.lean` (the module states
`erdos_674.variants.infinite`; no code imported).
-/

/-- Erdős Problem 674: the equation `x^x y^y = z^z` has infinitely many solutions in integers
`x, y, z > 1` (in particular at least one). -/
def selfPowerEquationInfinitelyManySolutions : Prop :=
  {t : ℕ × ℕ × ℕ | 1 < t.1 ∧ 1 < t.2.1 ∧ 1 < t.2.2 ∧
    t.1 ^ t.1 * t.2.1 ^ t.2.1 = t.2.2 ^ t.2.2}.Infinite

/--
Resolved true: there are infinitely many solutions, for example `x = 2¹² 3⁶`, `y = 2⁸ 3⁸`, `z = 2¹¹
3⁷`, and more generally Ko's family with `a = 2^{n+1}`, `b = 2^n - 1`: `x = 2^{a(b-n)} b^{2b}
2^{2n}`, `y = 2^{a(b-n)} b^{2b} b²`, `z = 2^{a(b-n)} b^{2b} 2^{n+1} b` (`n ≥ 2`); Ko proved there
are none with `gcd(x, y) = 1`. erdosproblems.com/674 lists the problem as proved. Source: T. F.
Bloom, Erdős Problems, Problem #674, https://www.erdosproblems.com/674 (status PROVED (LEAN));
resolution: C. Ko, Note on the Diophantine equation x^x y^y = z^z, J. Chinese Math. Soc. 2 (1940),
205-207, erdosproblems.com/674: there are infinitely many solutions, e.g. x = 2¹² 3⁶, y = 2⁸ 3⁸, z =
2¹¹ 3⁷, and Ko's family x = 2^{a(b-n)} b^{2b} 2^{2n}, y = 2^{a(b-n)} b^{2b} b², z = 2^{a(b-n)}
b^{2b} 2^{n+1} b with a = 2^{n+1}, b = 2^n - 1, https://www.erdosproblems.com/674.
-/
public theorem_wanted selfPowerEquationInfinitelyManySolutions_holds :
    selfPowerEquationInfinitelyManySolutions

end MathlibExt.NumberTheory.SelfPowerEquationErdosProblem674Wanted
