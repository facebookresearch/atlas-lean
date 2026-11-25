/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# An explicit formula and a recurrence for OEIS A265233

Statements from Juntao Jin, "An Explicit Formula and a
Recurrence for OEIS A265233", *Journal of Integer
Sequences* 29 (2026), Article 26.5.3
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Jin/jin48.html>).

The OEIS definition of `(a_n)` is not reproduced in the
extracted statements, so `a265233` is defined over `ℚ`
by the paper's Theorem 1(2) recurrence together with its
initial values `a_0 = 1`, `a_1 = 1`, `a_2 = 7`,
`a_3 = 56`, which determine the sequence. The explicit
formula of Theorem 1(1) and both parts of Corollary 2
are then stated as properties of this sequence; the
paper's Franel numbers `f_m = ∑_k C(m, k)^3` are the
existing `MetaMathlibExt.binomialPowerSeq 3 0 m`, cast
to `ℚ`. The
recurrence and the explicit formula were checked to
agree for `1 ≤ n ≤ 13` (values `1, 1, 7, 56, 495, 4686,
…`).

The paper's lemma that `f_m` is the coefficient of
`x^m y^m z^m` in `((x + y)(y + z)(z + x))^m` is proved
in `MathlibExt.NumberTheory.FranelDiagonalCoeff`, which
this module imports.

Corollary 2(1) is stated analytically on the common
convergence domain `|x| < 1/12` and
`|27x(1 - 4x)^2| < 1` (Mathlib's `₂F₁` takes the junk
value `0` outside its radius of convergence). It is
proved in
`MathlibExt.NumberTheory.OeisA265233GeneratingFunction`,
which this module imports.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.ArithmeticFunction.BinomialPowerRealizability
public import MathlibExt.NumberTheory.FranelDiagonalCoeff
public import MathlibExt.NumberTheory.OeisA265233
public import MathlibExt.NumberTheory.OeisA265233GeneratingFunction

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.OeisA265233Wanted

/-- **Asymptotics of A265233.** The sequence $(a_n)_{n \ge 0}$ A265233 satisfies

$$a_n \sim \frac{\sqrt{3}}{6\pi} \cdot \frac{12^n}{n} \quad \text{as } n \to \infty.$$

Source: Juntao Jin, "An Explicit Formula and a
Recurrence for OEIS A265233", Corollary 2. -/
theorem_wanted a265233_isEquivalent :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => (a265233 n : ℝ))
      (fun n : ℕ => Real.sqrt 3 / (6 * Real.pi) * 12 ^ n / n)

end MathlibExt.NumberTheory.OeisA265233Wanted
