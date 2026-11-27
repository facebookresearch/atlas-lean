/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.NumberTheory.PrimeCounting.ResidueClassPsi

/-!
# Bombieri–Vinogradov theorem — wishlist

This file records the classical Bombieri–Vinogradov theorem in its authoritative
von Mangoldt form: the average over moduli of the maximal residue-class error of
the Chebyshev psi function against the inner-variable main term `y / φ(q)`.
-/

@[expose] public section

namespace MetaMathlibExt.NumberTheory.PrimeCounting

/-- **Residue-class error of Chebyshev's function.** For natural numbers $y$, $q$ and $a$, the
residue-class error is $E(y; q, a) = \left|\psi(y; q, a) - y/\varphi(q)\right|$, where
$\psi(y; q, a)$ is Chebyshev's function in the residue class of $a$ modulo $q$ and $\varphi$ is
Euler's totient function.

Source: S. Baier and L. Zhao, *Bombieri-Vinogradov Type Theorem for Sparse Sets
of Moduli*, arXiv:math/0602116, classical theorem display (1.1). -/
public noncomputable def bombieriVinogradovResidueError (y q a : ℕ) : ℝ :=
  |Chebyshev.psiResidueClass (a : ZMod q) (y : ℝ) -
    (y : ℝ) / (Nat.totient q : ℝ)|

open Classical in
/-- **Maximal residue-class error.** For natural numbers $y$ and $q$, $E^{\ast}(y; q)$ is the
maximum of the residue-class error $E(y; q, a)$ over the natural numbers $a < q$ coprime to $q$,
and $0$ if there is no such $a$.

Source: S. Baier and L. Zhao, *Bombieri-Vinogradov Type Theorem for Sparse Sets
of Moduli*, arXiv:math/0602116, inner maximum of display (1.1). -/
public noncomputable def bombieriVinogradovMaxResidueError (y q : ℕ) : ℝ :=
  (((Finset.range q).filter fun a => Nat.Coprime a q).image
    fun a => bombieriVinogradovResidueError y q a).max.unbotD 0

open Classical in
/-- **Maximal residue-class error up to a level.** For natural numbers $x$ and $q$,
$E^{\ast\ast}(x; q)$ is the maximum of the maximal residue-class error $E^{\ast}(y; q)$ over the
natural numbers $y \le x$.

Source: S. Baier and L. Zhao, *Bombieri-Vinogradov Type Theorem for Sparse Sets
of Moduli*, arXiv:math/0602116, maximum over `y ≤ x` in display (1.1). -/
public noncomputable def bombieriVinogradovMaxUpToError (x q : ℕ) : ℝ :=
  ((Finset.range (x + 1)).image
    fun y => bombieriVinogradovMaxResidueError y q).max.unbotD 0

open Classical in
/-- **Bombieri–Vinogradov sum.** For a natural number $x$ and a real number $A$, the
Bombieri–Vinogradov sum $S(x, A)$ is the sum of the maximal residue-class error
$E^{\ast\ast}(x; q)$ up to $x$ over the integers $q$ with $1 \le q \le x$ and
$q \le \sqrt{x} / (\log x)^{A + 5}$.

When $A > -5$ and $x \ge 3$, the condition $q \le x$ follows from the other one.

Source: S. Baier and L. Zhao, *Bombieri-Vinogradov Type Theorem for Sparse Sets
of Moduli*, arXiv:math/0602116, outer sum of display (1.1). -/
public noncomputable def bombieriVinogradovSum (x : ℕ) (A : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (x + 1),
    if 0 < q ∧ (q : ℝ) ≤ Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 5)
    then bombieriVinogradovMaxUpToError x q else 0

/-- **Bombieri–Vinogradov theorem.** Let $\psi(y; q, a)$ denote Chebyshev's function in the
residue class of $a$ modulo $q$, and let $\varphi$ be Euler's totient function. For a natural
number $x$ and a real number $A$, let $S(x, A)$ be the sum, over the integers $q$ with
$1 \le q \le x$ and $q \le \sqrt{x} / (\log x)^{A + 5}$, of the maximum of
$\left|\psi(y; q, a) - y/\varphi(q)\right|$ over the natural numbers $y \le x$ and $a < q$
coprime to $q$. Then for every real number $A > 0$ there are a real number $C > 0$ and a natural
number $x_0$ such that every natural number $x \ge x_0$ satisfies $S(x, A) \le C x / (\log x)^A$.

The main term $y/\varphi(q)$ depends on the inner variable $y$; it is not a
logarithmic-integral term depending on $x$.

Source: S. Baier and L. Zhao, *Bombieri-Vinogradov Type Theorem for Sparse Sets
of Moduli*, arXiv:math/0602116, classical theorem display (1.1), source lines
54–62. The official source bundle has SHA-256
`86b591e2c1c73eadc18774d32318421b8f12a99ab89cc213a3f54aa7953da00f`, the TeX
file has SHA-256
`0826f6d0f8b5f5be49c6238fcdda2bb65d1b1b81a74c964a4328cb5454d0bdb4`, the exact
newline-terminated span has SHA-256
`0c8e89016584b4acbcc9a1c8fd12cb988749e827143e6e83c0e2c4cc025dff0a`, and the
semantic id is `jis_grounded_f3db17ecd03ec2208fa68754`. -/
public theorem_wanted bombieriVinogradov (A : ℝ) (hA : 0 < A) :
    ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧
      ∀ x : ℕ, x₀ ≤ x →
        bombieriVinogradovSum x A ≤ C * (x : ℝ) / (Real.log (x : ℝ)) ^ A

end MetaMathlibExt.NumberTheory.PrimeCounting
