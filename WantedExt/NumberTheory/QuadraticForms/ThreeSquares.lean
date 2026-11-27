/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticForms.ThreeSquares
public import Mathlib.Data.Rat.Defs
import Batteries.Util.ProofWanted

@[expose] public section

namespace Nat

/-- **Gauss's three-square formula, residues 1, 2, 5, 6 modulo 8.** For every positive natural
number $n$ with $n \equiv 1$, $2$, $5$ or $6 \pmod 8$, the number $r_3(n)$ of ordered triples
$(x, y, z)$ of integers with $x^2 + y^2 + z^2 = n$ equals $12 H(4n)$, where $H$ is the Hurwitz
class number.

Source: arXiv:2307.05244 `main.tex` lines 191-199 (span SHA-256
    `39c31ed010dd887f8865ff9c7c36f814bf598c58f691b2954a6d0f62ad1fc1e2`). -/
theorem_wanted threeSquareRepresentationCount_eq_twelve_mul_hurwitzClassNumber_four_n
    (n : ℕ) (hn : 0 < n)
    (h : n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 5 ∨ n % 8 = 6) :
    (threeSquareRepresentationCount n : ℚ) = 12 * hurwitzClassNumber (4 * n)

/-- **Gauss's three-square formula, residue 3 modulo 8.** For every positive natural number $n$
with $n \equiv 3 \pmod 8$, the number $r_3(n)$ of ordered triples $(x, y, z)$ of integers with
$x^2 + y^2 + z^2 = n$ equals $24 H(n)$, where $H$ is the Hurwitz class number.

Source:
    arXiv:2307.05244 `main.tex` lines 191-199 (span SHA-256
    `39c31ed010dd887f8865ff9c7c36f814bf598c58f691b2954a6d0f62ad1fc1e2`). -/
theorem_wanted threeSquareRepresentationCount_eq_twenty_four_mul_hurwitzClassNumber
    (n : ℕ) (hn : 0 < n) (h : n % 8 = 3) :
    (threeSquareRepresentationCount n : ℚ) = 24 * hurwitzClassNumber n

end Nat
