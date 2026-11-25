/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Batteries.Util.ProofWanted
import MathlibExt.NumberTheory.LucasSequence

/-!
# Lucas numbers modulo m

The residues `{L_n mod m}` form a complete residue system iff
`m ∈ {2, 4, 6, 7, 14}` or `m = 3^k`.
-/

namespace MathlibExt.NumberTheory.LucasNumbersModuloMWanted

/-- **Classification of moduli for which the Lucas numbers attain every residue.** The
proposition that for every integer $m > 1$, with $L_n$ the Lucas numbers, every residue modulo
$m$ is attained (for every $r$ with $0 \le r < m$ there is $n \ge 0$ with
$L_n \equiv r \pmod m$) if and only if $m \in \{2, 4, 6, 7, 14\}$ or $m = 3^k$ for some
integer $k \ge 1$.

Source: OPG-37402, Lucas Numbers Modulo m [OpenGarden]. -/
def Statement : Prop :=
  ∀ (m : ℕ), 1 < m →
    ((∀ r : ℕ, r < m → ∃ n : ℕ, MetaMathlibExt.lucasNumber n % m = r) ↔
      (m = 2 ∨ m = 4 ∨ m = 6 ∨ m = 7 ∨ m = 14 ∨
        ∃ k : ℕ, 1 ≤ k ∧ m = 3 ^ k))

/--
**Avila–Chen theorem on Lucas numbers modulo $m$.** Let $L_n$ denote the Lucas numbers. For every
integer $m > 1$, every residue modulo $m$ is attained by the Lucas numbers (for every $r$ with
$0 \le r < m$ there is $n \ge 0$ with $L_n \equiv r \pmod m$) if and only if
$m \in \{2, 4, 6, 7, 14\}$ or $m = 3^k$ for some integer $k \ge 1$.

Source: Brandon Avila and Yongyi Chen, On Moduli For Which the Lucas Numbers Contain a Complete
Residue System, Fibonacci Quarterly 51(2) (2013), 151–152,
https://doi.org/10.1080/00150517.2013.12427958. Moved from
`OpenConjectures/NumberTheory/LucasNumbersModuloM`.
-/
theorem_wanted Statement_holds : Statement

end MathlibExt.NumberTheory.LucasNumbersModuloMWanted
