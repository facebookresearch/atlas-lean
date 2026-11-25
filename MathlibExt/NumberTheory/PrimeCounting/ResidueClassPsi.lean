/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# The Chebyshev psi function in a residue class

This file defines the von Mangoldt sum over one residue class, using the same
inclusive real cutoff convention as `Chebyshev.psi`.
-/

@[expose] public section

namespace Chebyshev

/-- **Chebyshev's function in a residue class.** For a natural number $q$, a residue class
$a \in \mathbb{Z}/q\mathbb{Z}$ and a real number $x$, $\psi(x; q, a)$ is the sum of the von
Mangoldt function $\Lambda(n)$ over the positive integers $n \le x$ with $n \equiv a \pmod q$. -/
noncomputable def psiResidueClass {q : ℕ} (a : ZMod q) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt.residueClass a n

/-- **The residue-class Chebyshev function vanishes below one.** For every natural number $q$,
every residue class $a \in \mathbb{Z}/q\mathbb{Z}$ and every real number $x < 1$, we have
$\psi(x; q, a) = 0$, where $\psi(x; q, a)$ is the sum of the von Mangoldt function $\Lambda(n)$
over the positive integers $n \le x$ with $n \equiv a \pmod q$. -/
theorem psiResidueClass_of_lt_one {q : ℕ} (a : ZMod q) {x : ℝ}
    (hx : x < 1) : psiResidueClass a x = 0 := by
  simp [psiResidueClass, Nat.floor_eq_zero.mpr hx]

end Chebyshev
