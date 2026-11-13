/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Proofs of several conjectures from the OEIS

Statements from Sela Fried, "Proofs of Several
Conjectures From the OEIS", *Journal of Integer
Sequences* 28 (2025), Article 25.4.3
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Fried/fried15.html>).

`avoidZZ1Z k n` counts words of length `n` over a
`k`-letter alphabet with no consecutive pattern
`z, z+1, z`; the recurrence and initial values were
verified by brute force for `k ≤ 4`, `n ≤ 7`. The
bit-length formula was verified for `n ≤ 8`, and the
cube-root floor formula at `n = 3`.

Not stated (see the source audit table): Theorem 1 and
Corollary 2 (the polynomials `B_k^{(m)}` and numbers
`a_{n,k}^{(3)}`), Theorem 4 and Corollary 5 (the
generating function, whose extracted coefficients do
not match the counted sequence), Theorem 8 (median
absolute deviation), and Theorem 9 (whose defining
averaging condition is garbled in the extraction).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Size

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.OeisConjecturesWanted

/-- **Words avoiding the consecutive pattern $z, z+1, z$.** For natural numbers $k$ and $n$,
$f_k(n)$ is the number of words $w_0 w_1 \cdots w_{n-1}$ of length $n$ over the alphabet
$\{0, 1, \dots, k-1\}$ with no position $i$ such that $i + 2 < n$, $w_{i+1} = w_i + 1$ and
$w_{i+2} = w_i$. -/
def avoidZZ1Z (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin k)).filter (fun w =>
    ∀ i : Fin n, ∀ h1 : (i : ℕ) + 1 < n,
      ∀ h2 : (i : ℕ) + 2 < n,
        ¬ (w ⟨(i : ℕ) + 2, h2⟩ = w i ∧
          (w ⟨(i : ℕ) + 1, h1⟩ : ℕ) = (w i : ℕ) + 1))).card

/-- **Recurrence for words avoiding the pattern $z, z+1, z$.** Let $k \ge 1$ and, for each
natural number $n$, let $f_k(n)$ be the number of words of length $n$ over the alphabet
$\{0, 1, \dots, k-1\}$ that avoid the consecutive pattern $z, z+1, z$. Then $f_k(0) = 1$,
$f_k(1) = k$, $f_k(2) = k^2$, and $f_k(n) = k f_k(n-1) - f_k(n-2) + f_k(n-3)$ for every $n \ge 3$.

At $k = 0$ the recurrence would read $0 = 1$ at $n = 3$.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Theorem 3. -/
theorem_wanted avoidZZ1Z_spec (k : ℕ) (hk : 1 ≤ k) :
    avoidZZ1Z k 0 = 1 ∧ avoidZZ1Z k 1 = k ∧
      avoidZZ1Z k 2 = k ^ 2 ∧
      ∀ n : ℕ, 3 ≤ n →
        (avoidZZ1Z k n : ℤ) =
          (k : ℤ) * avoidZZ1Z k (n - 1) -
            avoidZZ1Z k (n - 2) + avoidZZ1Z k (n - 3)

/-- **Bit length of $\binom{2^n}{2^{n-1}}$.** For every integer $n \ge 1$, the binary expansion of
the binomial coefficient $\binom{2^n}{2^{n-1}}$ has exactly $2^n - \lfloor n/2 \rfloor$ digits.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Theorem 6. -/
theorem_wanted size_choose_two_pow (n : ℕ) (hn : 1 ≤ n) :
    Nat.size (Nat.choose (2 ^ n) (2 ^ (n - 1))) =
      2 ^ n - n / 2

/-- **Floor of a sum of cube roots.** For every integer $m \ge 1$, the sum
$S_m = \sum_{i=1}^{10^{3m}} i^{1/3}$ of the real cube roots of $1, 2, \dots, 10^{3m}$ satisfies

$$\lfloor S_m \rfloor = \frac{3 \cdot 10^{4m}}{4} + 5 \cdot 10^{m-1} - 1.$$

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Theorem 7. -/
theorem_wanted floor_sum_cbrt (m : ℕ) (hm : 1 ≤ m) :
    Nat.floor (∑ i ∈ Finset.Icc (1 : ℕ) (10 ^ (3 * m)),
        (i : ℝ) ^ (1 / 3 : ℝ)) =
      3 * 10 ^ (4 * m) / 4 + 5 * 10 ^ (m - 1) - 1

end MathlibExt.NumberTheory.OeisConjecturesWanted
