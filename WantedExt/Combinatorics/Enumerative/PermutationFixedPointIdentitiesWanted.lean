/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Identities for permutations with fixed points

Statements from Jean-Christophe Pain, "Identities for Permutations
with Fixed Points", *Journal of Integer Sequences* 28 (2025),
Article 25.6.4
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Pain/pain3.html>).

The paper works with `n ≥ 2`.  Its signature is Mathlib's
`Equiv.Perm.sign`, and `fix σ` is
`Fintype.card (Function.fixedPoints σ)`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Dynamics.FixedPoints.Defs
public import Mathlib.GroupTheory.Perm.Sign

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.PermutationFixedPointIdentitiesWanted

/-- **Pain's signed falling-factorial identity for fixed points.** Let $n$ and $k$ be natural
numbers with $n \ge 2$, $k \ge 1$ and $k + 1 \le n$, and let $x$ be a real number. For a
permutation $\sigma$ of $\lbrace 0, 1, \dots, n-1 \rbrace$, write $\operatorname{sgn}(\sigma)$ for
its sign and $\operatorname{fix}(\sigma)$ for its number of fixed points, and for a natural number
$m$ write $(m)_k = m(m-1)\cdots(m-k+1)$ for the falling factorial. Then, summing over all
permutations $\sigma$ of this set,
$$\sum_{\sigma} \operatorname{sgn}(\sigma) (\operatorname{fix}(\sigma))_k
x^{\operatorname{fix}(\sigma) - k} = \frac{n!}{(n-k)!} (x-1)^{n-k-1} (x + n - k - 1),$$
where a term with $\operatorname{fix}(\sigma) < k$ is $0$ because then
$(\operatorname{fix}(\sigma))_k = 0$.

The left side is the $k$-th derivative in $x$ of
$\sum_{\sigma} \operatorname{sgn}(\sigma) x^{\operatorname{fix}(\sigma)}$.

Source: Jean-Christophe Pain, "Identities for Permutations with Fixed
Points", Theorem 2. -/
theorem_wanted sum_perm_sign_falling_fixedPoints_mul_pow
    (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) (x : ℝ) :
    (∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        (∏ j ∈ Finset.range k,
          ((Fintype.card (Function.fixedPoints σ) : ℝ) - j)) *
        x ^ (Fintype.card (Function.fixedPoints σ) - k)) =
      (x - 1) ^ (n - k - 1) *
        (Nat.factorial n : ℝ) * (x + n - k - 1) /
          (Nat.factorial (n - k) : ℝ)

/-- **Pain's signed factorial-ratio identity for fixed points.** Let $n$ and $k$ be natural
numbers with $n \ge 2$ and $k \ge 1$. For a permutation $\sigma$ of
$\lbrace 0, 1, \dots, n-1 \rbrace$, write $\operatorname{sgn}(\sigma)$ for its sign and
$\operatorname{fix}(\sigma)$ for its number of fixed points. Then, summing over all permutations
$\sigma$ of this set,
$$\sum_{\sigma} \operatorname{sgn}(\sigma)
\frac{\operatorname{fix}(\sigma)!}{(\operatorname{fix}(\sigma) + k)!} =
\frac{(-1)^{n+1} \left(n^2 + (k-1)n - (k-1)\right)}{(k-1)! (n+k-1)(n+k)}.$$

Source: Jean-Christophe Pain, "Identities for Permutations with Fixed
Points", Theorem 3. -/
theorem_wanted sum_perm_sign_factorial_fixedPoints_div
    (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    (∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ((Nat.factorial (Fintype.card (Function.fixedPoints σ)) : ℝ) /
          (Nat.factorial (Fintype.card (Function.fixedPoints σ) + k) : ℝ))) =
      (-1 : ℝ) ^ (n + 1) *
        ((n : ℝ) ^ 2 + ((k : ℝ) - 1) * n - ((k : ℝ) - 1)) /
          ((Nat.factorial (k - 1) : ℝ) * ((n : ℝ) + k - 1) *
            ((n : ℝ) + k))

end MathlibExt.Combinatorics.Enumerative.PermutationFixedPointIdentitiesWanted
