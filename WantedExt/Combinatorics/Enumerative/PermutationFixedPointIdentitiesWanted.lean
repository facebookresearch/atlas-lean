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
public import MathlibExt.Combinatorics.Enumerative.PermutationFixedPointIdentities

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.PermutationFixedPointIdentitiesWanted

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
