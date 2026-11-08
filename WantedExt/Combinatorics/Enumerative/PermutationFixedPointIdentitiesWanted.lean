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

/-- Pain's Theorem 2, with the paper's implicit parameter domain made
explicit: for `n ≥ 2`, `1 ≤ k`, and `k + 1 ≤ n`, the signed falling
fixed-point moment is
`(x - 1) ^ (n - k - 1) * n ! * (x + n - k - 1) / (n - k)!`.

The falling factor is written as a product over `Finset.range k`.
Together with the natural subtraction in `x ^ (fix σ - k)`, this gives
the polynomial derivative term also when `fix σ < k` (the product then
contains a zero factor).

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

/-- Pain's Theorem 3: for `n ≥ 2` and positive `k`, the signed sum of
`fix σ ! / (fix σ + k)!` over all permutations of `Fin n` has the
displayed closed form.

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
