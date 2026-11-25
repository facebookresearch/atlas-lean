/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.PrimitiveLambdaRoots.LocalFactors

/-!
# Inequalities for primitive λ-roots modulo n
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.PrimitiveLambdaRootsWanted

/-- **Supermultiplicativity of the number of primitive λ-roots.** Let $R(n)$ be the number of
primitive λ-roots modulo $n$. For coprime natural numbers $m, n > 1$, we have
$R(m)\,R(n) \le R(mn)$, and $R(mn) = R(m)\,R(n)$ if and only if $m = 2$ and $n$ is odd, or
$n = 2$ and $m$ is odd.

Source: Benjamin Huang and Shuguang Li, "Notes on the Number of
Primitive λ-roots mod n and Its Multiplicative Properties",
Theorem 1. -/
theorem_wanted primitiveLambdaRootCount_mul_ge_and_eq_iff
    (m n : ℕ) (hm : 1 < m) (hn : 1 < n) (hcop : Nat.Coprime m n) :
    primitiveLambdaRootCount m * primitiveLambdaRootCount n ≤
        primitiveLambdaRootCount (m * n) ∧
      (primitiveLambdaRootCount (m * n) =
          primitiveLambdaRootCount m * primitiveLambdaRootCount n ↔
        (m = 2 ∧ Odd n) ∨ (n = 2 ∧ Odd m))

end MathlibExt.NumberTheory.PrimitiveLambdaRootsWanted
