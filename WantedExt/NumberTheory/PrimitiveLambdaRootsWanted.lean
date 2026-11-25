/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.PrimitiveLambdaRoots

/-!
# Inequalities for primitive λ-roots modulo n
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.PrimitiveLambdaRootsWanted

/-- **Huang–Li inequality for the local factors $h_q$.** Let $\lambda$ be the Carmichael function,
and let $\Delta_q$ and $h_q$ be the count and the local factor for primitive λ-roots. Let
$m, n > 1$ be coprime natural numbers and let $q$ be a prime dividing $\lambda(mn)$. Then
$h_q(m)\,h_q(n) \le h_q(mn)$. Moreover, $h_q(m)\,h_q(n) < h_q(mn)$ if and only if at least one
of the following holds: $0 < \Delta_q(m) < \Delta_q(mn)$; $0 < \Delta_q(n) < \Delta_q(mn)$; or
$\Delta_q(m) > 0$, $\Delta_q(n) > 0$, and $\Delta_q(mn)$ equals $\Delta_q(m)$ or $\Delta_q(n)$.

Source: Benjamin Huang and Shuguang Li, "Notes on the Number of
Primitive λ-roots mod n and Its Multiplicative Properties",
Lemma 2. -/
theorem_wanted lambdaH_mul_ge_and_gt_iff
    (m n q : ℕ) (hm : 1 < m) (hn : 1 < n)
    (hcop : Nat.Coprime m n) (hq : q.Prime)
    (hqdvd : q ∣ ArithmeticFunction.carmichael (m * n)) :
    lambdaH q m * lambdaH q n ≤ lambdaH q (m * n) ∧
      (lambdaH q m * lambdaH q n < lambdaH q (m * n) ↔
        (lambdaDelta q m < lambdaDelta q (m * n) ∧
            0 < lambdaDelta q m) ∨
          (lambdaDelta q n < lambdaDelta q (m * n) ∧
            0 < lambdaDelta q n) ∨
          (0 < lambdaDelta q m ∧ 0 < lambdaDelta q n ∧
            (lambdaDelta q (m * n) = lambdaDelta q m ∨
              lambdaDelta q (m * n) = lambdaDelta q n)))

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
