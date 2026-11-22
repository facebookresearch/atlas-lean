/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Primitive λ-roots modulo n

Statements from Benjamin Huang and Shuguang Li, "Notes on the Number
of Primitive λ-roots mod n and Its Multiplicative Properties",
*INTEGERS* 25 (2025), Article A34
(<https://math.colgate.edu/~integers/z34/z34.pdf>).

Here `λ(n)` is Mathlib's Carmichael function
`ArithmeticFunction.carmichael n`, the exponent of `(ZMod n)ˣ`.
A primitive λ-root is a unit whose multiplicative order is `λ(n)`,
and `R(n)` below is the number of such residue classes.

For a prime `q`, the paper's `Δ_q(n)` is zero when `q ∤ λ(n)`.
Otherwise, writing `q^v` for the exact power of `q` dividing
`λ(n)`, it counts the prime divisors `p` of `n` for which
`q^v ∣ λ(p^(v_p n))`, with the exceptional formula
`Δ₂(n) = 1 + #{prime p : p ∣ n}` when `2^3` exactly divides `n`
and `2` exactly divides `λ(n)`.  The factor `h_q(n)` is
`1 - q^(-Δ_q(n))` when `Δ_q(n) > 0`, and `1` otherwise.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.PrimitiveLambdaRootsWanted

/-- **The count $\Delta_q(n)$ for primitive λ-roots.** Let $\lambda$ be the Carmichael function
and, for natural numbers $p$ and $m$, let $v_p(m)$ be the exponent of $p$ in the prime
factorization of $m$ (taken to be $0$ when $p$ is not prime or $m = 0$). For natural numbers
$q$ and $n$, the natural number $\Delta_q(n)$ is defined as follows. If $q = 2$, $v_2(n) = 3$
and $v_2(\lambda(n)) = 1$, then $\Delta_q(n)$ is one more than the number of distinct prime
factors of $n$. Otherwise, if $q$ divides $\lambda(n)$, then $\Delta_q(n)$ is the number of
prime factors $p$ of $n$ (there are none when $n = 0$) such that $q^{v_q(\lambda(n))}$ divides
$\lambda(p^{v_p(n)})$. In all remaining cases $\Delta_q(n) = 0$.

The argument $q$ is intended to be prime; the definition is the displayed formula for every
natural $q$. -/
def lambdaDelta (q n : ℕ) : ℕ :=
  if q = 2 ∧ n.factorization 2 = 3 ∧
      (ArithmeticFunction.carmichael n).factorization 2 = 1 then
    1 + n.primeFactors.card
  else if q ∣ ArithmeticFunction.carmichael n then
    (n.primeFactors.filter fun p =>
      q ^ ((ArithmeticFunction.carmichael n).factorization q) ∣
        ArithmeticFunction.carmichael (p ^ n.factorization p)).card
  else
    0

/-- **The local factor $h_q(n)$ for primitive λ-roots.** Let $\Delta_q(n)$ be the count for
primitive λ-roots. For natural numbers $q$ and $n$, the rational number $h_q(n)$ equals $1$ if
$\Delta_q(n) = 0$, and $1 - 1/q^{\Delta_q(n)}$ otherwise. -/
def lambdaH (q n : ℕ) : ℚ :=
  if lambdaDelta q n = 0 then
    1
  else
    1 - 1 / (q : ℚ) ^ (lambdaDelta q n)

/-- **Number of primitive λ-roots.** For a natural number $n$, $R(n)$ is the number of units $a$
of $\mathbb{Z}/n\mathbb{Z}$ whose multiplicative order equals $\lambda(n)$, where $\lambda$ is
the Carmichael function. -/
noncomputable def primitiveLambdaRootCount (n : ℕ) : ℕ :=
  Nat.card {a : (ZMod n)ˣ //
    orderOf a = ArithmeticFunction.carmichael n}

/-- **Carmichael's function on coprime products.** For coprime natural numbers $m, n > 1$,
the Carmichael function $\lambda$ satisfies
$\lambda(mn) = \operatorname{lcm}(\lambda(m), \lambda(n))$.

Source: Benjamin Huang and Shuguang Li, "Notes on the Number of
Primitive λ-roots mod n and Its Multiplicative Properties",
Lemma 1. -/
theorem_wanted carmichael_mul_eq_lcm
    (m n : ℕ) (hm : 1 < m) (hn : 1 < n) (hcop : Nat.Coprime m n) :
    ArithmeticFunction.carmichael (m * n) =
      Nat.lcm (ArithmeticFunction.carmichael m)
        (ArithmeticFunction.carmichael n)

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
