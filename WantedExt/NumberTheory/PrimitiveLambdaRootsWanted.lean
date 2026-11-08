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

/-- The paper's `Δ_q(n)`.  The argument `q` is intended to be prime;
the definition is the displayed formula for every natural `q`. -/
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

/-- The paper's local factor `h_q(n)`, as a rational number. -/
def lambdaH (q n : ℕ) : ℚ :=
  if lambdaDelta q n = 0 then
    1
  else
    1 - 1 / (q : ℚ) ^ (lambdaDelta q n)

/-- The number `R(n)` of primitive λ-root residue classes modulo
`n`: units in `ZMod n` whose order is the Carmichael value `λ(n)`. -/
noncomputable def primitiveLambdaRootCount (n : ℕ) : ℕ :=
  Nat.card {a : (ZMod n)ˣ //
    orderOf a = ArithmeticFunction.carmichael n}

/-- **Lemma 1**: for coprime `m n > 1`, Carmichael's function
satisfies `λ(m*n) = lcm (λ m) (λ n)`.

Source: Benjamin Huang and Shuguang Li, "Notes on the Number of
Primitive λ-roots mod n and Its Multiplicative Properties",
Lemma 1. -/
theorem_wanted carmichael_mul_eq_lcm
    (m n : ℕ) (hm : 1 < m) (hn : 1 < n) (hcop : Nat.Coprime m n) :
    ArithmeticFunction.carmichael (m * n) =
      Nat.lcm (ArithmeticFunction.carmichael m)
        (ArithmeticFunction.carmichael n)

/-- **Lemma 2**: for coprime `m n > 1` and a prime divisor `q` of
`λ(m*n)`, one has `h_q(m*n) ≥ h_q(m) * h_q(n)`, with strict
inequality exactly under the three displayed `Δ_q` conditions.

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

/-- **Theorem 1**: for coprime `m n > 1`,
`R(m*n) ≥ R(m) * R(n)`, with equality exactly when one factor is
`2` and the other is odd.

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
