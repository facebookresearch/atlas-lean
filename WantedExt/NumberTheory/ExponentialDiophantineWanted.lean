/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Exponential Diophantine equations `(p+a)^x ± p^y = z^2`

Statements from Shalini Choudhury and Naba Kanta Sarma,
"On the Diophantine Equations `(p+a)^x + p^y = z^2` and
`(p+a)^x - p^y = z^2` where `p` and `p+a` Are Odd
Primes", *INTEGERS* 26 (2026), Article A87
(<https://math.colgate.edu/~integers/vol26.html>).

Only the paper's new Diophantine conclusions are stated
here; its Theorem 1 is Mihăilescu's theorem, already
recorded as `MathlibExt.NumberTheory.MihailescuWanted.mihailescu`,
and its Theorems 2–5 (Fermat's little theorem and
Legendre-symbol laws, including quadratic reciprocity)
are already in Mathlib; all five are recorded as
covered in the source audit table. Theorem 6 has no
unexpected small solutions across its first instances
(checked numerically).

Proved in `MathlibExt.NumberTheory.ExponentialDiophantine`:
Corollary 1, `19^x + 151^y` is never a square
(`MetaMathlibExt.pow19_add_pow151_ne_sq`).

Theorems 7 and 8 carry the Legendre-symbol hypothesis
`(a/p) = -1` (`legendreSym p a = -1`); both were checked
numerically on their first instances.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import MathlibExt.NumberTheory.ExponentialDiophantine

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.ExponentialDiophantineWanted

/-- **Theorem 6**: the Diophantine equation
`p^x + (p + a)^y = z^2`, where `a ≡ 0 (mod 4)` and
`a ≡ -1 (mod p)`, has no solution other than
`(x, y, z) = (0, 1, √(p + a + 1))` when `p + a + 1` is a
perfect square, provided `p ≠ 3` and `p`, `p + a` are
both odd primes.

Source: Shalini Choudhury and Naba Kanta Sarma, "On the
Diophantine Equations `(p+a)^x + p^y = z^2` and
`(p+a)^x - p^y = z^2` where `p` and `p+a` Are Odd
Primes", Theorem 6. -/
theorem_wanted pow_add_pow_eq_sq (p a x y z : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpa : (p + a).Prime) (ha4 : a % 4 = 0)
    (hap : p ∣ a + 1) (h : p ^ x + (p + a) ^ y = z ^ 2) :
    x = 0 ∧ y = 1 ∧ z ^ 2 = p + a + 1

/-- **Theorem 7**: if `p > 3` and `p + a` are odd primes
with `a ≡ 2 (mod 4)`, `a ≡ -1 (mod p)` and `(a/p) = -1`,
then `p^x + (p + a)^y = z^2` has no solution in positive
integers (`z > 0` is automatic and not assumed; `p + a`
is odd because `a` is even and `p` is odd).

Source: Shalini Choudhury and Naba Kanta Sarma, "On the
Diophantine Equations `(p+a)^x + p^y = z^2` and
`(p+a)^x - p^y = z^2` where `p` and `p+a` Are Odd
Primes", INTEGERS 26 (2026), Article A87, Theorem 7 (`integers-2026-A87-thm-7`). -/
theorem_wanted pow_add_pow_ne_sq_of_legendreSym (p a : ℕ)
    [Fact p.Prime] (hp3 : 3 < p) (hpa : (p + a).Prime)
    (ha4 : a % 4 = 2) (hap : p ∣ a + 1)
    (hleg : legendreSym p a = -1) (x y z : ℕ) (hx : 0 < x)
    (hy : 0 < y) : p ^ x + (p + a) ^ y ≠ z ^ 2

/-- **Theorem 8**: let `p ≡ -1 (mod 4)`, `p ≠ 3`, and
`p + a` be primes with `a ≡ 2 (mod 4)` (so `a > 0`),
`a ≡ ±1 (mod p)` and `(a/p) = -1`. Then the only
solutions of `(p + a)^x - p^y = z^2`, written
`(p + a)^x = p^y + z^2`, in non-negative integers are the
trivial `(0, 0, 0)` and `(1, 0, √(p + a - 1))` when
`p + a - 1` is a perfect square (a negative `z` gives the
same `z^2`); stated as an equivalence (both listed cases
are solutions).

Source: Shalini Choudhury and Naba Kanta Sarma, "On the
Diophantine Equations `(p+a)^x + p^y = z^2` and
`(p+a)^x - p^y = z^2` where `p` and `p+a` Are Odd
Primes", INTEGERS 26 (2026), Article A87, Theorem 8 (`integers-2026-A87-thm-8`). -/
theorem_wanted pow_sub_pow_eq_sq_iff_of_legendreSym (p a : ℕ)
    [Fact p.Prime] (hp4 : p % 4 = 3) (hp3 : p ≠ 3)
    (hpa : (p + a).Prime) (ha4 : a % 4 = 2)
    (hap : a % p = 1 ∨ a % p = p - 1)
    (hleg : legendreSym p a = -1) (x y z : ℕ) :
    (p + a) ^ x = p ^ y + z ^ 2 ↔
      (x = 0 ∧ y = 0 ∧ z = 0) ∨
        (x = 1 ∧ y = 0 ∧ z ^ 2 = p + a - 1)

end MathlibExt.NumberTheory.ExponentialDiophantineWanted
