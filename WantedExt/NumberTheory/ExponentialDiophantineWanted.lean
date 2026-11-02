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
covered in the source audit table. Sanity-checked
numerically: `19^x + 151^y` is never a square (it is
`≡ 2 (mod 3)`), and Theorem 6 has no unexpected small
solutions across its first instances.

Not stated (see the source audit table): Theorems 7
and 8, whose Legendre-symbol hypotheses are garbled in
the extracted statements.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.ExponentialDiophantineWanted

/-- **Solutions of $p^x + (p + a)^y = z^2$ for odd primes $p$ and $p + a$.** Let $p$ be a
prime with $p \ne 2$ and $p \ne 3$, and let $a$ be a natural number such that $p + a$ is
prime, $a \equiv 0 \pmod 4$ and $p$ divides $a + 1$. If natural numbers $x$, $y$ and $z$
satisfy $p^x + (p + a)^y = z^2$, then $x = 0$, $y = 1$ and $z^2 = p + a + 1$.

Source: Shalini Choudhury and Naba Kanta Sarma, "On the
Diophantine Equations `(p+a)^x + p^y = z^2` and
`(p+a)^x - p^y = z^2` where `p` and `p+a` Are Odd
Primes", Theorem 6. -/
theorem_wanted pow_add_pow_eq_sq (p a x y z : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpa : (p + a).Prime) (ha4 : a % 4 = 0)
    (hap : p ∣ a + 1) (h : p ^ x + (p + a) ^ y = z ^ 2) :
    x = 0 ∧ y = 1 ∧ z ^ 2 = p + a + 1

/-- **$19^x + 151^y$ is never a perfect square.** For all natural numbers $x$, $y$ and $z$,
$19^x + 151^y \ne z^2$.

Source: Shalini Choudhury and Naba Kanta Sarma, "On the
Diophantine Equations `(p+a)^x + p^y = z^2` and
`(p+a)^x - p^y = z^2` where `p` and `p+a` Are Odd
Primes", Corollary 1. -/
theorem_wanted pow19_add_pow151_ne_sq (x y z : ℕ) :
    19 ^ x + 151 ^ y ≠ z ^ 2

end MathlibExt.NumberTheory.ExponentialDiophantineWanted
