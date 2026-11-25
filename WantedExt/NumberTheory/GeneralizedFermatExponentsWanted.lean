/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.NormNum

/-!
# Exponents for which `x^m + y^n = z^r` has solutions

Statements from Richard F. Ryan, *Under What Conditions on the Exponents Does
`x^m + y^n = z^r` Have Solutions?*, INTEGERS 24 (2024), Article A48.

Throughout the paper `x`, `y`, `z` are nonzero integers ("solutions" are triples with
`xyz ≠ 0`, primitive or not) and the exponents are integers greater than one.
`GeneralizedFermatSolvable m n r` says that `x^m + y^n = z^r` has such a solution.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Solvable generalized Fermat equation.** For natural numbers $m$, $n$, $r$, the equation
$x^m + y^n = z^r$ is called solvable when there are nonzero integers $x$, $y$, $z$ with
$x^m + y^n = z^r$.

Source: Richard F. Ryan, *Under What Conditions on the Exponents Does `x^m + y^n = z^r` Have
Solutions?*, INTEGERS 24 (2024), Article A48, Section 1, equation (1). -/
def GeneralizedFermatSolvable (m n r : ℕ) : Prop :=
  ∃ x y z : ℤ, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x ^ m + y ^ n = z ^ r

/-- **A solution of x³ + y⁶ = z².** The equation $x^3 + y^6 = z^2$ has a solution in nonzero
integers, namely $2^3 + 1^6 = 3^2$.

Source: Richard F. Ryan, *Under What Conditions on the Exponents Does `x^m + y^n = z^r` Have
Solutions?*, INTEGERS 24 (2024), Article A48, Lemma 1 (the case `s = t = w = 1`). -/
theorem generalizedFermatSolvable_three_six_two : GeneralizedFermatSolvable 3 6 2 :=
  ⟨2, 1, 3, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Swapping the first two exponents of a generalized Fermat equation.** For natural numbers
$m$, $n$, $r$, if $x^m + y^n = z^r$ has a solution in nonzero integers, then so does
$x^n + y^m = z^r$.

Source: Richard F. Ryan, *Under What Conditions on the Exponents Does `x^m + y^n = z^r` Have
Solutions?*, INTEGERS 24 (2024), Article A48, Section 1, equation (1). -/
theorem GeneralizedFermatSolvable.swap {m n r : ℕ} (h : GeneralizedFermatSolvable m n r) :
    GeneralizedFermatSolvable n m r := by
  obtain ⟨x, y, z, hx, hy, hz, h⟩ := h
  exact ⟨y, x, z, hy, hx, hz, by rw [add_comm]; exact h⟩

/-- **Generalized Fermat equations with two non-coprime pairs of exponents.** Let
$m, n, r \ge 2$ be integers with $\gcd(m, n, r) = 1$ such that at least two of $\gcd(m, n)$,
$\gcd(m, r)$ and $\gcd(n, r)$ are greater than $1$. Suppose there are no natural numbers
$s, t, w$ that are pairwise coprime, with $s$ odd and $3 \nmid w$, such that $(m, n, r)$ is one
of $(3s, 6t, 2w)$, $(6t, 3s, 2w)$, $(2w, 3s, 6t)$ and $(3s, 2w, 6t)$. Then the equation
$x^m + y^n = z^r$ has no solution in nonzero integers $x, y, z$.

Positivity of $s, t, w$ is automatic from $m, n, r \ge 2$.

Source: Richard F. Ryan, *Under What Conditions on the Exponents Does `x^m + y^n = z^r` Have
Solutions?*, INTEGERS 24 (2024), Article A48, Theorem 1 (`integers-2024-A48-thm-1`). -/
public theorem_wanted not_generalizedFermatSolvable_of_two_gcd_gt_one {m n r : ℕ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hr : 2 ≤ r) (hgcd : Nat.gcd (Nat.gcd m n) r = 1)
    (htwo : (1 < Nat.gcd m n ∧ 1 < Nat.gcd m r) ∨ (1 < Nat.gcd m n ∧ 1 < Nat.gcd n r) ∨
      (1 < Nat.gcd m r ∧ 1 < Nat.gcd n r))
    (hexc : ¬ ∃ s t w : ℕ, Nat.Coprime s t ∧ Nat.Coprime s w ∧ Nat.Coprime t w ∧ Odd s ∧
      ¬ 3 ∣ w ∧ ((m, n, r) = (3 * s, 6 * t, 2 * w) ∨ (m, n, r) = (6 * t, 3 * s, 2 * w) ∨
        (m, n, r) = (2 * w, 3 * s, 6 * t) ∨ (m, n, r) = (3 * s, 2 * w, 6 * t))) :
    ¬ GeneralizedFermatSolvable m n r

/-- **The Bartolomé–Mihăilescu theorem for prime exponents.** Let $p \le q$ be primes with
$p \ge 5$, and let $x, y, z$ be pairwise coprime nonzero integers. Then $x^p + y^p \ne z^q$.

The source quotes this result from Bartolomé and Mihăilescu, arXiv:2108.08572.

Source: Richard F. Ryan, *Under What Conditions on the Exponents Does `x^m + y^n = z^r` Have
Solutions?*, INTEGERS 24 (2024), Article A48, Corollary 1 (`integers-2024-A48-cor-1`). -/
public theorem_wanted pow_add_pow_ne_pow_of_prime_five_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h5 : 5 ≤ p) (hpq : p ≤ q) {x y z : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z) :
    x ^ p + y ^ p ≠ z ^ q

/-- **Generalized Fermat equations with exponents 3s, 6t and 2w.** Let $s, t, w$ be positive
integers. If $s, t, w$ are pairwise coprime, $s$ is odd and $3 \nmid w$, then the equation
$x^{3s} + y^{6t} = z^{2w}$ has infinitely many solutions $(x, y, z)$ in nonzero integers;
otherwise it has no solution in nonzero integers.

Source: Richard F. Ryan, *Under What Conditions on the Exponents Does `x^m + y^n = z^r` Have
Solutions?*, INTEGERS 24 (2024), Article A48, Lemma 1 (`integers-2024-A48-lem-1`). -/
public theorem_wanted generalizedFermat_three_six_two_mul {s t w : ℕ} (hs : 0 < s) (ht : 0 < t)
    (hw : 0 < w) :
    (Nat.Coprime s t ∧ Nat.Coprime s w ∧ Nat.Coprime t w ∧ Odd s ∧ ¬ 3 ∣ w →
      {xyz : ℤ × ℤ × ℤ | xyz.1 ≠ 0 ∧ xyz.2.1 ≠ 0 ∧ xyz.2.2 ≠ 0 ∧
        xyz.1 ^ (3 * s) + xyz.2.1 ^ (6 * t) = xyz.2.2 ^ (2 * w)}.Infinite) ∧
    (¬ (Nat.Coprime s t ∧ Nat.Coprime s w ∧ Nat.Coprime t w ∧ Odd s ∧ ¬ 3 ∣ w) →
      ¬ GeneralizedFermatSolvable (3 * s) (6 * t) (2 * w))

/-- **Generalized Fermat equations with exponents u, uv and v.** Let $u, v \ge 2$ be integers.
(A) The equation $x^u + y^{uv} = z^v$ has a solution in nonzero integers $x, y, z$ if and only
if it has one with $\gcd(x, y, z) = 1$. (B) If $u$ or $v$ is even, $(u, v) \ne (2, 2)$ and
$(u, v) \ne (3, 2)$, the equation has no solution in nonzero integers. (C) If $3 \mid u$ or
$3 \mid v$, and $(u, v) \ne (3, 2)$, the equation has no solution in nonzero integers.

Source: Richard F. Ryan, *Under What Conditions on the Exponents Does `x^m + y^n = z^r` Have
Solutions?*, INTEGERS 24 (2024), Article A48, Lemma 2 (`integers-2024-A48-lem-2`). -/
public theorem_wanted generalizedFermat_mul_exponent {u v : ℕ} (hu : 2 ≤ u) (hv : 2 ≤ v) :
    (GeneralizedFermatSolvable u (u * v) v ↔
      ∃ x y z : ℤ, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ Nat.gcd (Int.gcd x y) z.natAbs = 1 ∧
        x ^ u + y ^ (u * v) = z ^ v) ∧
    ((Even u ∨ Even v) → (u, v) ≠ (2, 2) → (u, v) ≠ (3, 2) →
      ¬ GeneralizedFermatSolvable u (u * v) v) ∧
    ((3 ∣ u ∨ 3 ∣ v) → (u, v) ≠ (3, 2) → ¬ GeneralizedFermatSolvable u (u * v) v)

end

end MetaMathlibExt
