/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.EllipticCurve.PointCount
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Waterhouse's theorem on Frobenius traces.** Let $p$ be a prime, let $a \ge 1$, and let $F$
be a finite field with $q = p^a$ elements. An integer $\beta$ is the Frobenius trace
$q + 1 - \#E(F)$ of some elliptic curve $E$ over $F$ if and only if $\beta^2 \le 4q$ and one of
the following holds:
1. $\gcd(\beta, p) = 1$;
2. $a$ is even and $\beta = \pm 2p^{a/2}$;
3. $a$ is even, $p \not\equiv 1 \pmod 3$ and $\beta = \pm p^{a/2}$;
4. $a$ is odd, $p = 2$ or $p = 3$, and $\beta = \pm p^{(a+1)/2}$;
5. $a$ is odd, or $a$ is even and $p \not\equiv 1 \pmod 4$, and $\beta = 0$.

The paper states a one-to-one correspondence between $F$-isogeny classes of elliptic curves and
these integers; the statement above describes its image. Injectivity is Tate's isogeny theorem.

Source: Daniel Vallières, *Elliptic Curves over Finite Fields and Ramanujan
Graphs on Two Vertices*, INTEGERS 24 (2024), Article A8, Theorem 6
(`integers-2024-A8-thm-6`). -/
public theorem_wanted exists_isElliptic_frobeniusTrace_eq_iff {F : Type*} [Field F]
    [Finite F] {p a : ℕ} (hp : p.Prime) (ha : 0 < a) (hq : Nat.card F = p ^ a) (β : ℤ) :
    (∃ W : WeierstrassCurve F, W.IsElliptic ∧ W.toAffine.frobeniusTrace = β) ↔
      β ^ 2 ≤ 4 * (p : ℤ) ^ a ∧
        (Int.gcd β p = 1 ∨
          (Even a ∧ (β = 2 * (p : ℤ) ^ (a / 2) ∨ β = -(2 * (p : ℤ) ^ (a / 2)))) ∨
          (Even a ∧ ¬ p ≡ 1 [MOD 3] ∧ (β = (p : ℤ) ^ (a / 2) ∨ β = -(p : ℤ) ^ (a / 2))) ∨
          (Odd a ∧ (p = 2 ∨ p = 3) ∧
            (β = (p : ℤ) ^ ((a + 1) / 2) ∨ β = -(p : ℤ) ^ ((a + 1) / 2))) ∨
          ((Odd a ∨ (Even a ∧ ¬ p ≡ 1 [MOD 4])) ∧ β = 0))

/-- **Ihara's criterion for Ramanujan graphs.** Let $q \ge 2$ be a natural number and let $A$ be a
symmetric $n \times n$ matrix with integer entries. Every complex root $\mu \ne q + 1$ of the
characteristic polynomial of $A$ satisfies $|\mu| \le 2\sqrt{q}$ if and only if, for every such
root $\mu \ne q + 1$, every complex number $s$ with $1 - \mu q^{-s} + q^{1 - 2s} = 0$ has real
part $1/2$.

When $A$ is the adjacency matrix of a $(q + 1)$-regular graph $X$, the left side says that $X$ is
Ramanujan. Writing $\zeta_X$ for the Ihara zeta function of $X$, the numbers $s$ on the right are
the non-trivial zeros of $Q_X(s) = \zeta_X(q^{-s})^{-1}$, that is, the zeros of
$P_X(q^{-s}) = \prod_{\mu \ne q + 1} (1 - \mu q^{-s} + q^{1 - 2s})$. The roots $\mu$ are real
because $A$ is symmetric. The paper also assumes that $X$ is connected and regular and has at
least two vertices; these assumptions are not needed, since the equivalence holds root by root.

Source: Daniel Vallières, *Elliptic Curves over Finite Fields and Ramanujan Graphs on Two
Vertices*, INTEGERS 24 (2024), Article A8, Theorem 2 (`integers-2024-A8-thm-2`). -/
public theorem_wanted ramanujan_iff_nontrivial_zeros_re_eq_half {n q : ℕ} (hq : 2 ≤ q)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.IsSymm) :
    (∀ μ ∈ A.charpoly.aroots ℂ, μ ≠ (q : ℂ) + 1 → ‖μ‖ ≤ 2 * Real.sqrt q) ↔
      ∀ μ ∈ A.charpoly.aroots ℂ, μ ≠ (q : ℂ) + 1 → ∀ s : ℂ,
        1 - μ * (q : ℂ) ^ (-s) + (q : ℂ) ^ (1 - 2 * s) = 0 → s.re = 1 / 2

/-- **Ramanujan graphs give Weil numbers.** Let $q$ be a natural number and let $A$ be a symmetric
$n \times n$ matrix with integer entries such that every complex root $\mu \ne q + 1$ of its
characteristic polynomial satisfies $|\mu| \le 2\sqrt{q}$. Let $\mu \ne q + 1$ be a complex root
of the characteristic polynomial of $A$ and let $\alpha \in \mathbb{C}$ satisfy
$\alpha^2 - \mu\alpha + q = 0$. Then $\alpha$ is an algebraic integer, and every complex root of
the minimal polynomial of $\alpha$ over $\mathbb{Q}$ has absolute value $\sqrt{q}$; that is,
$\alpha$ is a Weil $q$-number.

When $A$ is the adjacency matrix of a $(q + 1)$-regular graph $X$, the hypothesis says that $X$ is
Ramanujan, and the numbers $\alpha$ are the inverse roots of
$P_X(u) = \prod_{\mu \ne q + 1} (1 - \mu u + q u^2)$. The paper takes $q = p^a$ and $X$
connected; neither assumption is needed.

Source: Daniel Vallières, *Elliptic Curves over Finite Fields and Ramanujan Graphs on Two
Vertices*, INTEGERS 24 (2024), Article A8, Proposition 1 (`integers-2024-A8-prop-1`). -/
public theorem_wanted isWeilNumber_of_ramanujan {n q : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.IsSymm)
    (hram : ∀ μ ∈ A.charpoly.aroots ℂ, μ ≠ (q : ℂ) + 1 → ‖μ‖ ≤ 2 * Real.sqrt q)
    {μ α : ℂ} (hμ : μ ∈ A.charpoly.aroots ℂ) (hμq : μ ≠ (q : ℂ) + 1)
    (hα : α ^ 2 - μ * α + q = 0) :
    IsIntegral ℤ α ∧ ∀ β ∈ (minpoly ℚ α).aroots ℂ, ‖β‖ = Real.sqrt q

/-- **Elliptic curves with point count divisible by 4 and Ramanujan graphs on two vertices.** Let
$p$ be an odd prime, let $a \in \{1, 2\}$, and let $F$ be a finite field with $q = p^a$ elements. A
natural number $N$ is the number $\#E(F)$ of $F$-points (counting the point at infinity) of some
elliptic curve $E$ over $F$ with $4 \mid N$ if and only if there are natural numbers $l$ and $m$
with $N = 2m$, $2l + m = q + 1$, $m > 0$ and $(2l - m)^2 \le 4q$.

In graph terms, $X(l, m)$ is the two-vertex graph with $l$ loops at each vertex and $m$ edges
between the two vertices. For such $l$ and $m$ it is $(q + 1)$-regular, it is connected exactly
when $m > 0$, and its non-trivial eigenvalue is $2l - m$, so the last condition says that $X(l, m)$
is Ramanujan. The paper states a bijection from $F$-isogeny classes of such curves to these
graphs; the statement above is its point-count form, and injectivity on isogeny classes is Tate's
theorem.

Source: Daniel Vallières, *Elliptic Curves over Finite Fields and Ramanujan Graphs on Two
Vertices*, INTEGERS 24 (2024), Article A8, Theorem 8 (`integers-2024-A8-thm-8`). -/
public theorem_wanted exists_isElliptic_card_eq_iff_ramanujan_two_vertices {F : Type*} [Field F]
    [Finite F] {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : a = 1 ∨ a = 2)
    (hq : Nat.card F = p ^ a) (N : ℕ) :
    (∃ W : WeierstrassCurve F, W.IsElliptic ∧ Nat.card W.toAffine.Point = N ∧ 4 ∣ N) ↔
      ∃ l m : ℕ, N = 2 * m ∧ 2 * l + m = p ^ a + 1 ∧ 0 < m ∧
        ((2 * l : ℤ) - m) ^ 2 ≤ 4 * (p : ℤ) ^ a

/-- **Ordinary elliptic curves with point count divisible by 4 and Ramanujan graphs on two
vertices.** Let $p$ be an odd prime, let $a \ge 1$, and let $F$ be a finite field with $q = p^a$
elements. A natural number $N$ is the number $\#E(F)$ of $F$-points (counting the point at
infinity) of some elliptic curve $E$ over $F$ with $4 \mid N$ whose Frobenius trace
$q + 1 - \#E(F)$ is coprime to $p$ if and only if there are natural numbers $l$ and $m$ with
$N = 2m$, $2l + m = q + 1$, $m > 0$, $(2l - m)^2 \le 4q$ and $2m \not\equiv 1 \pmod p$.

A Frobenius trace coprime to $p$ is the paper's criterion for $E$ to be ordinary; since $p \mid q$,
the trace $q + 1 - 2m$ is coprime to $p$ exactly when $2m \not\equiv 1 \pmod p$. In graph terms,
$X(l, m)$ is the two-vertex graph with $l$ loops at each vertex and $m$ edges between the two
vertices; it is $(q + 1)$-regular, connected exactly when $m > 0$, and Ramanujan exactly when
$(2l - m)^2 \le 4q$. The paper states a bijection from $F$-isogeny classes of such curves to these
graphs; the statement above is its point-count form, and injectivity on isogeny classes is Tate's
theorem.

Source: Daniel Vallières, *Elliptic Curves over Finite Fields and Ramanujan Graphs on Two
Vertices*, INTEGERS 24 (2024), Article A8, Theorem 9 (`integers-2024-A8-thm-9`). -/
public theorem_wanted exists_ordinary_card_eq_iff_ramanujan_two_vertices {F : Type*} [Field F]
    [Finite F] {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a)
    (hq : Nat.card F = p ^ a) (N : ℕ) :
    (∃ W : WeierstrassCurve F, W.IsElliptic ∧ Int.gcd W.toAffine.frobeniusTrace p = 1 ∧
        Nat.card W.toAffine.Point = N ∧ 4 ∣ N) ↔
      ∃ l m : ℕ, N = 2 * m ∧ 2 * l + m = p ^ a + 1 ∧ 0 < m ∧
        ((2 * l : ℤ) - m) ^ 2 ≤ 4 * (p : ℤ) ^ a ∧ ¬ 2 * m ≡ 1 [MOD p]

end

end MetaMathlibExt
