/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Set.Card
public import MathlibExt.Combinatorics.Enumerative.DoublePerfectPartitions

namespace MetaMathlibExt

@[expose] public section

/-- **Lee's form of double-perfect partitions.** Let $N \ge 4$ and let $\lambda$ be a
double-perfect partition of $N$ of order $1$. Then there are integers $q_1 \ge 2$ and
$q_2 \ge 1$, with $q_2 = 1$ unless $q_1 = 3$, an integer $k \ge 2$ and integers
$q_3, \dots, q_k \ge 1$ such that, with $B = q_1 + 2q_2 - 1$,
$\lambda = (1^{q_1}, 2^{q_2}, B^{q_3}, (B(q_3+1))^{q_4}, \dots,
(B(q_3+1) \cdots (q_{k-1}+1))^{q_k})$ (for $k = 2$ the only parts are $1$ and $2$). That is, the
parts other than $1^{q_1}$ and $2^{q_2}$ are $B$ times the parts of the perfect partition
$(1^{q_3}, (q_3+1)^{q_4}, \dots, ((q_3+1) \cdots (q_{k-1}+1))^{q_k})$ attached to the ordered
factorization $(q_3+1)(q_4+1) \cdots (q_k+1)$.

The hypothesis $N \ge 4$ is needed: $(1^3)$ is a double-perfect partition of $3$ of order $1$
but has no part $2$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Proposition 1 (Lee), display (3) (`integers-2025-A109-prop-1`). -/
public theorem_wanted doublePerfect_form (N : ℕ) (hN : 4 ≤ N) (l : Multiset ℕ)
    (hl : IsDoublePerfectOfOrder 1 N l) :
    ∃ q₁ q₂ : ℕ, ∃ qs : List ℕ, 2 ≤ q₁ ∧ 1 ≤ q₂ ∧ (∀ q ∈ qs, 1 ≤ q) ∧ (q₁ ≠ 3 → q₂ = 1) ∧
      l = Multiset.replicate q₁ 1 + Multiset.replicate q₂ 2 +
        (perfectPartitionOfFactorization (qs.map (· + 1))).map ((q₁ + 2 * q₂ - 1) * ·)

/-- **Lee's count of double-perfect partitions.** Let $f(m)$ be the number of ordered
factorizations of $m$ into factors greater than $1$, with $f(0) = 0$ and $f(1) = 1$. For every
$n \ge 4$, the number $d(n)$ of double-perfect partitions of $n$ of order $1$ is $f(n-1)$ unless
$n \equiv 1 \pmod 4$, in which case $d(n) = f(n-1) - f((n-1)/4)$.

The hypothesis $n \ge 4$ is needed: for $n = 3$ both perfect partitions $(1^3)$ and $(1, 2)$ are
double-perfect of order $1$ while $f(2) = 1$, and for $n = 1$ the partition $(1)$ is
double-perfect of order $1$ while $f(0) = 0$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Theorem 1 (Lee), display (4) (`integers-2025-A109-thm-1`). -/
public theorem_wanted doublePerfect_ncard (n : ℕ) (hn : 4 ≤ n) :
    ({l | IsDoublePerfectOfOrder 1 n l}.ncard : ℤ) =
      if n % 4 = 1 then
        (orderedFactorizationCount (n - 1) : ℤ) - orderedFactorizationCount ((n - 1) / 4)
      else orderedFactorizationCount (n - 1)

/-- **Double-perfect partitions from perfect partitions.** Let $N > 3$. A multiset $\lambda$ of
natural numbers is a double-perfect partition of $N$ of order $1$ if and only if there is a
perfect partition $\beta$ of $N - 2$ such that either $1$ occurs exactly once in $\beta$ and
$\lambda$ is $\beta$ with two more parts equal to $1$, or $2$ is not a part of $\beta$ and
$\lambda$ is $\beta$ with one more part equal to $2$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Proposition 2 (`integers-2025-A109-prop-2`). -/
public theorem_wanted isDoublePerfect_one_iff (N : ℕ) (hN : 3 < N) (l : Multiset ℕ) :
    IsDoublePerfectOfOrder 1 N l ↔ ∃ β, IsPerfectPartition (N - 2) β ∧
      ((β.count 1 = 1 ∧ l = β + {1, 1}) ∨ (2 ∉ β ∧ l = β + {2}))

/-- **Lee's two forms of double-perfect partitions.** For an integer $B$, an integer $k \ge 2$ and
integers $q_3, \dots, q_k \ge 1$, write $T_B(q_3, \dots, q_k)$ for the parts
$B^{q_3}, (B(q_3+1))^{q_4}, \dots, (B(q_3+1) \cdots (q_{k-1}+1))^{q_k}$ (no parts when $k = 2$).
Let $N \ge 4$ and let $\lambda$ be a double-perfect partition of $N$ of order $1$. Then either
$\lambda = (1^3, 2^{q_2}, T_{2(q_2+1)}(q_3, \dots, q_k))$ for some $q_2 > 1$, some $k \ge 2$ and
some $q_3, \dots, q_k \ge 1$, or $\lambda = (1^{q_1}, 2, T_{q_1+1}(q_3, \dots, q_k))$ for some
$q_1 \ge 2$, some $k \ge 2$ and some $q_3, \dots, q_k \ge 1$.

The hypothesis $N \ge 4$ is needed, as for Lee's form of double-perfect partitions: $(1^3)$ is a
double-perfect partition of $3$ of order $1$ of neither form.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Corollary 1 with displays (5), (6) (`integers-2025-A109-cor-1`). -/
public theorem_wanted doublePerfect_lee_forms (N : ℕ) (hN : 4 ≤ N) (l : Multiset ℕ)
    (hl : IsDoublePerfectOfOrder 1 N l) :
    (∃ q₂ : ℕ, ∃ qs : List ℕ, 1 < q₂ ∧ (∀ q ∈ qs, 1 ≤ q) ∧
      l = Multiset.replicate 3 1 + Multiset.replicate q₂ 2 +
        (perfectPartitionOfFactorization (qs.map (· + 1))).map ((2 * (q₂ + 1)) * ·)) ∨
    (∃ q₁ : ℕ, ∃ qs : List ℕ, 2 ≤ q₁ ∧ (∀ q ∈ qs, 1 ≤ q) ∧
      l = Multiset.replicate q₁ 1 + {2} +
        (perfectPartitionOfFactorization (qs.map (· + 1))).map ((q₁ + 1) * ·))

/-- **Shapes of Type-A double-perfect partitions.** Let $r \ge 1$ and $N \ge 2(r+1)$. For a
finite sequence $(a_1, \dots, a_k)$ write
$P(a_1, \dots, a_k) = (1^{a_1-1}, a_1^{a_2-1}, \dots, (a_1\cdots a_{k-1})^{a_k-1})$ for the
partition that MacMahon's bijection attaches to the ordered factorization $a_1 \cdots a_k$,
where $x^e$ denotes $e$ parts equal to $x$, and let $\cup$ join parts with multiplicity. Every
Type-A double-perfect partition $\lambda$ of $N$ of order $r$ has one of two shapes. Either
there are $k \ge 1$ and integers $a_2, \dots, a_k \ge 2$ with $(r+1) a_2 \cdots a_k = N - r$ and
$\lambda = (1^{r+1}) \cup P(r+1, a_2, \dots, a_k) =
(1^{2r+1}, (r+1)^{a_2-1}, ((r+1)a_2)^{a_3-1}, \dots)$; or there are $k \ge 0$ and integers
$a_1, \dots, a_k \ge 2$ with $a_1 \cdots a_k = N - r$, with $a_1 \ne r + 1$ if $k \ge 1$, and
$\lambda = P(a_1, \dots, a_k) \cup (r+1)$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Corollary 2 with displays (14)-(17) (`integers-2025-A109-cor-2`). -/
public theorem_wanted typeADoublePerfect_forms (r N : ℕ) (hr : 1 ≤ r) (hN : 2 * (r + 1) ≤ N)
    (l : Multiset ℕ) (hl : IsTypeADoublePerfect r N l) :
    (∃ as : List ℕ, (∀ a ∈ as, 2 ≤ a) ∧ (r + 1) * as.prod = N - r ∧
      l = Multiset.replicate (r + 1) 1 + perfectPartitionOfFactorization ((r + 1) :: as)) ∨
    (∃ as : List ℕ, (∀ a ∈ as, 2 ≤ a) ∧ as.prod = N - r ∧ as.head? ≠ some (r + 1) ∧
      l = perfectPartitionOfFactorization as + {r + 1})

/-- **Number of Type-A double-perfect partitions.** Let $f(n)$ be the number of ordered
factorizations of $n$ into factors greater than $1$. Let $r \ge 1$ and $N \ge 2(r+1)$, that is,
$1 \le r \le \lfloor (N-2)/2 \rfloor$, and put $M = 2(r+1)$. The number $d_r(N)$ of Type-A
double-perfect partitions of $N$ of order $r$ is
$f(N-r) - f((N-r)/M) - (f(r+1) - 1) f((N-r)/(r+1))$ if $N \equiv r \pmod M$,
$f(N-r) - (f(r+1) - 1) f((N-r)/(r+1))$ if $N \equiv -1 \pmod M$, and $f(N-r)$ otherwise.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Theorem 3, display (18) (`integers-2025-A109-thm-3`). -/
public theorem_wanted typeADoublePerfect_ncard (r N : ℕ) (hr : 1 ≤ r) (hN : 2 * (r + 1) ≤ N) :
    ({l | IsTypeADoublePerfect r N l}.ncard : ℤ) =
      if N % (2 * (r + 1)) = r then
        (orderedFactorizationCount (N - r) : ℤ) -
          orderedFactorizationCount ((N - r) / (2 * (r + 1))) -
          ((orderedFactorizationCount (r + 1) : ℤ) - 1) *
            orderedFactorizationCount ((N - r) / (r + 1))
      else if N % (2 * (r + 1)) = 2 * (r + 1) - 1 then
        (orderedFactorizationCount (N - r) : ℤ) -
          ((orderedFactorizationCount (r + 1) : ℤ) - 1) *
            orderedFactorizationCount ((N - r) / (r + 1))
      else orderedFactorizationCount (N - r)

/-- **Adding equal parts to a Type-A double-perfect partition.** Let $r \ge 1$ and
$n \ge 2(r+1)$ be integers, and let $\lambda$ be a Type-A double-perfect partition of $n$ of
order $r$. Then for every natural number $m$, the partition obtained from $\lambda$ by adding $m$
parts equal to $n - r$ is a Type-A double-perfect partition of $n + m(n - r)$ of order $r$.

The bound $n \ge 2(r+1)$ is needed: for $r = 1$ and $n = 2$, the partition $(1^2)$, obtained
from the empty perfect partition of $0$ by adding two parts $1$, is Type-A double-perfect of
order $1$, but adding $m = 2$ parts equal to $1$ gives $(1^4)$, which is not double-perfect of
order $1$ because it contains only one partition of $2$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Proposition 3 (`integers-2025-A109-prop-3`). -/
public theorem_wanted isTypeADoublePerfect_add_replicate (r n : ℕ) (hr : 1 ≤ r)
    (hn : 2 * (r + 1) ≤ n) (l : Multiset ℕ) (hl : IsTypeADoublePerfect r n l) (m : ℕ) :
    IsTypeADoublePerfect r (n + m * (n - r)) (l + Multiset.replicate m (n - r))

/-- **Adding a copy of the largest part to a double-perfect partition.** Let $r \ge 1$,
$n \ge 2(r+1)$, and let $\lambda$ be a double-perfect partition of $n$ of order $r$ whose largest
part $\ell$ is not $r + 1$. Then $\lambda$ with one more part $\ell$ is a double-perfect partition
of $n + \ell$ of order $r$. The condition $\ell \ne r + 1$ cannot be dropped: $(1^2, 3^4, 6)$ is
a Type-A double-perfect partition of $20$ of order $5$, but $(1^2, 3^4, 6^2)$ is not a
double-perfect partition of $26$ of order $5$.

The hypothesis $n \ge 2(r+1)$ is needed: for $r = 1$, $(1^3)$ is a double-perfect partition of
$3$ of order $1$, but $(1^4)$ is not a double-perfect partition of $4$ of order $1$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Corollary 3 (`integers-2025-A109-cor-3`). -/
public theorem_wanted isDoublePerfectOfOrder_add_largest :
    (∀ (r n : ℕ), 1 ≤ r → 2 * (r + 1) ≤ n → ∀ l : Multiset ℕ, IsDoublePerfectOfOrder r n l →
      l.sup ≠ r + 1 → IsDoublePerfectOfOrder r (n + l.sup) (l + {l.sup})) ∧
    IsTypeADoublePerfect 5 20 {1, 1, 3, 3, 3, 3, 6} ∧
    ¬ IsDoublePerfectOfOrder 5 26 {1, 1, 3, 3, 3, 3, 6, 6}

/-- **Halved perfect partitions are double-perfect but not of Type A.** For integers
$a_1, \dots, a_k \ge 2$ write $P(a_1, \dots, a_k)$ for the perfect partition
$(1^{a_1-1}, a_1^{a_2-1}, (a_1a_2)^{a_3-1}, \dots, (a_1 \cdots a_{k-1})^{a_k-1})$. Let $N$ and
$r \ge 1$ be natural numbers, let $a_1, \dots, a_k \ge 2$ and $1 < j < k$ with
$a_1 \cdots a_j = 2(r+1)$, $a_1 \cdots a_k = 2(N - r)$, $a_j > 2$ and $a_{j+1} > 2$. Let
$\lambda$ consist of the parts of $P(a_1, \dots, a_j)$ together with $r + 1$ times each part of
$P(a_{j+1}, \dots, a_k)$, that is,
$\lambda = (1^{a_1-1}, a_1^{a_2-1}, \dots, (a_1 \cdots a_{j-1})^{a_j-1},
(a_1 \cdots a_j/2)^{a_{j+1}-1}, \dots, (a_1 \cdots a_{k-1}/2)^{a_k-1})$. Then $\lambda$ is a
double-perfect partition of $N$ of order $r$ and is not a Type-A double-perfect partition of $N$
of order $r$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Theorem 5 with conditions (23)-(25) and display (26)
(`integers-2025-A109-thm-5`). -/
public theorem_wanted halvedPerfect_isDoublePerfect_not_typeA (r N : ℕ) (hr : 1 ≤ r)
    (b c : List ℕ) (hb : ∀ a ∈ b, 2 ≤ a) (hc : ∀ a ∈ c, 2 ≤ a) (hblen : 2 ≤ b.length)
    (hc0 : c ≠ []) (hbprod : b.prod = 2 * (r + 1)) (hprod : (b ++ c).prod = 2 * (N - r))
    (hbj : ∀ x ∈ b.getLast?, 2 < x) (hcj : ∀ x ∈ c.head?, 2 < x) :
    IsDoublePerfectOfOrder r N
        (perfectPartitionOfFactorization b +
          (perfectPartitionOfFactorization c).map ((r + 1) * ·)) ∧
      ¬ IsTypeADoublePerfect r N
        (perfectPartitionOfFactorization b +
          (perfectPartitionOfFactorization c).map ((r + 1) * ·))

/-- **Number of Type-B double-perfect partitions.** Let $f(n)$ be the number of ordered
factorizations of $n$ into factors greater than $1$. Let $r \ge 1$ and $N \ge 3r + 4$, that is,
$1 \le r \le \lfloor (N-4)/3 \rfloor$, and put $M = 2(r+1)$ and $c = f(M) - 1 - f(r+1)$. The
number $e_r(N)$ of Type-B double-perfect partitions of $N$ of order $r$, that is, of
double-perfect partitions of $N$ of order $r$ that are not of Type A, is
$c\,(f((N-r)/(r+1)) - f((N-r)/M))$ if $N \equiv r \pmod M$, $c\, f((N-r)/(r+1))$ if
$N \equiv -1 \pmod M$, and $0$ otherwise.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Theorem 6, display (27) (`integers-2025-A109-thm-6`). -/
public theorem_wanted typeBDoublePerfect_ncard (r N : ℕ) (hr : 1 ≤ r) (hN : 3 * r + 4 ≤ N) :
    ({l | IsDoublePerfectOfOrder r N l ∧ ¬ IsTypeADoublePerfect r N l}.ncard : ℤ) =
      if N % (2 * (r + 1)) = r then
        ((orderedFactorizationCount (2 * (r + 1)) : ℤ) - 1 - orderedFactorizationCount (r + 1)) *
          ((orderedFactorizationCount ((N - r) / (r + 1)) : ℤ) -
            orderedFactorizationCount ((N - r) / (2 * (r + 1))))
      else if N % (2 * (r + 1)) = 2 * (r + 1) - 1 then
        ((orderedFactorizationCount (2 * (r + 1)) : ℤ) - 1 - orderedFactorizationCount (r + 1)) *
          orderedFactorizationCount ((N - r) / (r + 1))
      else 0

/-- **Number of double-perfect partitions of higher order.** Let $f(m)$ be the number of ordered
factorizations of $m$ into factors greater than $1$. Let $r \ge 1$ and $N \ge 2(r+1)$
(equivalently $1 \le r \le \lfloor (N-2)/2 \rfloor$), put $M = 2(r+1)$, and let $u_r(N)$ be the
number of double-perfect partitions of $N$ of order $r$. Then $u_r(N)$ equals
$f(N-r) + (f(M) - 2f(r+1)) f((N-r)/(r+1)) - (f(M) - f(r+1)) f((N-r)/M)$ if $N \equiv r \pmod M$,
$f(N-r) + (f(M) - 2f(r+1)) f((N-r)/(r+1))$ if $N \equiv -1 \pmod M$, and $f(N-r)$ otherwise.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Theorem 7, display (28) (`integers-2025-A109-thm-7`). -/
public theorem_wanted doublePerfectOfOrder_ncard (r N : ℕ) (hr : 1 ≤ r)
    (hN : 2 * (r + 1) ≤ N) :
    ({l | IsDoublePerfectOfOrder r N l}.ncard : ℤ) =
      if N % (2 * (r + 1)) = r then
        (orderedFactorizationCount (N - r) : ℤ) +
          ((orderedFactorizationCount (2 * (r + 1)) : ℤ) - 2 * orderedFactorizationCount (r + 1)) *
            orderedFactorizationCount ((N - r) / (r + 1)) -
          ((orderedFactorizationCount (2 * (r + 1)) : ℤ) - orderedFactorizationCount (r + 1)) *
            orderedFactorizationCount ((N - r) / (2 * (r + 1)))
      else if N % (2 * (r + 1)) = 2 * (r + 1) - 1 then
        (orderedFactorizationCount (N - r) : ℤ) +
          ((orderedFactorizationCount (2 * (r + 1)) : ℤ) - 2 * orderedFactorizationCount (r + 1)) *
            orderedFactorizationCount ((N - r) / (r + 1))
      else orderedFactorizationCount (N - r)

end

end MetaMathlibExt
