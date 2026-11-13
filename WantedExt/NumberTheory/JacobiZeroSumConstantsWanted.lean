/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Zero-sum constants related to the Jacobi symbol: wishlist

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7
(arXiv:2111.14477).

Definitions follow the paper. For a weight-set `A ⊆ ℤ_n`, a sequence `(x_1, …, x_k)` in
`ℤ_n` is an `A`-weighted zero-sum sequence if `a_1 x_1 + ⋯ + a_k x_k = 0` for some
`a_i ∈ A`. The weighted Davenport constant `D_A(n)` is the least positive integer `k`
such that every sequence of length `k` in `ℤ_n` has an `A`-weighted zero-sum
(nonempty) subsequence; `C_A(n)` is the same with a subsequence of consecutive terms.
Both are stated with `IsLeast` on the corresponding set (local notation below), so no
new definition is introduced. `U(n)` is the unit group, `U(n)²` its squares,
`S(n) = {x ∈ U(n) : (x/n) = 1}` and `L(n;p) = {x ∈ U(n) : (x/n) = (x/p)}` with the
Jacobi symbol `jacobiSym`; `f_{n,m}` is `ZMod.castHom`. The paper assumes `n` odd from
Section 2 on (the Jacobi symbol is defined for odd `n`); this is a hypothesis wherever
`S(n)` or `L(n;p)` appears and is not already implied. `Ω` is
`ArithmeticFunction.cardFactors`.
-/

open scoped ArithmeticFunction.Omega

namespace MetaMathlibExt

@[expose] public section

set_option quotPrecheck false in
/-- The set of positive `k` such that every length-`k` sequence in `ℤ_n` has an
`A`-weighted zero-sum subsequence; `D_A(n)` is its least element. -/
local notation "davenportSet" n:max A:max => {k : ℕ | 0 < k ∧ ∀ x : Fin k → ZMod n,
  ∃ I : Finset (Fin k), I.Nonempty ∧
    ∃ a : Fin k → ZMod n, (∀ i ∈ I, a i ∈ A) ∧ ∑ i ∈ I, a i * x i = 0}

set_option quotPrecheck false in
/-- The set of positive `k` such that every length-`k` sequence in `ℤ_n` has an
`A`-weighted zero-sum subsequence of consecutive terms; `C_A(n)` is its least element. -/
local notation "consecutiveSet" n:max A:max => {k : ℕ | 0 < k ∧ ∀ x : Fin k → ZMod n,
  ∃ s t : Fin k, s ≤ t ∧
    ∃ a : Fin k → ZMod n, (∀ i ∈ Finset.Icc s t, a i ∈ A) ∧
      ∑ i ∈ Finset.Icc s t, a i * x i = 0}

set_option quotPrecheck false in
/-- `x : Fin k → ZMod n` is an `A`-weighted zero-sum sequence. -/
local notation "IsWeightedZeroSum" n:max k:max A:max x:max =>
  ∃ a : Fin k → ZMod n, (∀ i, a i ∈ A) ∧ ∑ i, a i * x i = 0

set_option quotPrecheck false in
/-- `U(n)`, the units of `ℤ_n`. -/
local notation "unitSet" n:max => {x : ZMod n | IsUnit x}

set_option quotPrecheck false in
/-- `U(n)²`, the squares of units of `ℤ_n`. -/
local notation "unitSqSet" n:max => {x : ZMod n | ∃ y : ZMod n, IsUnit y ∧ y ^ 2 = x}

set_option quotPrecheck false in
/-- `S(n) = {x ∈ U(n) : (x/n) = 1}`. -/
local notation "jacobiOneSet" n:max =>
  {x : ZMod n | IsUnit x ∧ jacobiSym ((x.val : ℕ) : ℤ) n = 1}

set_option quotPrecheck false in
/-- `L(n;p) = {x ∈ U(n) : (x/n) = (x/p)}`. -/
local notation "jacobiEqSet" n:max p:max =>
  {x : ZMod n | IsUnit x ∧ jacobiSym ((x.val : ℕ) : ℤ) n = jacobiSym ((x.val : ℕ) : ℤ) p}

/-- **Unit-weighted zero-sum constants of $\mathbb{Z}_n$.** Let $n$ be a positive integer, let
$U(n)$ be the set of units of $\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$, and let $\Omega(n)$ be the
number of prime factors of $n$ counted with multiplicity. Then $D_{U(n)}(n) = \Omega(n) + 1$ and
$C_{U(n)}(n) = 2^{\Omega(n)}$. Here $D_{U(n)}(n)$ is the least positive integer $k$ such that
every sequence $(x_1, \dots, x_k)$ in $\mathbb{Z}_n$ has a nonempty set $I$ of indices and units
$a_i \in U(n)$ for $i \in I$ with $\sum_{i \in I} a_i x_i = 0$, and $C_{U(n)}(n)$ is defined in
the same way with $I$ restricted to a block $\{s, s+1, \dots, t\}$ of consecutive indices.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Theorem 4
(`jis-2024-24.1.7-thm-4`). -/
public theorem_wanted unit_weighted_zero_sum_constants (n : ℕ) (hn : 0 < n) :
    IsLeast (davenportSet n (unitSet n)) (Ω n + 1) ∧
      IsLeast (consecutiveSet n (unitSet n)) (2 ^ Ω n)

/-- **Quadratic-residue-weighted zero-sum constants modulo a prime.** Let $p$ be an odd prime and
let $Q_p$ be the set of squares of units of $\mathbb{Z}_p = \mathbb{Z}/p\mathbb{Z}$. Then
$C_{Q_p}(p) = D_{Q_p}(p) = 3$. Here $D_{Q_p}(p)$ is the least positive integer $k$ such that every
sequence $(x_1, \dots, x_k)$ in $\mathbb{Z}_p$ has a nonempty set $I$ of indices and weights
$a_i \in Q_p$ for $i \in I$ with $\sum_{i \in I} a_i x_i = 0$, and $C_{Q_p}(p)$ is defined in the
same way with $I$ restricted to a block $\{s, s+1, \dots, t\}$ of consecutive indices.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Theorem 5
(`jis-2024-24.1.7-thm-5`). -/
public theorem_wanted quadratic_residue_weighted_zero_sum_constants (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    IsLeast (consecutiveSet p (unitSqSet p)) 3 ∧ IsLeast (davenportSet p (unitSqSet p)) 3

/-- **Product lower bound for the consecutive weighted zero-sum constant.** For a natural number
$n$ and $A \subseteq \mathbb{Z}/n\mathbb{Z}$, let $C_A(n)$ denote the least positive integer $k$
such that every sequence $(x_1, \dots, x_k)$ in $\mathbb{Z}/n\mathbb{Z}$ has a block of
consecutive terms $x_s, \dots, x_t$ with $s \le t$ and weights $a_s, \dots, a_t \in A$ such that
$a_s x_s + \dots + a_t x_t = 0$. Let $m$ and $q$ be natural numbers and let
$A \subseteq \mathbb{Z}/mq\mathbb{Z}$, $B \subseteq \mathbb{Z}/m\mathbb{Z}$ and
$C \subseteq \mathbb{Z}/q\mathbb{Z}$ be such that the reduction map
$\mathbb{Z}/mq\mathbb{Z} \to \mathbb{Z}/m\mathbb{Z}$ sends $A$ into $B$ and the reduction map
$\mathbb{Z}/mq\mathbb{Z} \to \mathbb{Z}/q\mathbb{Z}$ sends $A$ into $C$. If $C_A(mq)$, $C_B(m)$
and $C_C(q)$ exist, then $C_A(mq) \ge C_B(m)\,C_C(q)$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 8
(`jis-2024-24.1.7-lem-8`). -/
public theorem_wanted consecutive_constant_mul_le (m q : ℕ) (A : Set (ZMod (m * q)))
    (B : Set (ZMod m)) (C : Set (ZMod q))
    (hB : ZMod.castHom (dvd_mul_right m q) (ZMod m) '' A ⊆ B)
    (hC : ZMod.castHom (dvd_mul_left q m) (ZMod q) '' A ⊆ C) (cA cB cC : ℕ)
    (hA : IsLeast (consecutiveSet (m * q) A) cA) (hBc : IsLeast (consecutiveSet m B) cB)
    (hCc : IsLeast (consecutiveSet q C) cC) :
    cB * cC ≤ cA

/-- **Lower bound for the weighted Davenport constant of a product modulus.** For a natural
number $n$ and $A \subseteq \mathbb{Z}/n\mathbb{Z}$, let $D_A(n)$ denote the least positive
integer $k$ such that every sequence $(x_1, \dots, x_k)$ in $\mathbb{Z}/n\mathbb{Z}$ has a
nonempty set $J$ of indices and weights $a_i \in A$ for $i \in J$ with
$\sum_{i \in J} a_i x_i = 0$. Let $m$ and $q$ be natural numbers and let
$A \subseteq \mathbb{Z}/mq\mathbb{Z}$, $B \subseteq \mathbb{Z}/m\mathbb{Z}$ and
$C \subseteq \mathbb{Z}/q\mathbb{Z}$ be such that the reduction map
$\mathbb{Z}/mq\mathbb{Z} \to \mathbb{Z}/m\mathbb{Z}$ sends $A$ into $B$ and the reduction map
$\mathbb{Z}/mq\mathbb{Z} \to \mathbb{Z}/q\mathbb{Z}$ sends $A$ into $C$. If $D_A(mq)$, $D_B(m)$
and $D_C(q)$ exist, then $D_A(mq) \ge D_B(m) + D_C(q) - 1$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 9
(`jis-2024-24.1.7-lem-9`). -/
public theorem_wanted davenport_constant_add_le (m q : ℕ) (A : Set (ZMod (m * q)))
    (B : Set (ZMod m)) (C : Set (ZMod q))
    (hB : ZMod.castHom (dvd_mul_right m q) (ZMod m) '' A ⊆ B)
    (hC : ZMod.castHom (dvd_mul_left q m) (ZMod q) '' A ⊆ C) (dA dB dC : ℕ)
    (hA : IsLeast (davenportSet (m * q) A) dA) (hBd : IsLeast (davenportSet m B) dB)
    (hCd : IsLeast (davenportSet q C) dC) :
    dB + dC - 1 ≤ dA

/-- **The index of the Jacobi symbol kernel.** Let $n$ be an odd natural number, let $U(n)$
be the group of units of $\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$, and let
$S(n) = \{u \in U(n) : (u/n) = 1\}$, where $(u/n)$ is the Jacobi symbol $(a/n)$ of the
representative $0 \le a < n$ of $u$. If $n$ is not a perfect square, then $S(n)$ is a subgroup of
$U(n)$ of index $2$. If $n$ is a perfect square, then $S(n) = U(n)$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7,
Proposition 11 (`jis-2024-24.1.7-prop-11`). -/
public theorem_wanted jacobi_kernel_index_two (n : ℕ) (hn : Odd n) :
    (¬ IsSquare n → ∃ H : Subgroup (ZMod n)ˣ,
      (∀ u : (ZMod n)ˣ, u ∈ H ↔ jacobiSym (((u : ZMod n).val : ℕ) : ℤ) n = 1) ∧
        H.index = 2) ∧
    (IsSquare n → ∀ u : (ZMod n)ˣ, jacobiSym (((u : ZMod n).val : ℕ) : ℤ) n = 1)

/-- **Units lift to the kernel of the Jacobi symbol across a non-square coprime factor.** Let $d$
and $n'$ be coprime natural numbers such that $d n'$ is odd and $d$ is not a perfect square, and
put $n = d n'$. Then every unit $y$ of $\mathbb{Z}/n'\mathbb{Z}$ is the reduction modulo $n'$ of a
unit $x$ of $\mathbb{Z}/n\mathbb{Z}$ whose least nonnegative representative $v$ has Jacobi symbol
$\left(\frac{v}{n}\right) = 1$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 14
(`jis-2024-24.1.7-lem-14`). -/
public theorem_wanted units_subset_image_jacobi_kernel (d n' : ℕ) (hn : Odd (d * n'))
    (hd : ¬ IsSquare d) (hcop : Nat.Coprime d n') (y : ZMod n') (hy : IsUnit y) :
    ∃ x ∈ jacobiOneSet (d * n'), ZMod.castHom (dvd_mul_left n' d) (ZMod n') x = y

/-- **Lifting weighted zero sums along a coprime factor.** Let $d$ and $n'$ be coprime natural
numbers, put $n = d n'$, and let $f : \mathbb{Z}/n\mathbb{Z} \to \mathbb{Z}/n'\mathbb{Z}$ be
reduction modulo $n'$. Let $A \subseteq \mathbb{Z}/n\mathbb{Z}$ and
$A' \subseteq \mathbb{Z}/n'\mathbb{Z}$ with $A' \subseteq f(A)$, and let
$x_1, \dots, x_k \in \mathbb{Z}/n\mathbb{Z}$ each be divisible by $d$ in $\mathbb{Z}/n\mathbb{Z}$.
If there are $a'_1, \dots, a'_k \in A'$ with $a'_1 f(x_1) + \dots + a'_k f(x_k) = 0$, then there
are $a_1, \dots, a_k \in A$ with $a_1 x_1 + \dots + a_k x_k = 0$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 15
(`jis-2024-24.1.7-lem-15`). -/
public theorem_wanted weighted_zero_sum_of_image (d n' k : ℕ) (hcop : Nat.Coprime d n')
    (x : Fin k → ZMod (d * n')) (hx : ∀ i, (d : ZMod (d * n')) ∣ x i)
    (A : Set (ZMod (d * n'))) (A' : Set (ZMod n'))
    (hA : A' ⊆ ZMod.castHom (dvd_mul_left n' d) (ZMod n') '' A)
    (h : IsWeightedZeroSum n' k A' (fun i => ZMod.castHom (dvd_mul_left n' d) (ZMod n') (x i))) :
    IsWeightedZeroSum (d * n') k A x

/-- **Unit-weighted zero sums modulo an odd prime power.** Let $p$ be an odd prime, let $r$ and
$k$ be natural numbers, and let $x_1, \dots, x_k \in \mathbb{Z}/p^r\mathbb{Z}$. Suppose that for
at least two indices $i$ the least nonnegative representative of $x_i$ is coprime to $p$. Then
there are units $a_1, \dots, a_k$ of $\mathbb{Z}/p^r\mathbb{Z}$ with
$a_1 x_1 + \dots + a_k x_k = 0$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 16
(`jis-2024-24.1.7-lem-16`). -/
public theorem_wanted unit_weighted_zero_sum_prime_power (p r k : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (x : Fin k → ZMod (p ^ r))
    (h : 2 ≤ (Finset.univ.filter fun i => Nat.Coprime (x i).val p).card) :
    IsWeightedZeroSum (p ^ r) k (unitSet (p ^ r)) x

/-- **Three-term sums of square-weighted units cover $\mathbb{Z}_{p^r}$.** Let $p \ge 7$ be a
prime, $r$ a natural number and $n = p^r$; write $\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$ and
$A = U(n)^2$ for the set of squares of units of $\mathbb{Z}_n$. For all units $x_1, x_2, x_3$ of
$\mathbb{Z}_n$, $A x_1 + A x_2 + A x_3 = \mathbb{Z}_n$: every $z \in \mathbb{Z}_n$ equals
$a_1 x_1 + a_2 x_2 + a_3 x_3$ for some $a_1, a_2, a_3 \in A$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 17
(`jis-2024-24.1.7-lem-17`). -/
public theorem_wanted unit_square_three_sumset_eq_univ (p r : ℕ) (hp : p.Prime) (h7 : 7 ≤ p)
    (x : Fin 3 → ZMod (p ^ r)) (hx : ∀ i, IsUnit (x i)) (z : ZMod (p ^ r)) :
    ∃ a : Fin 3 → ZMod (p ^ r), (∀ i, a i ∈ unitSqSet (p ^ r)) ∧ ∑ i, a i * x i = z

/-- **Three-term sums with prescribed square classes cover $\mathbb{Z}_{p^r}$.** Let $p \ge 7$ be
a prime, $r \ge 1$ and $n = p^r$; write $\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$, $U(n)$ for its
group of units, $A_1 = U(n)^2$ for the set of squares of units and $A_2 = U(n) \setminus U(n)^2$.
For all units $x_1, x_2, x_3$ of $\mathbb{Z}_n$ and every $f : \{1, 2, 3\} \to \{1, 2\}$,
$A_{f(1)} x_1 + A_{f(2)} x_2 + A_{f(3)} x_3 = \mathbb{Z}_n$: every $z \in \mathbb{Z}_n$ equals
$a_1 x_1 + a_2 x_2 + a_3 x_3$ for some $a_1 \in A_{f(1)}$, $a_2 \in A_{f(2)}$, $a_3 \in A_{f(3)}$.

The hypothesis $r \ge 1$ is needed: for $r = 0$, $\mathbb{Z}_1 = \{0\}$ has $0 = 0^2$ as its only
unit, so $A_2$ is empty.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 18
(`jis-2024-24.1.7-lem-18`). -/
public theorem_wanted unit_square_class_three_sumset_eq_univ (p r : ℕ) (hp : p.Prime)
    (h7 : 7 ≤ p) (hr : 0 < r) (x : Fin 3 → ZMod (p ^ r)) (hx : ∀ i, IsUnit (x i))
    (f : Fin 3 → Bool) (z : ZMod (p ^ r)) :
    ∃ a : Fin 3 → ZMod (p ^ r),
      (∀ i, IsUnit (a i) ∧ (a i ∈ unitSqSet (p ^ r) ↔ f i = true)) ∧ ∑ i, a i * x i = z

open Classical in
/-- **Three unit terms force a square-weighted zero sum modulo $p^r$.** Let $p \ge 7$ be a prime,
$r$ a natural number and $n = p^r$, and let $U(n)^2$ be the set of squares of units of
$\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$. If a sequence $(x_1, \dots, x_k)$ in $\mathbb{Z}_n$ has
at least three indices $i$ with $x_i$ a unit, then there are $a_1, \dots, a_k \in U(n)^2$ with
$a_1 x_1 + \dots + a_k x_k = 0$, that is, the sequence is a $U(n)^2$-weighted zero-sum sequence.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7,
Corollary 19 (`jis-2024-24.1.7-cor-19`). -/
public theorem_wanted unit_square_weighted_zero_sum_prime_power (p r k : ℕ) (hp : p.Prime)
    (h7 : 7 ≤ p) (x : Fin k → ZMod (p ^ r))
    (h : 3 ≤ (Finset.univ.filter fun i => IsUnit (x i)).card) :
    IsWeightedZeroSum (p ^ r) k (unitSqSet (p ^ r)) x

open Classical in
/-- **Few unit terms force a Jacobi-weighted zero sum.** Let $n$ be an odd squarefree natural
number, $\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$, and $S(n)$ the set of units $u$ of $\mathbb{Z}_n$
whose Jacobi symbol $(a/n)$ is $1$, where $0 \le a < n$ is the representative of $u$. Let
$(x_1, \dots, x_k)$ be a sequence in $\mathbb{Z}_n$, and call $x_i$ coprime to a prime $p$ when its
representative in $\{0, \dots, n-1\}$ is. Suppose that for every prime divisor $p$ of $n$ at least
two indices $i$ have $x_i$ coprime to $p$, and that at most one index $i$ has $x_i$ a unit. Then
there are $a_1, \dots, a_k \in S(n)$ with $a_1 x_1 + \dots + a_k x_k = 0$, that is, the sequence
is an $S(n)$-weighted zero-sum sequence.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 21
(`jis-2024-24.1.7-lem-21`). -/
public theorem_wanted jacobi_weighted_zero_sum_of_few_units (n k : ℕ) (hn : Odd n)
    (hsf : Squarefree n) (x : Fin k → ZMod n)
    (h2 : ∀ p ∈ n.primeFactors, 2 ≤ (Finset.univ.filter fun i => Nat.Coprime (x i).val p).card)
    (h1 : (Finset.univ.filter fun i => IsUnit (x i)).card ≤ 1) :
    IsWeightedZeroSum n k (jacobiOneSet n) x

/-- **Three terms coprime to one prime force a Jacobi-weighted zero sum.** Let $n$ be a squarefree
natural number all of whose prime divisors are at least $7$, let
$\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$, and let $S(n)$ be the set of units $u$ of $\mathbb{Z}_n$
whose Jacobi symbol $(a/n)$ is $1$, where $0 \le a < n$ is the representative of $u$. Let
$(x_1, \dots, x_k)$ be a sequence in $\mathbb{Z}_n$, and call $x_i$ coprime to a prime $p$ when its
representative in $\{0, \dots, n-1\}$ is. Suppose that for every prime divisor $p$ of $n$ at least
two indices $i$ have $x_i$ coprime to $p$, and that for some prime divisor $p$ of $n$ at least
three indices $i$ have $x_i$ coprime to $p$. Then there are $a_1, \dots, a_k \in S(n)$ with
$a_1 x_1 + \dots + a_k x_k = 0$, that is, the sequence is an $S(n)$-weighted zero-sum sequence.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 22
(`jis-2024-24.1.7-lem-22`). -/
public theorem_wanted jacobi_weighted_zero_sum_of_three_coprime (n k : ℕ) (hsf : Squarefree n)
    (h7 : ∀ p ∈ n.primeFactors, 7 ≤ p) (x : Fin k → ZMod n)
    (h2 : ∀ p ∈ n.primeFactors, 2 ≤ (Finset.univ.filter fun i => Nat.Coprime (x i).val p).card)
    (h3 : ∃ p ∈ n.primeFactors, 3 ≤ (Finset.univ.filter fun i => Nat.Coprime (x i).val p).card) :
    IsWeightedZeroSum n k (jacobiOneSet n) x

/-- **Davenport constant for the weights of Jacobi symbol one.** For a
natural number $n$ and $A \subseteq \mathbb{Z}/n\mathbb{Z}$, let $D_A(n)$ denote the least positive
integer $k$ such that every sequence $(x_1, \dots, x_k)$ in $\mathbb{Z}/n\mathbb{Z}$ has a
nonempty set $J$ of indices and weights $a_i \in A$ for $i \in J$ with
$\sum_{i \in J} a_i x_i = 0$. Let $n$ be an odd squarefree natural number and let
$S(n)$ be the set of units $x$ of $\mathbb{Z}/n\mathbb{Z}$ with Jacobi symbol
$\left(\frac{x}{n}\right) = 1$. If $n$ is prime, then $D_{S(n)}(n) = 3$. If $n$ is not prime and
every prime divisor of $n$ is at least $7$, then $D_{S(n)}(n) = \Omega(n) + 1$, where $\Omega(n)$ is
the number of prime factors of $n$ counted with multiplicity.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Theorem 23
(`jis-2024-24.1.7-thm-23`). -/
public theorem_wanted jacobi_davenport_constant (n : ℕ) (hn : Odd n) (hsf : Squarefree n) :
    (n.Prime → IsLeast (davenportSet n (jacobiOneSet n)) 3) ∧
    (¬ n.Prime → (∀ p ∈ n.primeFactors, 7 ≤ p) →
      IsLeast (davenportSet n (jacobiOneSet n)) (Ω n + 1))

/-- **Consecutive constant for the weights of Jacobi symbol one.** For a
natural number $n$ and $A \subseteq \mathbb{Z}/n\mathbb{Z}$, let $C_A(n)$ denote the least positive
integer $k$ such that every sequence $(x_1, \dots, x_k)$ in $\mathbb{Z}/n\mathbb{Z}$ has a block of
consecutive terms $x_s, \dots, x_t$ with $s \le t$ and weights $a_s, \dots, a_t \in A$ such that
$a_s x_s + \dots + a_t x_t = 0$. Let $n$ be an odd squarefree natural number and let
$S(n)$ be the set of units $x$ of $\mathbb{Z}/n\mathbb{Z}$ with Jacobi symbol
$\left(\frac{x}{n}\right) = 1$. If $n$ is prime, then $C_{S(n)}(n) = 3$. If $n$ is not prime and
every prime divisor of $n$ is at least $7$, then $C_{S(n)}(n) = 2^{\Omega(n)}$, where $\Omega(n)$ is
the number of prime factors of $n$ counted with multiplicity.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Theorem 24
(`jis-2024-24.1.7-thm-24`). -/
public theorem_wanted jacobi_consecutive_constant (n : ℕ) (hn : Odd n) (hsf : Squarefree n) :
    (n.Prime → IsLeast (consecutiveSet n (jacobiOneSet n)) 3) ∧
    (¬ n.Prime → (∀ p ∈ n.primeFactors, 7 ≤ p) →
      IsLeast (consecutiveSet n (jacobiOneSet n)) (2 ^ Ω n))

/-- **Units with equal Jacobi and Legendre symbols form a subgroup of index two.** Let $n$ be an
odd natural number and $p$ a prime divisor of $n$, and suppose that $p$ is not the unique prime
divisor of $n$ with odd exponent in $n$; that is, it is not the case that the exponent of $p$ in
$n$ is odd and every prime divisor of $n$ with odd exponent in $n$ equals $p$. Then the set of
units $u$ of $\mathbb{Z}/n\mathbb{Z}$ whose Jacobi symbol $\left(\frac{u}{n}\right)$ equals the
Legendre symbol $\left(\frac{u}{p}\right)$ is a subgroup of index two in the unit group of
$\mathbb{Z}/n\mathbb{Z}$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7,
Proposition 26 (`jis-2024-24.1.7-prop-26`). -/
public theorem_wanted jacobi_eq_legendre_index_two (n p : ℕ) (hn : Odd n) (hp : p.Prime)
    (hpn : p ∣ n)
    (hnot : ¬ (Odd (n.factorization p) ∧
      ∀ q ∈ n.primeFactors, Odd (n.factorization q) → q = p)) :
    ∃ H : Subgroup (ZMod n)ˣ,
      (∀ u : (ZMod n)ˣ, u ∈ H ↔
        jacobiSym (((u : ZMod n).val : ℕ) : ℤ) n = jacobiSym (((u : ZMod n).val : ℕ) : ℤ) p) ∧
      H.index = 2

/-- **Lifting the Jacobi kernel into the Jacobi agreement set.** Let $n$ be an odd natural number
and let $p$, $p'$ be prime divisors of $n$ with $p$ coprime to $n' = n/p$. For a residue $x$ modulo
$N$ and an odd $m$, write $(x/m)$ for the Jacobi symbol $(a/m)$ of the representative
$0 \le a < N$ of $x$. Let $U(m)$ be the group of units of $\mathbb{Z}_m = \mathbb{Z}/m\mathbb{Z}$,
let $S(n') = \{y \in U(n') : (y/n') = 1\}$ and $L(n;p') = \{x \in U(n) : (x/n) = (x/p')\}$, and
let $f_{n,n'} : \mathbb{Z}_n \to \mathbb{Z}_{n'}$ be reduction modulo $n'$. Then
$S(n') \subseteq f_{n,n'}(L(n;p'))$: every $y \in S(n')$ equals $f_{n,n'}(x)$ for some
$x \in L(n;p')$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 28
(`jis-2024-24.1.7-lem-28`). -/
public theorem_wanted jacobi_kernel_subset_image_jacobi_eq_legendre (n p p' : ℕ) (hn : Odd n)
    (hp : p.Prime) (hp' : p'.Prime) (hpn : p ∣ n) (hp'n : p' ∣ n)
    (hcop : Nat.Coprime p (n / p)) (y : ZMod (n / p)) (hy : y ∈ jacobiOneSet (n / p)) :
    ∃ x ∈ jacobiEqSet n p', ZMod.castHom (Nat.div_dvd_of_dvd hpn) (ZMod (n / p)) x = y

/-- **Units modulo a prime divisor lift to units where the Jacobi and Legendre symbols agree.**
Let $n$ be odd and let $p'$ be a prime dividing $n$ such that $p'$ is coprime to $n/p'$. Write
$L(n;p')$ for the set of units $x$ of $\mathbb{Z}/n\mathbb{Z}$ whose least nonnegative
representative $v$ satisfies $\left(\frac{v}{n}\right) = \left(\frac{v}{p'}\right)$, where both
are Jacobi symbols. Then every unit $z$ of $\mathbb{Z}/p'\mathbb{Z}$ is the reduction modulo $p'$
of some element of $L(n;p')$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 29
(`jis-2024-24.1.7-lem-29`). -/
public theorem_wanted units_prime_subset_image_jacobi_eq_legendre (n p' : ℕ) (hn : Odd n)
    (hp' : p'.Prime) (hp'n : p' ∣ n) (hcop : Nat.Coprime p' (n / p')) (z : ZMod p')
    (hz : IsUnit z) :
    ∃ x ∈ jacobiEqSet n p', ZMod.castHom hp'n (ZMod p') x = z

/-- **Chinese remainder lifts into the Jacobi agreement set.** Let $n$ be an odd squarefree natural
number, $p'$ a prime divisor of $n$ and $n' = n/p'$. For a residue $x$ modulo $N$ and an odd $m$,
write $(x/m)$ for the Jacobi symbol $(a/m)$ of the representative $0 \le a < N$ of $x$. Let $U(m)$
be the group of units of $\mathbb{Z}_m = \mathbb{Z}/m\mathbb{Z}$, let
$S(n') = \{y \in U(n') : (y/n') = 1\}$ and $L(n;p') = \{x \in U(n) : (x/n) = (x/p')\}$, and for
$m \mid n$ let $f_{n,m} : \mathbb{Z}_n \to \mathbb{Z}_m$ be reduction modulo $m$. Then for every
$y \in S(n')$ and every $z \in U(p')$ there is $x \in L(n;p')$ with $f_{n,n'}(x) = y$ and
$f_{n,p'}(x) = z$. That is, the Chinese remainder isomorphism
$\psi = (f_{n,n'}, f_{n,p'}) : U(n) \to U(n') \times U(p')$ satisfies
$S(n') \times U(p') \subseteq \psi(L(n;p'))$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 31
(`jis-2024-24.1.7-lem-31`). -/
public theorem_wanted jacobi_kernel_prod_units_subset_crt_image (n p' : ℕ) (hn : Odd n)
    (hsf : Squarefree n) (hp' : p'.Prime) (hp'n : p' ∣ n) (y : ZMod (n / p'))
    (hy : y ∈ jacobiOneSet (n / p')) (z : ZMod p') (hz : IsUnit z) :
    ∃ x ∈ jacobiEqSet n p', ZMod.castHom (Nat.div_dvd_of_dvd hp'n) (ZMod (n / p')) x = y ∧
      ZMod.castHom hp'n (ZMod p') x = z

open Classical in
/-- **Weighted zero-sum criterion for the Jacobi–Legendre weights.** Let $n$ be a squarefree
natural number all of whose prime divisors are at least $7$, let $p'$ be a prime divisor of $n$,
let $n' = n/p'$, and let $L(n;p')$ be the set of units $x$ of $\mathbb{Z}/n\mathbb{Z}$ whose Jacobi
symbol $\left(\frac{x}{n}\right)$ equals the Legendre symbol $\left(\frac{x}{p'}\right)$. Let
$(x_1, \dots, x_k)$ be a sequence in $\mathbb{Z}/n\mathbb{Z}$ such that for every prime divisor
$p$ of $n$ at least two terms $x_i$ are not divisible by $p$. Suppose that at most one term $x_i$
maps to a unit under the reduction map $\mathbb{Z}/n\mathbb{Z} \to \mathbb{Z}/n'\mathbb{Z}$, or
that for some prime divisor $p$ of $n'$ at least three terms $x_i$ are not divisible by $p$. Then
there are weights $a_1, \dots, a_k \in L(n;p')$ with $a_1 x_1 + \dots + a_k x_k = 0$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 32
(`jis-2024-24.1.7-lem-32`). -/
public theorem_wanted jacobi_eq_legendre_weighted_zero_sum (n p' k : ℕ) (hsf : Squarefree n)
    (h7 : ∀ p ∈ n.primeFactors, 7 ≤ p) (hp' : p' ∈ n.primeFactors) (x : Fin k → ZMod n)
    (h2 : ∀ p ∈ n.primeFactors, 2 ≤ (Finset.univ.filter fun i => Nat.Coprime (x i).val p).card)
    (hcase : (Finset.univ.filter fun i =>
        IsUnit (ZMod.castHom (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp'))
          (ZMod (n / p')) (x i))).card ≤ 1 ∨
      ∃ p ∈ (n / p').primeFactors,
        3 ≤ (Finset.univ.filter fun i => Nat.Coprime (x i).val p).card) :
    IsWeightedZeroSum n k (jacobiEqSet n p') x

/-- **Davenport constant of the Jacobi–Legendre weights.** For a
natural number $n$ and $A \subseteq \mathbb{Z}/n\mathbb{Z}$, let $D_A(n)$ denote the least positive
integer $k$ such that every sequence $(x_1, \dots, x_k)$ in $\mathbb{Z}/n\mathbb{Z}$ has a
nonempty set $J$ of indices and weights $a_i \in A$ for $i \in J$ with
$\sum_{i \in J} a_i x_i = 0$. Let $n$ be a squarefree natural number all of whose prime divisors are
at least $7$, with $\Omega(n) \ne 2$, where $\Omega(n)$ is the number of prime factors of $n$
counted with multiplicity. Let $p'$ be a prime divisor of $n$ and let $L(n;p')$ be the set of units
$x$ of $\mathbb{Z}/n\mathbb{Z}$ whose Jacobi symbol $\left(\frac{x}{n}\right)$ equals the Legendre
symbol $\left(\frac{x}{p'}\right)$. Then $D_{L(n;p')}(n) = \Omega(n) + 1$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Theorem 33
(`jis-2024-24.1.7-thm-33`). -/
public theorem_wanted jacobi_eq_legendre_davenport_constant (n p' : ℕ) (hsf : Squarefree n)
    (h7 : ∀ p ∈ n.primeFactors, 7 ≤ p) (hΩ : Ω n ≠ 2) (hp' : p' ∈ n.primeFactors) :
    IsLeast (davenportSet n (jacobiEqSet n p')) (Ω n + 1)

/-- **Davenport constant of the Jacobi–Legendre weights modulo a product of two primes.** For a
natural number $n$ and $A \subseteq \mathbb{Z}/n\mathbb{Z}$, let $D_A(n)$ denote the least positive
integer $k$ such that every sequence $(x_1, \dots, x_k)$ in $\mathbb{Z}/n\mathbb{Z}$ has a
nonempty set $J$ of indices and weights $a_i \in A$ for $i \in J$ with
$\sum_{i \in J} a_i x_i = 0$. Let $p'$ and $q$ be distinct primes with $p' \ge 7$ and $q \ge 7$, let
$n = p'q$, and let $L(n;p')$ be the set of units $x$ of $\mathbb{Z}/n\mathbb{Z}$ whose Jacobi symbol
$\left(\frac{x}{n}\right)$ equals the Legendre symbol $\left(\frac{x}{p'}\right)$. Then
$D_{L(n;p')}(n) = 4$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Theorem 34
(`jis-2024-24.1.7-thm-34`). -/
public theorem_wanted jacobi_eq_legendre_davenport_constant_two_primes (p' q : ℕ)
    (hp' : p'.Prime) (hq : q.Prime) (hne : p' ≠ q) (h7p : 7 ≤ p') (h7q : 7 ≤ q) :
    IsLeast (davenportSet (p' * q) (jacobiEqSet (p' * q) p')) 4

/-- **Consecutive constant of the Jacobi–Legendre weights.** For a
natural number $n$ and $A \subseteq \mathbb{Z}/n\mathbb{Z}$, let $C_A(n)$ denote the least positive
integer $k$ such that every sequence $(x_1, \dots, x_k)$ in $\mathbb{Z}/n\mathbb{Z}$ has a block of
consecutive terms $x_s, \dots, x_t$ with $s \le t$ and weights $a_s, \dots, a_t \in A$ such that
$a_s x_s + \dots + a_t x_t = 0$. Let $n$ be a squarefree natural number all of whose prime
divisors are at least $7$, with $\Omega(n) \ne 2$, where $\Omega(n)$ is the number of prime factors
of $n$ counted with multiplicity. Let $p'$ be a prime divisor of $n$ and let $L(n;p')$ be the
set of units $x$ of $\mathbb{Z}/n\mathbb{Z}$ whose Jacobi symbol $\left(\frac{x}{n}\right)$ equals
the Legendre symbol $\left(\frac{x}{p'}\right)$. Then $C_{L(n;p')}(n) = 2^{\Omega(n)}$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Theorem 35
(`jis-2024-24.1.7-thm-35`). -/
public theorem_wanted jacobi_eq_legendre_consecutive_constant (n p' : ℕ) (hsf : Squarefree n)
    (h7 : ∀ p ∈ n.primeFactors, 7 ≤ p) (hΩ : Ω n ≠ 2) (hp' : p' ∈ n.primeFactors) :
    IsLeast (consecutiveSet n (jacobiEqSet n p')) (2 ^ Ω n)

/-- **Consecutive constant of the Jacobi–Legendre weights modulo a product of two primes.** For a
natural number $n$ and $A \subseteq \mathbb{Z}/n\mathbb{Z}$, let $C_A(n)$ denote the least positive
integer $k$ such that every sequence $(x_1, \dots, x_k)$ in $\mathbb{Z}/n\mathbb{Z}$ has a block of
consecutive terms $x_s, \dots, x_t$ with $s \le t$ and weights $a_s, \dots, a_t \in A$ such that
$a_s x_s + \dots + a_t x_t = 0$. Let $p'$ and $q$ be distinct primes with $p' \ge 7$ and
$q \ge 7$, let $n = p'q$, and let $L(n;p')$ be the set of units $x$ of $\mathbb{Z}/n\mathbb{Z}$
whose Jacobi symbol $\left(\frac{x}{n}\right)$ equals the Legendre symbol
$\left(\frac{x}{p'}\right)$. Then $C_{L(n;p')}(n) = 6$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Theorem 36
(`jis-2024-24.1.7-thm-36`). -/
public theorem_wanted jacobi_eq_legendre_consecutive_constant_two_primes (p' q : ℕ)
    (hp' : p'.Prime) (hq : q.Prime) (hne : p' ≠ q) (h7p : 7 ≤ p') (h7q : 7 ≤ q) :
    IsLeast (consecutiveSet (p' * q) (jacobiEqSet (p' * q) p')) 6

end

end MetaMathlibExt
