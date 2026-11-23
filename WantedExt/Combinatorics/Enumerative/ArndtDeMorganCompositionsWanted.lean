/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Arndt and De Morgan compositions

Statements from Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*,
INTEGERS 26 (2026), Article A64.

The permutations `U` and `V` act on Mathlib's `Composition n`; the counts are over tuples of
positive integers, as in `kArndtCompositionCount`. The number `a(n, k)` of generalized Arndt
compositions of `n` (pairwise condition `c_{2i-1} > c_{2i} + k`) is `kArndtTotalCount k n`, the
sum over the number of parts of `kArndtCompositionCount k n m`
(`WantedExt/Combinatorics/Enumerative/ArndtCompositionsGeneratingFunctionsWanted.lean`).
`c^{2k}_o(n)` and `c^{2k+1}_e(n)` are `oddOrSmallEvenCompositionCount k n` and
`evenOrSmallOddCompositionCount k n`. The permutations `U` and `V` of the paper act on the list of
parts pair by pair; a final unpaired part `c` is the pair `(c, 0)` and maps to `c` parts `1`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Data.Nat.Fib.Basic
public import MathlibExt.NumberTheory.PadovanSequence
public import WantedExt.Combinatorics.Enumerative.ArndtCompositionsGeneratingFunctionsWanted

namespace MetaMathlibExt

@[expose] public section

/-- **Generalized Arndt compositions.** For an integer $k$ and a natural number $n$, $a(n, k)$ is
the number of compositions $(c_1, \dots, c_m)$ of $n$, with any number $m \ge 0$ of parts, such
that $c_{2i-1} > c_{2i} + k$ for every $i$ with $2i \le m$; a final unpaired part is
unconstrained. The empty composition gives $a(0, k) = 1$, and $k = 0$ gives Arndt compositions.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Definition 4. -/
def kArndtTotalCount (k : ℤ) (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (n + 1), kArndtCompositionCount k n m

/-- **Generalized Arndt counts for compositions of five.** The numbers $a(5, k)$ of generalized
Arndt compositions of $5$ (compositions $(c_1, \dots, c_m)$ of $5$ with $c_{2i-1} > c_{2i} + k$
whenever $2i \le m$) are $a(5, 0) = 5$, $a(5, -1) = 10$, $a(5, -2) = 14$ and $a(5, 1) = 3$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Table 9. -/
theorem kArndtTotalCount_five :
    kArndtTotalCount 0 5 = 5 ∧ kArndtTotalCount (-1) 5 = 10 ∧ kArndtTotalCount (-2) 5 = 14 ∧
      kArndtTotalCount 1 5 = 3 := by
  decide

/-- **Compositions into odd or small even parts.** For natural numbers $k$ and $n$, $c^{2k}_o(n)$
is the number of compositions of $n$, with any number of parts, in which every part is odd or at
most $2k$. For $k = 0$ these are De Morgan's compositions of $n$ into odd parts.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Definitions 2 and 5. -/
def oddOrSmallEvenCompositionCount (k n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (n + 1), ((Finset.Nat.antidiagonalTuple m n).filter fun c =>
    ∀ i, 0 < c i ∧ (Odd (c i) ∨ c i ≤ 2 * k)).card

/-- **Compositions of five into odd or small even parts.** Let $c^{2k}_o(n)$ be the number of
compositions of $n$ in which every part is odd or at most $2k$. Then $c^0_o(5) = 5$ and
$c^2_o(5) = 14$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Table 3 and the discussion after Theorem 5. -/
theorem oddOrSmallEvenCompositionCount_five :
    oddOrSmallEvenCompositionCount 0 5 = 5 ∧ oddOrSmallEvenCompositionCount 1 5 = 14 := by
  decide

/-- **Compositions into even or small odd parts.** For natural numbers $k$ and $n$,
$c^{2k+1}_e(n)$ is the number of compositions of $n$ (sequences of positive integers of any
length, including the empty one, that sum to $n$) in which every part is even or at most
$2k + 1$. In particular $c^{2k+1}_e(0) = 1$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Definition 5. -/
def evenOrSmallOddCompositionCount (k n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (n + 1), ((Finset.Nat.antidiagonalTuple m n).filter fun c =>
    ∀ i, 0 < c i ∧ (Even (c i) ∨ c i ≤ 2 * k + 1)).card

/-- **Compositions of $5$ into even or small odd parts.** $c^1_e(5) = 10$ and $c^3_e(5) = 15$,
where $c^{2k+1}_e(n)$ is the number of compositions of $n$ in which every part is even or at
most $2k + 1$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Table 6 and the discussion after Theorem 6. -/
theorem evenOrSmallOddCompositionCount_five :
    evenOrSmallOddCompositionCount 0 5 = 10 ∧ evenOrSmallOddCompositionCount 1 5 = 15 := by
  decide

/-- **The map $U$ on lists.** The map $U$ sends a list $(c_1, c_2, \dots)$ of natural
numbers to the concatenation of the images of its consecutive pairs $(c_1, c_2)$, $(c_3, c_4)$,
and so on, where $1^j$ denotes $j$ parts equal to $1$: a pair $(a, b)$ with $b < a$ goes to
$(1^{a - b - 1}, 2b + 1)$; a pair $(a, b)$ with $b \ge a$ goes to $(1^{a + b - 2k}, 2k)$, where
$k = \lfloor (b - a)/2 \rfloor + 1$ is the integer $k \ge 1$ with $2k - 2 \le b - a < 2k$; and a
final unpaired entry $a$ goes to $1^a$. The empty list goes to itself. The exponent
$a + b - 2k$ is read as $0$ when it is negative, which happens only when $a = 0$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 2 and its proof. -/
def arndtU : List ℕ → List ℕ
  | [] => []
  | [a] => List.replicate a 1
  | a :: b :: rest =>
      (if b < a then List.replicate (a - b - 1) 1 ++ [2 * b + 1]
        else List.replicate (a + b - 2 * ((b - a) / 2 + 1)) 1 ++ [2 * ((b - a) / 2 + 1)]) ++
        arndtU rest

/-- **Values of the map $U$.** The map $U$ sends $(2, 3)$ to $(1, 1, 1, 2)$, $(1, 4)$ to
$(1, 4)$, $(3, 2)$ to $(5)$, $(1, 1, 1, 2)$ to $(2, 1, 2)$ and $(1, 3, 1)$ to $(4, 1)$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Table 3. -/
theorem arndtU_examples :
    arndtU [2, 3] = [1, 1, 1, 2] ∧ arndtU [1, 4] = [1, 4] ∧ arndtU [3, 2] = [5] ∧
      arndtU [1, 1, 1, 2] = [2, 1, 2] ∧ arndtU [1, 3, 1] = [4, 1] := by
  decide

/-- **The map $V$ on lists.** The map $V$ sends a list $(c_1, c_2, \dots)$ of natural
numbers to the concatenation of the images of its consecutive pairs $(c_1, c_2)$, $(c_3, c_4)$,
and so on, where $1^j$ denotes $j$ parts equal to $1$: a pair $(a, b)$ with $b \le a$ goes to
$(1^{a - b}, 2b)$; a pair $(a, b)$ with $b > a$ goes to $(1^{a + b - 2k - 1}, 2k + 1)$, where
$k = \lfloor (b - a + 1)/2 \rfloor$ is the integer $k \ge 1$ with $2k - 1 \le b - a < 2k + 1$;
and a final unpaired entry $a$ goes to $1^a$. The empty list goes to itself. The exponent
$a + b - 2k - 1$ is read as $0$ when it is negative, which happens only when $a = 0$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 3 and its proof. -/
def arndtV : List ℕ → List ℕ
  | [] => []
  | [a] => List.replicate a 1
  | a :: b :: rest =>
      (if b ≤ a then List.replicate (a - b) 1 ++ [2 * b]
        else List.replicate (a + b - 2 * ((b - a + 1) / 2) - 1) 1 ++
          [2 * ((b - a + 1) / 2) + 1]) ++
        arndtV rest

/-- **Values of the map $V$.** The map $V$ sends $(2, 3)$ to $(1, 1, 3)$, $(1, 4)$ to $(5)$,
$(4, 1)$ to $(1, 1, 1, 2)$, $(1, 3, 1)$ to $(1, 3, 1)$ and $(2, 2, 1)$ to $(4, 1)$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Table 6. -/
theorem arndtV_examples :
    arndtV [2, 3] = [1, 1, 3] ∧ arndtV [1, 4] = [5] ∧ arndtV [4, 1] = [1, 1, 1, 2] ∧
      arndtV [1, 3, 1] = [1, 3, 1] ∧ arndtV [2, 2, 1] = [4, 1] := by
  decide

/-- **Arndt compositions and compositions into odd parts are equinumerous.** For every natural
number $n$, the number $a(n, 0)$ of Arndt compositions of $n$ (compositions $(c_1, \dots, c_m)$
of $n$ with $c_{2i-1} > c_{2i}$ whenever $2i \le m$) equals the number $c^0_o(n)$ of compositions
of $n$ into odd parts. This includes $n = 0$, where both counts are $1$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 1 (`integers-2026-A64-thm-1`). -/
public theorem_wanted kArndtTotalCount_zero_eq_odd_compositions (n : ℕ) :
    kArndtTotalCount 0 n = oddOrSmallEvenCompositionCount 0 n

/-- **The pairwise map U permutes compositions.** For every natural number $n$ there is a
permutation $\sigma$ of the compositions of $n$ such that, for every composition $c$ of $n$, the
list of parts of $\sigma(c)$ is $U(c)$, the result of applying the pairwise map $U$ to the list
of parts of $c$. In particular, $U$ sends compositions of $n$ to compositions of $n$ and permutes
them.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 2 (`integers-2026-A64-thm-2`). -/
public theorem_wanted exists_perm_composition_blocks_eq_arndtU (n : ℕ) :
    ∃ σ : Equiv.Perm (Composition n), ∀ c, (σ c).blocks = arndtU c.blocks

/-- **The map $V$ permutes compositions.** For every natural number $n$, the map $V$ sends
compositions of $n$ to compositions of $n$, and it is a permutation of the set of compositions
of $n$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 3 (`integers-2026-A64-thm-3`). -/
public theorem_wanted exists_perm_composition_blocks_eq_arndtV (n : ℕ) :
    ∃ σ : Equiv.Perm (Composition n), ∀ c, (σ c).blocks = arndtV c.blocks

/-- **Compositions fixed by $U$ and their Padovan count.** A composition $(c_1, \dots, c_m)$ of
$n$ is fixed by the map $U$ if and only if $c_i = 1$ for every odd $i$ and $c_i$ is even for
every even $i$. Let $c_U(n)$ be the number of compositions of $n$ fixed by $U$. Then
$c_U(n) = c_U(n - 2) + c_U(n - 3)$ for every $n \ge 4$, $c_U(1) = 1$, $c_U(2) = 0$,
$c_U(3) = 1$, and $c_U(n) = P_{n-1}$ for every $n \ge 1$, where $P$ is the shifted Padovan
sequence, given by $P_0 = 1$, $P_1 = 0$, $P_2 = 1$ and $P_{j+3} = P_{j+1} + P_j$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Proposition 1 (`integers-2026-A64-prop-1`). -/
public theorem_wanted arndtU_fixed_iff_and_count :
    (∀ (n : ℕ) (c : Composition n), arndtU c.blocks = c.blocks ↔
      ∀ (i : ℕ) (h : i < c.blocks.length),
        if i % 2 = 0 then c.blocks[i] = 1 else Even c.blocks[i]) ∧
    (∀ n : ℕ, 4 ≤ n →
      (Finset.univ.filter fun c : Composition n => arndtU c.blocks = c.blocks).card =
        (Finset.univ.filter fun c : Composition (n - 2) => arndtU c.blocks = c.blocks).card +
          (Finset.univ.filter fun c : Composition (n - 3) => arndtU c.blocks = c.blocks).card) ∧
    (Finset.univ.filter fun c : Composition 1 => arndtU c.blocks = c.blocks).card = 1 ∧
    (Finset.univ.filter fun c : Composition 2 => arndtU c.blocks = c.blocks).card = 0 ∧
    (Finset.univ.filter fun c : Composition 3 => arndtU c.blocks = c.blocks).card = 1 ∧
    ∀ n : ℕ, 1 ≤ n →
      (Finset.univ.filter fun c : Composition n => arndtU c.blocks = c.blocks).card =
        shiftedPadovanSequence (n - 1)

/-- **Compositions fixed by $V$ and their Fibonacci count.** A composition $(c_1, \dots, c_m)$
of $n$ is fixed by the map $V$ if and only if $c_i = 1$ for every odd $i$ and $c_i$ is odd and
at least $3$ for every even $i$. Let $c_V(n)$ be the number of compositions of $n$ fixed by $V$.
Then $c_V(n) = c_V(n - 2) + c_V(n - 4)$ for every $n \ge 5$, $c_V(1) = c_V(4) = 1$,
$c_V(2) = c_V(3) = 0$, and $c_V(2j) = c_V(2j + 1) = F_{j-1}$ for every $j \ge 1$, where $F$ is
the Fibonacci sequence with $F_0 = 0$ and $F_1 = 1$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Proposition 2 (`integers-2026-A64-prop-2`). -/
public theorem_wanted arndtV_fixed_iff_and_count :
    (∀ (n : ℕ) (c : Composition n), arndtV c.blocks = c.blocks ↔
      ∀ (i : ℕ) (h : i < c.blocks.length),
        if i % 2 = 0 then c.blocks[i] = 1 else Odd c.blocks[i] ∧ 3 ≤ c.blocks[i]) ∧
    (∀ n : ℕ, 5 ≤ n →
      (Finset.univ.filter fun c : Composition n => arndtV c.blocks = c.blocks).card =
        (Finset.univ.filter fun c : Composition (n - 2) => arndtV c.blocks = c.blocks).card +
          (Finset.univ.filter fun c : Composition (n - 4) => arndtV c.blocks = c.blocks).card) ∧
    (Finset.univ.filter fun c : Composition 1 => arndtV c.blocks = c.blocks).card = 1 ∧
    (Finset.univ.filter fun c : Composition 4 => arndtV c.blocks = c.blocks).card = 1 ∧
    (Finset.univ.filter fun c : Composition 2 => arndtV c.blocks = c.blocks).card = 0 ∧
    (Finset.univ.filter fun c : Composition 3 => arndtV c.blocks = c.blocks).card = 0 ∧
    ∀ j : ℕ, 1 ≤ j →
      (Finset.univ.filter fun c : Composition (2 * j) => arndtV c.blocks = c.blocks).card =
          Nat.fib (j - 1) ∧
        (Finset.univ.filter fun c : Composition (2 * j + 1) =>
          arndtV c.blocks = c.blocks).card = Nat.fib (j - 1)

/-- **Recurrences for generalized Arndt counts.** Let $a(n, k)$ be the number of generalized
Arndt compositions of $n$ with shift $k$, set $a(m, k) = 0$ for $m < 0$, and note that
$a(0, k) = 1$ counts the empty composition. For every natural number $j$ and every $n \ge 3$,
$$a(n, -j) = a(n - 1, -j) + 2a(n - 2, -j) - a(n - 2 - j, -j),$$
and for every natural number $k$ and every $n \ge 3$,
$$a(n, k) = a(n - 1, k) + a(n - 2, k) - a(n - 3, k) + a(n - 3 - k, k).$$

The paper sets $a(n - 2 - j, -j) = 0$ whenever $n - 2 - j \le 0$; at $n - 2 - j = 0$ that is
false ($j = 1$, $n = 3$: $a(3, -1) = 3$, while $a(2, -1) + 2a(1, -1) - 0 = 4$), and its own
bijection uses the empty composition there. At $n = 2$ the recurrences fail for every shift
(for instance $a(2, k) \ne a(1, k) + 2a(0, k)$), so $n \ge 3$ is assumed.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 4 (`integers-2026-A64-thm-4`). -/
public theorem_wanted kArndtTotalCount_recurrence :
    (∀ j n : ℕ, 3 ≤ n →
      (kArndtTotalCount (-(j : ℤ)) n : ℤ) =
        kArndtTotalCount (-(j : ℤ)) (n - 1) + 2 * kArndtTotalCount (-(j : ℤ)) (n - 2) -
          if j + 2 ≤ n then (kArndtTotalCount (-(j : ℤ)) (n - 2 - j) : ℤ) else 0) ∧
    ∀ k n : ℕ, 3 ≤ n →
      (kArndtTotalCount k n : ℤ) =
        kArndtTotalCount k (n - 1) + kArndtTotalCount k (n - 2) - kArndtTotalCount k (n - 3) +
          if k + 3 ≤ n then (kArndtTotalCount k (n - 3 - k) : ℤ) else 0

/-- **Generalized Arndt compositions with negative even shift.** For every natural number
$j \ge 1$ and every natural number $n$, the number $a(n, -2j)$ of compositions
$(c_1, \dots, c_m)$ of $n$ with $c_{2i-1} > c_{2i} - 2j$ whenever $2i \le m$ equals the number
$c^{2j}_o(n)$ of compositions of $n$ in which every part is odd or at most $2j$. This includes
$n = 0$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 5 (`integers-2026-A64-thm-5`). -/
public theorem_wanted kArndtTotalCount_neg_even (j n : ℕ) (hj : 1 ≤ j) :
    kArndtTotalCount (-(2 * j : ℤ)) n = oddOrSmallEvenCompositionCount j n

/-- **Generalized Arndt compositions with negative odd shift.** For all natural numbers $j$ and
$n$, the number $a(n, -2j - 1)$ of compositions $(c_1, \dots, c_m)$ of $n$ with
$c_{2i-1} > c_{2i} - 2j - 1$ whenever $2i \le m$ equals the number $c^{2j+1}_e(n)$ of
compositions of $n$ in which every part is even or at most $2j + 1$. This includes $n = 0$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 6 (`integers-2026-A64-thm-6`). -/
public theorem_wanted kArndtTotalCount_neg_odd (j n : ℕ) :
    kArndtTotalCount (-(2 * j + 1 : ℤ)) n = evenOrSmallOddCompositionCount j n

/-- **Recurrences for even-or-small-odd and odd-or-small-even compositions.** For natural
numbers $k$ and $n$, let $c^{2k+1}_e(n)$ be the number of compositions of $n$ in which every part
is even or at most $2k + 1$, and $c^{2k}_o(n)$ the number in which every part is odd or at most
$2k$. If $k \ge 1$ and $n \ge 3$, then
$$c^{2k+1}_e(n) = c^{2k+1}_e(n - 1) + 2c^{2k+1}_e(n - 2) - c^{2k+1}_e(n - 3 - 2k)$$
and
$$c^{2k}_o(n) = c^{2k}_o(n - 1) + 2c^{2k}_o(n - 2) - c^{2k}_o(n - 2 - 2k),$$
where the last term is read as $0$ when its argument is negative.

Both recurrences fail at $n = 2$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Corollary 1 (`integers-2026-A64-cor-1`). -/
public theorem_wanted evenOrSmallOdd_oddOrSmallEven_recurrence (k n : ℕ) (hk : 1 ≤ k)
    (hn : 3 ≤ n) :
    ((evenOrSmallOddCompositionCount k n : ℤ) =
        evenOrSmallOddCompositionCount k (n - 1) + 2 * evenOrSmallOddCompositionCount k (n - 2) -
          if 2 * k + 3 ≤ n then (evenOrSmallOddCompositionCount k (n - 3 - 2 * k) : ℤ)
          else 0) ∧
      (oddOrSmallEvenCompositionCount k n : ℤ) =
        oddOrSmallEvenCompositionCount k (n - 1) + 2 * oddOrSmallEvenCompositionCount k (n - 2) -
          if 2 * k + 2 ≤ n then (oddOrSmallEvenCompositionCount k (n - 2 - 2 * k) : ℤ) else 0

end

end MetaMathlibExt
