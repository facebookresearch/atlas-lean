/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Enumerative.EvenOddCompositions
public import MathlibExt.Combinatorics.Enumerative.SignedLargePartCompositions
public import MathlibExt.Combinatorics.Enumerative.SignedMinimumPartCompositions

namespace MetaMathlibExt

@[expose] public section

/-! A composition or partition is even (odd) if its number of parts is even
(odd). Compositions are Mathlib's `Composition`, partitions are
`Nat.Partition`, and partitions into distinct parts are
`Nat.Partition.distincts`. -/

/-- **Legendre's identity for partitions into distinct parts.** For a natural number $n$, let
$E(n)$ and $O(n)$ be the numbers of partitions of $n$ into distinct parts with an even and an
odd number of parts, respectively. If $2n = j(3j + 1)$ or $2n = j(3j - 1)$ for some integer
$j \ge 0$, then $E(n) - O(n) = (-1)^j$; otherwise $E(n) - O(n) = 0$.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 1 (Legendre)
(`jis-2024-24.6.5-thm-1`). -/
public theorem_wanted sum_distincts_neg_one_pow_card (n : ℕ) :
    (∀ j : ℕ, 2 * n = j * (3 * j + 1) ∨ 2 * n = j * (3 * j - 1) →
        ∑ p ∈ Nat.Partition.distincts n, (-1 : ℤ) ^ p.parts.card = (-1) ^ j) ∧
      ((∀ j : ℕ, 2 * n ≠ j * (3 * j + 1) ∧ 2 * n ≠ j * (3 * j - 1)) →
        ∑ p ∈ Nat.Partition.distincts n, (-1 : ℤ) ^ p.parts.card = 0)

/-- **Nyirenda's identity for distinct parts modulo a multiple of four.** Let $r \ge 1$ and $n$
be natural numbers, and let $E(n)$ and $O(n)$ be the numbers of partitions of $n$ into distinct
parts, each congruent to $0$, $2r + 1$ or $2r - 1$ modulo $4r$, with an even and an odd number
of parts, respectively. If $n = j(2rj + 1)$ or $n = j(2rj - 1)$ for some integer $j \ge 0$, then
$E(n) - O(n) = (-1)^j$; otherwise $E(n) - O(n) = 0$.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 9 (Nyirenda)
(`jis-2024-24.6.5-thm-9`). -/
public theorem_wanted sum_distincts_mod_four_mul_neg_one_pow_card (r n : ℕ) (hr : 1 ≤ r) :
    (∀ j : ℕ, n = j * (2 * r * j + 1) ∨ n = j * (2 * r * j - 1) →
        ∑ p ∈ (Nat.Partition.distincts n).filter (fun p => ∀ a ∈ p.parts,
            a % (4 * r) = 0 ∨ a % (4 * r) = 2 * r + 1 ∨ a % (4 * r) = 2 * r - 1),
          (-1 : ℤ) ^ p.parts.card = (-1) ^ j) ∧
      ((∀ j : ℕ, n ≠ j * (2 * r * j + 1) ∧ n ≠ j * (2 * r * j - 1)) →
        ∑ p ∈ (Nat.Partition.distincts n).filter (fun p => ∀ a ∈ p.parts,
            a % (4 * r) = 0 ∨ a % (4 * r) = 2 * r + 1 ∨ a % (4 * r) = 2 * r - 1),
          (-1 : ℤ) ^ p.parts.card = 0)

/-- **Nyirenda's identity for distinct parts modulo an odd number.** Let $r \ge 1$ and $n$ be
natural numbers, and let $E(n)$ and $O(n)$ be the numbers of partitions of $n$ into distinct
parts, each congruent to $0$, $r$ or $r + 1$ modulo $2r + 1$, with an even and an odd number of
parts, respectively. If $2n = j((2r + 1)j + 1)$ or $2n = j((2r + 1)j - 1)$ for some integer
$j \ge 0$, then $E(n) - O(n) = (-1)^j$; otherwise $E(n) - O(n) = 0$.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 9 (Nyirenda)
(`jis-2024-24.6.5-thm-9`). -/
public theorem_wanted sum_distincts_mod_two_mul_add_one_neg_one_pow_card (r n : ℕ)
    (hr : 1 ≤ r) :
    (∀ j : ℕ, 2 * n = j * ((2 * r + 1) * j + 1) ∨ 2 * n = j * ((2 * r + 1) * j - 1) →
        ∑ p ∈ (Nat.Partition.distincts n).filter (fun p => ∀ a ∈ p.parts,
            a % (2 * r + 1) = 0 ∨ a % (2 * r + 1) = r ∨ a % (2 * r + 1) = r + 1),
          (-1 : ℤ) ^ p.parts.card = (-1) ^ j) ∧
      ((∀ j : ℕ, 2 * n ≠ j * ((2 * r + 1) * j + 1) ∧ 2 * n ≠ j * ((2 * r + 1) * j - 1)) →
        ∑ p ∈ (Nat.Partition.distincts n).filter (fun p => ∀ a ∈ p.parts,
            a % (2 * r + 1) = 0 ∨ a % (2 * r + 1) = r ∨ a % (2 * r + 1) = r + 1),
          (-1 : ℤ) ^ p.parts.card = 0)

/-- **Signed count of compositions with parts at least $k$ in a residue class.** Let $k, n \ge 1$
and $r > s \ge 0$. Among the compositions of $n + k - 1$ whose parts are all at least $k$ and
congruent to $k + s$ modulo $r$, the number with an odd number of parts minus the number with an
even number of parts is the sum of $(-1)^j \binom{i+j}{i}$ over all $i, j \ge 0$ with
$ri + j(k+s) + s + 1 = n$ (an empty sum when $n \le s$).

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 10
(`jis-2024-24.6.5-thm-10`). -/
public theorem_wanted compositionOddMinusEven_parts_ge_modEq (k n r s : ℕ) (hk : 1 ≤ k)
    (hn : 1 ≤ n) (hsr : s < r) :
    compositionOddMinusEven (n + k - 1)
        (fun c => ∀ a ∈ c.blocks, k ≤ a ∧ a % r = (k + s) % r)
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          if r * i + j * (k + s) + s + 1 = n then (-1 : ℤ) ^ j * ((i + j).choose i : ℤ)
          else 0

/-- **Signed count of residue-class compositions with parts at least $r - s$.** Let $r > s \ge 0$,
let $k = r - s$ and let $n \ge 1$. Among the compositions of $n + k - 1$ whose parts are all at
least $k$ and congruent to $k + s$ modulo $r$, the number with an odd number of parts minus the
number with an even number of parts is $1$ if $n = s + 1$ and $0$ otherwise.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Corollary 12
(`jis-2024-24.6.5-cor-12`). -/
public theorem_wanted compositionOddMinusEven_parts_ge_modEq_sub (n r s : ℕ) (hn : 1 ≤ n)
    (hsr : s < r) :
    compositionOddMinusEven (n + (r - s) - 1)
        (fun c => ∀ a ∈ c.blocks, r - s ≤ a ∧ a % r = (r - s + s) % r)
      = if n = s + 1 then 1 else 0

/-- **Signed count of residue-class compositions with parts at least $2r - s$.** Let $r > s \ge 0$,
let $k = 2r - s$ and let $n \ge 1$. Among the compositions of $n + k - 1$ whose parts are all at
least $k$ and congruent to $k + s$ modulo $r$, let $b^{r,s}_{k,n}$ be the number with an odd
number of parts minus the number with an even number of parts. Then $b^{r,s}_{k,n} = (-1)^j$ if
$n = 3rj + s + 1$ or $n = 3rj + r + s + 1$ for some $j \ge 0$, and $b^{r,s}_{k,n} = 0$ otherwise.

The source record writes this quantity as $d^{r,s}_{k,n}$; the paper's proof computes
$b^{r,s}_{k,n}$, the quantity stated here.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Corollary 13
(`jis-2024-24.6.5-cor-13`). -/
public theorem_wanted compositionOddMinusEven_parts_ge_modEq_two_mul_sub (n r s : ℕ)
    (hn : 1 ≤ n) (hsr : s < r) :
    (∀ j : ℕ, n = 3 * r * j + s + 1 ∨ n = 3 * r * j + r + s + 1 →
        compositionOddMinusEven (n + (2 * r - s) - 1)
          (fun c => ∀ a ∈ c.blocks, 2 * r - s ≤ a ∧ a % r = (2 * r - s + s) % r)
          = (-1) ^ j) ∧
      ((∀ j : ℕ, n ≠ 3 * r * j + s + 1 ∧ n ≠ 3 * r * j + r + s + 1) →
        compositionOddMinusEven (n + (2 * r - s) - 1)
          (fun c => ∀ a ∈ c.blocks, 2 * r - s ≤ a ∧ a % r = (2 * r - s + s) % r) = 0)

/-- **Franklin's partition identity.** Let $k \ge 1$ and let $m$ and $n$ be natural numbers. The
number of partitions of $n$ in which exactly $m$ distinct part sizes occur at least $k$ times
equals the number of partitions of $n$ in which exactly $m$ distinct part sizes are divisible by
$k$.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 14 (Franklin)
(`jis-2024-24.6.5-thm-14`). -/
public theorem_wanted card_partition_franklin (k m n : ℕ) (hk : 1 ≤ k) :
    (Finset.univ.filter fun p : n.Partition =>
        (p.parts.toFinset.filter fun a => k ≤ p.parts.count a).card = m).card
      = (Finset.univ.filter fun p : n.Partition =>
        (p.parts.toFinset.filter fun a => k ∣ a).card = m).card

/-- **Signed count of Huang's compositions, monomial form.** Let $k \ge 2$, $m \ge 0$ and
$n \ge 1$. Among the compositions of $n + k - 1$ with exactly $m$ parts less than $k$ in which
every part less than $k$ is preceded by a part at least $k$ and followed by a part that is either
the last part or greater than $k$, let $b^{(m)}_{k,n}$ be the number with an odd number of parts
minus the number with an even number of parts. Then $b^{(m)}_{k,n}$ is the sum of
$(-1)^j \binom{i}{m} \binom{i+j-1}{j}$ over all $i, j \ge 0$ and all functions
$g \colon \{1, \dots, m\} \to \{0, 1, \dots, k-2\}$ with
$i + (k+1)m + jk + g(1) + \dots + g(m) = n$, where $\binom{-1}{0} = 1$.

Grouping the functions $g$ by the partition $\lambda$ formed by their nonzero values gives the
paper's form of the sum: over partitions $\lambda$ with at most $m$ parts, each at most $k-2$
(written $\lambda \subseteq (k-2)^m$), of size $|\lambda| = n - i - (k+1)m - jk$, each weighted
by $m_\lambda(1^m)$, the monomial symmetric function $m_\lambda$ in $m$ variables evaluated at
$x_1 = \dots = x_m = 1$, which is the number of functions $g$ in the group.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 16
(`jis-2024-24.6.5-thm-16`). -/
public theorem_wanted compositionOddMinusEven_huang_eq_sum_monomial (k m n : ℕ)
    (hk : 2 ≤ k) (hn : 1 ≤ n) :
    compositionOddMinusEven (n + k - 1)
        (fun c => (c.blocks.filter fun a => a < k).length = m ∧
          IsHuangSmallPartPlacement k c.blocks)
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), ∑ g : Fin m → Fin (k - 1),
          if i + (k + 1) * m + j * k + ∑ t, (g t : ℕ) = n then
            (-1 : ℤ) ^ j * (i.choose m : ℤ) * ((i + j - 1).choose j : ℤ)
          else 0

/-- **Signed count of compositions with exactly $m$ parts less than $k$.** Let $k, n \ge 1$ and
$m \ge 0$. Among the compositions of $n + k - 1$ with exactly $m$ parts less than $k$, the number
with an odd number of parts minus the number with an even number of parts is the sum of
$(-1)^{i+\ell+1} \binom{i+j-1}{j} \binom{i}{m} \binom{m}{\ell}$ over all $i, j, \ell \ge 0$ with
$i + j + (k-1)(\ell + i - m - 1) = n$, where $\binom{-1}{0} = 1$.

Only finitely many terms are nonzero: a nonzero term has $\ell \le m$ and
$i, j \le n + (k-1)(m+1)$.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 17
(`jis-2024-24.6.5-thm-17`). -/
public theorem_wanted compositionOddMinusEven_parts_lt_eq_sum (k m n : ℕ) (hk : 1 ≤ k)
    (hn : 1 ≤ n) :
    compositionOddMinusEven (n + k - 1) (fun c => (c.blocks.filter fun a => a < k).length = m)
      = ∑ i ∈ Finset.range (n + k * (m + 1) + 1), ∑ j ∈ Finset.range (n + k * (m + 1) + 1),
          ∑ l ∈ Finset.range (m + 1),
            if (i : ℤ) + j + ((k : ℤ) - 1) * ((l : ℤ) + i - m - 1) = n then
              (-1 : ℤ) ^ (i + l + 1) * ((i + j - 1).choose j : ℤ) * (i.choose m : ℤ) *
                (m.choose l : ℤ)
            else 0

end

end MetaMathlibExt
