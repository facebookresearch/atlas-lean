/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import WantedExt.NumberTheory.GobelSequenceWanted

/-!
# Non-integrality of `(k, l)`-Göbel sequences (statements)

Statement-only targets from Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of
the (k, l)-Göbel Sequences*. The sequence `g_{k,l}` is the existing `gobelSequence k l`;
`x ∈ ℤ_(p)` is `0 ≤ padicValRat p x`, as in `GobelSequenceWanted`. The thresholds `N_{k,l}`
are not defined; claims about them are stated directly through `gobelSequence`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The residue walk $\tilde g_l$.** For natural numbers $p$ and $l$, write
$\left(\frac{a}{p}\right)$ for the Jacobi symbol. The residue walk
$\tilde g_l \colon \mathbb{N} \to \mathbb{N}$ of $p$ starting at $l$ is defined by
$\tilde g_l(0) = 0$, $\tilde g_l(1) = l$ and, for every $n \ge 1$,
$\tilde g_l(n+1) = \tilde g_l(n) + \left(\frac{n}{p}\right)\left(\frac{\tilde g_l(n)}{p}\right)$
if $0 < \tilde g_l(n) < p$, and $\tilde g_l(n+1) = \tilde g_l(n)$ otherwise.

The sum in the first case is never negative, since $\tilde g_l(n) \ge 1$ there. The paper only
uses the indices $1 \le n \le p$; the value at $0$ and the values beyond $p$ totalize the walk.
For an odd prime $p$ the Jacobi symbol is the Legendre symbol.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the
(k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Section 2
definition of `tilde g_l`. -/
public def gobelResidueWalk (p l : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => l
  | n + 2 =>
      let x := gobelResidueWalk p l (n + 1)
      if 0 < x ∧ x < p then
        Int.toNat ((x : ℤ) + jacobiSym (n + 1 : ℤ) p * jacobiSym (x : ℤ) p)
      else
        x

/-- **Initial value of the residue walk.** For all natural numbers $p$ and $l$, the residue walk
$\tilde g_l$ of $p$ starting at $l$ satisfies $\tilde g_l(1) = l$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Section 2 definition of
`tilde g_l`. -/
public theorem gobelResidueWalk_one (p l : ℕ) : gobelResidueWalk p l 1 = l := by
  rfl

/-- **Recurrence of the residue walk at interior values.** Let $p$, $l$ and $n$ be natural numbers
with $n \ge 1$, write $\tilde g_l$ for the residue walk of $p$ starting at $l$, and write
$\left(\frac{a}{p}\right)$ for the Jacobi symbol. If $0 < \tilde g_l(n) < p$, then

$$\tilde g_l(n+1) = \max\bigl(0, \tilde g_l(n) + (\tfrac{n}{p})(\tfrac{\tilde g_l(n)}{p})\bigr).$$

The maximum with $0$ records the conversion of the integer sum back to a natural number; the sum
is never negative because $\tilde g_l(n) \ge 1$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the
(k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Section 2
definition of `tilde g_l`. -/
public theorem gobelResidueWalk_succ_of_between (p l n : ℕ) (hn : 1 ≤ n)
    (hbetween : 0 < gobelResidueWalk p l n ∧ gobelResidueWalk p l n < p) :
    gobelResidueWalk p l (n + 1) =
      Int.toNat ((gobelResidueWalk p l n : ℤ) +
        jacobiSym (n : ℤ) p * jacobiSym (gobelResidueWalk p l n : ℤ) p) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 1 m] at hbetween ⊢
  change (if 0 < gobelResidueWalk p l (m + 1) ∧ gobelResidueWalk p l (m + 1) < p then
      Int.toNat ((gobelResidueWalk p l (m + 1) : ℤ) +
        jacobiSym (m + 1 : ℤ) p * jacobiSym (gobelResidueWalk p l (m + 1) : ℤ) p)
    else gobelResidueWalk p l (m + 1)) = _
  simp [hbetween]

/-- **The residue walk stays at $0$.** Let $p$, $l$ and $n$ be natural numbers with $n \ge 1$,
and write $\tilde g_l$ for the residue walk of $p$ starting at $l$. If $\tilde g_l(n) = 0$, then
$\tilde g_l(n+1) = 0$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Section 2 definition of
`tilde g_l`. -/
public theorem gobelResidueWalk_succ_of_eq_zero (p l n : ℕ) (hn : 1 ≤ n)
    (hzero : gobelResidueWalk p l n = 0) :
    gobelResidueWalk p l (n + 1) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 1 m] at hzero ⊢
  change (if 0 < gobelResidueWalk p l (m + 1) ∧ gobelResidueWalk p l (m + 1) < p then _
    else gobelResidueWalk p l (m + 1)) = 0
  simp [hzero]

/-- **The residue walk stays at $p$.** Let $p$, $l$ and $n$ be natural numbers with $n \ge 1$,
and write $\tilde g_l$ for the residue walk of $p$ starting at $l$. If $\tilde g_l(n) = p$, then
$\tilde g_l(n+1) = p$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Section 2 definition of
`tilde g_l`. -/
public theorem gobelResidueWalk_succ_of_eq_prime (p l n : ℕ) (hn : 1 ≤ n)
    (hprime : gobelResidueWalk p l n = p) :
    gobelResidueWalk p l (n + 1) = p := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 1 m] at hprime ⊢
  change (if 0 < gobelResidueWalk p l (m + 1) ∧ gobelResidueWalk p l (m + 1) < p then _
    else gobelResidueWalk p l (m + 1)) = p
  simp [hprime]

/-- **Zigzag order on integer sequences.** For a natural number $p$ and functions
$a, b : \mathbb{N} \to \mathbb{Z}$, $a$ lies zigzag-below $b$ up to $p$, written $a \preceq b$,
when there is a natural number $m \le p$ such that $a(n) < b(n)$ for all $1 \le n \le m$ and
$a(n) = b(n)$ for all $m < n \le p$.

The paper's point sets are represented by their integer-valued coordinate functions; values
outside $1 \le n \le p$ play no role.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-
Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Section 2 definition
of `⪯`. -/
public def IsZigzagBelow (p : ℕ) (a b : ℕ → ℤ) : Prop :=
  ∃ m ≤ p,
    (∀ n, 1 ≤ n → n ≤ m → a n < b n) ∧
    (∀ n, m < n → n ≤ p → a n = b n)

/-- **The sign sequence $a_{p,l}$.** For natural numbers $p$ and $l$, a function
$a : \mathbb{N} \to \mathbb{Z}$ is an $a_{p,l}$-sequence when all of the following hold:
$a(n) \in \{1, -1\}$ for $1 \le n \le p-1$; $a(n) = 0$ for $n = 0$ and for every $n \ge p$;
$a(1) = 1$; $a(n) = a(p-n)$ for $1 \le n \le \lfloor (p-1)/2 \rfloor$; $a(n) = -a(l+1-n)$ for
$1 \le n \le \lfloor l/2 \rfloor$; and $a(n) = a(l+1+n)$ for $1 \le n \le p-l-2$.

The values outside $1 \le n \le p-1$ are fixed to $0$ so that uniqueness of the paper's finite
sequence becomes uniqueness of the function.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of
the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8,
Proposition 17. -/
public def IsGobelASequence (p l : ℕ) (a : ℕ → ℤ) : Prop :=
  (∀ n, 1 ≤ n → n ≤ p - 1 → a n = 1 ∨ a n = -1) ∧
  (∀ n, n = 0 ∨ p ≤ n → a n = 0) ∧
  a 1 = 1 ∧
  (∀ n, 1 ≤ n → n ≤ (p - 1) / 2 → a n = a (p - n)) ∧
  (∀ n, 1 ≤ n → n ≤ l / 2 → a n = -a (l + 1 - n)) ∧
  (∀ n, 1 ≤ n → n ≤ p - l - 2 → a n = a (l + 1 + n))

/-- **The periodic sign sequence $b_{l,s}$.** For natural numbers $l$ and $s$, a function
$b : \mathbb{Z} \to \mathbb{Z}$ is a $b_{l,s}$-sequence when all of the following hold:
$b(n) \in \{1, -1\}$ for every integer $n$; $b(n + l + 1) = b(n)$ for every integer $n$;
$b(1) = 1$; $b(n) = -b(l+1-n)$ for every integer $n$ not divisible by $l+1$; and
$b(s-n) = b(s+1+n)$ for every integer $n$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality
of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8,
Proposition 20. -/
public def IsGobelBSequence (l s : ℕ) (b : ℤ → ℤ) : Prop :=
  (∀ n, b n = 1 ∨ b n = -1) ∧
  (∀ n, b (n + (l + 1 : ℤ)) = b n) ∧
  b 1 = 1 ∧
  (∀ n, Int.emod n (l + 1 : ℤ) ≠ 0 → b n = -b ((l + 1 : ℤ) - n)) ∧
  (∀ n, b ((s : ℤ) - n) = b ((s : ℤ) + 1 + n))

/-- **Left boundary of the even Göbel residue walks.** Fix a natural number $p$ and, for each
natural number $l$, let $\tilde g_l$ denote the Göbel residue walk for $p$ starting at $l$. A
natural number $l_L$ is the left boundary for $p$ when there is an even natural number $l_0 < p$
with $\tilde g_{l_0}(p) = 0$ and $l_L = l_0 + 2$ such that every even natural number $l < p$
with $\tilde g_l(p) = 0$ satisfies $l \le l_0$. In other words, the set of even $l < p$ with
$\tilde g_l(p) = 0$ is nonempty and $l_L$ is its maximum plus $2$.

Source: Yuh Kobayashi and
Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer
Sequences 29 (2026), Article 26.3.8, proof of Theorem 1. -/
public def IsGobelLeftBoundary (p lL : ℕ) : Prop :=
  ∃ l0, Even l0 ∧ l0 < p ∧ gobelResidueWalk p l0 p = 0 ∧ lL = l0 + 2 ∧
    ∀ l, Even l → l < p → gobelResidueWalk p l p = 0 → l ≤ l0

/-- **Right boundary of the even Göbel residue walks.** Fix a natural number $p$ and, for each
natural number $l$, let $\tilde g_l$ denote the Göbel residue walk for $p$ starting at $l$. A
natural number $l_R$ is the right boundary for $p$ when $l_R$ is even, $l_R < p$,
$\tilde g_{l_R}(p) = p$, and every even natural number $l < p$ with $\tilde g_l(p) = p$
satisfies $l_R \le l$. In other words, $l_R$ is the least even $l < p$ with $\tilde g_l(p) = p$.

Source: Yuh Kobayashi and
Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer
Sequences 29 (2026), Article 26.3.8, proof of Theorem 1. -/
public def IsGobelRightBoundary (p lR : ℕ) : Prop :=
  Even lR ∧ lR < p ∧ gobelResidueWalk p lR p = p ∧
    ∀ l, Even l → l < p → gobelResidueWalk p l p = p → lR ≤ l

/-- **Göbel sequences at index $p$ for primes $p \equiv 3 \pmod 4$.** Let $g_{k,l}$ denote the
$(k, l)$-Göbel sequence and let $p$ be a prime with $p \equiv 3 \pmod 4$. Then for every natural
number $l < p$, the $p$-adic valuation of $g_{(p-1)/2,\,l}(p)$ is nonnegative (the valuation of
$0$ is taken to be $0$); that is, $g_{(p-1)/2,\,l}(p)$ lies in the localization
$\mathbb{Z}_{(p)}$.

Source: Yuh Kobayashi and
Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer
Sequences 29 (2026), Article 26.3.8, Theorem 1(a). -/
public theorem_wanted gobelSequence_half_pred_mem_localization_of_three_mod_four
    (p : ℕ) (hp : p.Prime) (hmod : p % 4 = 3) :
    ∀ l, l < p → 0 ≤ padicValRat p (gobelSequence ((p - 1) / 2) l p)

/-- **Odd starting values give a $p$-integral $p$-th term when $p \equiv 1 \pmod 4$.** Let $p$ be
a prime with $p \equiv 1 \pmod 4$, write $k = (p-1)/2$, and let $g_{k,l}$ denote the
$(k,l)$-Göbel sequence. Then for every odd natural number $l < p$, the term $g_{k,l}(p)$ lies in
the localization $\mathbb{Z}_{(p)}$, that is, its $p$-adic valuation is nonnegative.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-
Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Theorem 1(b), odd
case. -/
public theorem_wanted gobelSequence_half_pred_mem_localization_of_one_mod_four_of_odd
    (p : ℕ) (hp : p.Prime) (hmod : p % 4 = 1) :
    ∀ l, Odd l → l < p → 0 ≤ padicValRat p (gobelSequence ((p - 1) / 2) l p)

/-- **Unique boundary pair for Göbel sequences when $p \equiv 1 \pmod 4$.** Let $g_{k,l}$ denote
the $(k, l)$-Göbel sequence and let $p \ge 13$ be a prime with $p \equiv 1 \pmod 4$. Then there
is exactly one pair $(l_L, l_R)$ of even natural numbers with $2 \le l_L < l_R \le p-1$ such
that, for every even natural number $l < p$, the $p$-adic valuation of $g_{(p-1)/2,\,l}(p)$ is
nonnegative (the valuation of $0$ is taken to be $0$) if and only if $l < l_L$ or $l_R \le l$.

Thus the even $l < p$ split into the three intervals $l < l_L$, $l_L \le l < l_R$ and
$l_R \le l$, and $g_{(p-1)/2,\,l}(p)$ lies in $\mathbb{Z}_{(p)}$ exactly on the outer two.

Source: Yuh
Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.3.8, Theorem 1(b), unique decomposition. -/
public theorem_wanted gobelSequence_half_pred_unique_even_localization_decomposition
    (p : ℕ) (hp : p.Prime) (hmod : p % 4 = 1) (hp13 : 13 ≤ p) :
    ∃! bounds : ℕ × ℕ,
      Even bounds.1 ∧ Even bounds.2 ∧ 2 ≤ bounds.1 ∧ bounds.1 < bounds.2 ∧
      bounds.2 ≤ p - 1 ∧
      ∀ l, Even l → l < p →
        (0 ≤ padicValRat p (gobelSequence ((p - 1) / 2) l p) ↔
          l < bounds.1 ∨ bounds.2 ≤ l)

/-- **A congruence class of non-integral Göbel sequences.** Let $g_{k,l}$ denote the
$(k, l)$-Göbel sequence, let $p \ge 13$ be a prime with $p \equiv 1 \pmod 4$, and let
$k = \frac{p-1}{2} q$ for a positive odd natural number $q$. Then there is an even natural number
$l$ with $2 \le l \le p-3$ such that for every positive natural number $l'$ with
$l' \equiv l \pmod p$, the $p$-adic valuation of $g_{k,l'}(p)$ is negative, and some
$g_{k,l'}(n)$ with $1 \le n \le p$ is not an integer.

Every such $k$ is positive and even, as the paper requires.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Corollary 2. -/
public theorem_wanted gobelSequence_nonintegral_congruence_class_of_odd_multiple
    (k p : ℕ) (hp : p.Prime) (hp13 : 13 ≤ p)
    (hmod : p % 4 = 1)
    (hmultiple : ∃ q, 0 < q ∧ Odd q ∧ k = ((p - 1) / 2) * q) :
    ∃ l, Even l ∧ 2 ≤ l ∧ l ≤ p - 3 ∧
      ∀ l', 0 < l' → l' % p = l % p →
        padicValRat p (gobelSequence k l' p) < 0 ∧
        ∃ n, 1 ≤ n ∧ n ≤ p ∧ ¬∃ z : ℤ, gobelSequence k l' n = z

/-- **The odd multiples of $(p-1)/2$ admit no finite subcover.** For a prime $p$ write
$A_p = \{\tfrac{p-1}{2}(2m+1) : m \in \mathbb{N}\}$ for the set of odd multiples of $(p-1)/2$. For
every finite set $S$ of primes $q$ with $q \ge 13$ and $q \equiv 1 \pmod 4$, there is a natural
number $k$ that lies in $A_p$ for some prime $p \ge 13$ with $p \equiv 1 \pmod 4$ but lies in no
$A_q$ with $q \in S$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-
Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Lemma 3. -/
public theorem_wanted odd_multiple_prime_half_sets_not_finitely_coverable :
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ 13 ≤ p ∧ p % 4 = 1) → ∃ k,
      (∃ p m, p.Prime ∧ 13 ≤ p ∧ p % 4 = 1 ∧
        k = ((p - 1) / 2) * (2 * m + 1)) ∧
      ∀ p ∈ S, ¬∃ m, k = ((p - 1) / 2) * (2 * m + 1)

/-- **Index-scaled Göbel terms with $k = (p-1)/2$ are congruent to the residue walk.** Let $p$
be an odd prime and $l \le p - 1$ a natural number. Write $k = (p-1)/2$, let $g_{k,l}$ be the
$(k,l)$-Göbel sequence, and let $\tilde g_l$ be the residue walk of $p$ starting at $l$. Then
(a) for every $1 \le n \le p$, the rational number $n\,g_{k,l}(n) - \tilde g_l(n)$ is either $0$
or has $p$-adic valuation at least $1$, that is,
$n\,g_{k,l}(n) \equiv \tilde g_l(n) \pmod{p}$ in $\mathbb{Z}_{(p)}$; and (b) $g_{k,l}(p)$ lies in
the localization $\mathbb{Z}_{(p)}$, that is, has nonnegative $p$-adic valuation, if and only if
$\tilde g_l(p) = 0$ or $\tilde g_l(p) = p$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Lemma 6. -/
public theorem_wanted gobelSequence_half_pred_congruent_residue_walk
    (p l : ℕ) (hp : p.Prime) (hpodd : Odd p) (hl : l ≤ p - 1) :
    (∀ n, 1 ≤ n → n ≤ p →
      let d : ℚ := (n : ℚ) * gobelSequence ((p - 1) / 2) l n - gobelResidueWalk p l n
      d = 0 ∨ 1 ≤ padicValRat p d) ∧
    (0 ≤ padicValRat p (gobelSequence ((p - 1) / 2) l p) ↔
      gobelResidueWalk p l p = 0 ∨ gobelResidueWalk p l p = p)

/-- **The residue walk stays on the diagonal.** Let $p$ be an odd prime, let $l \le p - 1$ be a
natural number, and let $\tilde g_l$ be the residue walk of $l$ for $p$. If $1 \le m \le p$ and
$\tilde g_l(m) = m$, then $\tilde g_l(n) = n$ for every $n$ with $m \le n \le p$.

Source: Yuh Kobayashi and
Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer
Sequences 29 (2026), Article 26.3.8, Lemma 8. -/
public theorem_wanted gobelResidueWalk_eq_index_of_eq_index
    (p l m : ℕ) (hp : p.Prime) (hpodd : Odd p) (hl : l ≤ p - 1)
    (hm1 : 1 ≤ m) (hmp : m ≤ p) (hmeq : gobelResidueWalk p l m = m) :
    ∀ n, m ≤ n → n ≤ p → gobelResidueWalk p l n = n

/-- **The diagonal is zigzag-below every odd residue walk.** Let $p$ be an odd prime, let $l$ be
an odd natural number with $l < p$, and let $\tilde g_l$ be the residue walk of $l$ for $p$. Then
the diagonal $n \mapsto n$ is zigzag-below $\tilde g_l$ up to $p$: there is $m \le p$ such that
$n < \tilde g_l(n)$ for all $1 \le n \le m$ and $\tilde g_l(n) = n$ for all $m < n \le p$.

Source: Yuh Kobayashi and
Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer
Sequences 29 (2026), Article 26.3.8, Proposition 9. -/
public theorem_wanted diagonal_isZigzagBelow_gobelResidueWalk_of_odd
    (p l : ℕ) (hp : p.Prime) (hpodd : Odd p) (hlodd : Odd l) (hlp : l < p) :
    IsZigzagBelow p (fun n => (n : ℤ)) (fun n => gobelResidueWalk p l n)

/-- **Even residue walks lie zigzag-below the antidiagonal when $p \equiv 3 \pmod 4$.** Let $p$
be a prime with $p \equiv 3 \pmod 4$, let $l < p$ be an even natural number, and write
$\tilde g_l$ for the residue walk of $p$ starting at $l$. Then $\tilde g_l$ is zigzag-below the
function $n \mapsto p - n$ up to $p$: there is an $m \le p$ such that $\tilde g_l(n) < p - n$
for $1 \le n \le m$ and $\tilde g_l(n) = p - n$ for $m < n \le p$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Proposition 10. -/
public theorem_wanted gobelResidueWalk_isZigzagBelow_antidiagonal_of_three_mod_four
    (p l : ℕ) (hp : p.Prime) (hmod : p % 4 = 3)
    (hleven : Even l) (hlp : l < p) :
    IsZigzagBelow p (fun n => gobelResidueWalk p l n) (fun n => (p : ℤ) - n)

/-- **Consecutive even residue walks form a zigzag chain when $p \equiv 1 \pmod 4$.** Let $p$
be a prime with $p \equiv 1 \pmod 4$, and for a natural number $l$ write $\tilde g_l$ for the
residue walk of $p$ starting at $l$. Then for every even natural number $l$ with
$l + 2 \le p - 1$, the walk $\tilde g_l$ is zigzag-below $\tilde g_{l+2}$ up to $p$: there is
an $m \le p$ such that $\tilde g_l(n) < \tilde g_{l+2}(n)$ for $1 \le n \le m$ and
$\tilde g_l(n) = \tilde g_{l+2}(n)$ for $m < n \le p$. Writing $A \preceq B$ when $A$ is
zigzag-below $B$ up to $p$, these links form the chain
$\tilde g_0 \preceq \tilde g_2 \preceq \cdots \preceq \tilde g_{p-1}$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-
Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Proposition 11. -/
public theorem_wanted gobelResidueWalk_even_chain_of_one_mod_four
    (p : ℕ) (hp : p.Prime) (hmod : p % 4 = 1) :
    ∀ l, Even l → l + 2 ≤ p - 1 →
      IsZigzagBelow p (fun n => gobelResidueWalk p l n)
        (fun n => gobelResidueWalk p (l + 2) n)

/-- **Equality of the left and right boundaries via Legendre symbols.** Let $p$ be a prime with
$p \equiv 1 \pmod 4$ and, for each $l$, let $\tilde g_l$ be the residue walk of $l$ for $p$.
Suppose that $l_0$ is the largest even $l < p$ with $\tilde g_l(p) = 0$, put $l_L = l_0 + 2$, and
suppose that $l_R$ is the smallest even $l < p$ with $\tilde g_l(p) = p$. Then $l_L = l_R$ if and
only if there is an even natural number $l \le p - 3$ such that
$\left(\frac{n}{p}\right) = -\left(\frac{l + 1 - n}{p}\right)$ for all $1 \le n \le l/2$ and
$\left(\frac{n}{p}\right) = \left(\frac{l + 1 + n}{p}\right)$ for all $1 \le n \le p - l - 2$,
where $\left(\frac{\cdot}{p}\right)$ is the Legendre symbol.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on
Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article
26.3.8, Theorem 15. -/
public theorem_wanted gobel_boundaries_eq_iff_jacobi_symmetries
    (p lL lR : ℕ) (hp : p.Prime) (hmod : p % 4 = 1)
    (hleft : IsGobelLeftBoundary p lL) (hright : IsGobelRightBoundary p lR) :
    lL = lR ↔
      ∃ l, Even l ∧ l ≤ p - 3 ∧
        (∀ n, 1 ≤ n → n ≤ l / 2 →
          jacobiSym (n : ℤ) p = -jacobiSym (l + 1 - n : ℤ) p) ∧
        (∀ n, 1 ≤ n → n ≤ p - l - 2 →
          jacobiSym (n : ℤ) p = jacobiSym (l + 1 + n : ℤ) p)

/-- **Arithmetic billiards in a tilted rectangle.** Let $p$ be a prime with $p \equiv 1 \pmod 4$
and let $l$ be an even natural number with $l + 3 \le p$. Put $m = l + 1$ if $2l + 5 \le p$ and
$m = p - (l + 1)$ otherwise, and let $R \subseteq \mathbb{R}^2$ be the convex hull of the four
points $(0, m)$, $(m, 0)$, $(p/2, p/2 - m)$ and $(p/2 - m, p/2)$. Let $L$ be the set of integer
points on the boundary of $R$ other than $(0, m)$ and $(m, 0)$. Call a sequence $P_0, P_1, \ldots$
of integer points a billiard path if $P_0 = (0, m)$ and, for every $i < p - 1$, the point
$P_{i+1}$ lies on the boundary of $R$, differs from $P_i$, and has the same second coordinate as
$P_i$ when $i$ is even and the same first coordinate as $P_i$ when $i$ is odd. Then a billiard
path exists, and every billiard path $P$ maps $\{1, \ldots, p - 2\}$ bijectively onto $L$,
satisfies $P_{p-1} = (m, 0)$, and satisfies $P_{p-1-i} = (y_i, x_i)$ for every $i \le p - 1$,
where $P_i = (x_i, y_i)$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Lemma 16
(`lem:billiards`). -/
public theorem_wanted arithmetic_billiards_rotated_rectangle (p l : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 1) (hl : Even l) (hlp : l + 3 ≤ p) :
    let m : ℕ := if 2 * l + 5 ≤ p then l + 1 else p - (l + 1)
    let c : ℝ := if 2 * l + 5 ≤ p then (p : ℝ) / 2 - (l + 1) else (l + 1 : ℝ) - p / 2
    let R : Set (ℝ × ℝ) :=
      convexHull ℝ {((0 : ℝ), (m : ℝ)), ((m : ℝ), (0 : ℝ)), ((p : ℝ) / 2, c), (c, (p : ℝ) / 2)}
    let L : Set (ℤ × ℤ) :=
      {z | ((z.1 : ℝ), (z.2 : ℝ)) ∈ frontier R} \ {((0 : ℤ), (m : ℤ)), ((m : ℤ), (0 : ℤ))}
    let IsPath : (ℕ → ℤ × ℤ) → Prop := fun P =>
      P 0 = (0, (m : ℤ)) ∧ ∀ i < p - 1,
        (((P (i + 1)).1 : ℝ), ((P (i + 1)).2 : ℝ)) ∈ frontier R ∧ P (i + 1) ≠ P i ∧
          if Even i then (P (i + 1)).2 = (P i).2 else (P (i + 1)).1 = (P i).1
    (∃ P, IsPath P) ∧ ∀ P, IsPath P →
      Set.BijOn P (Set.Icc 1 (p - 2)) L ∧ P (p - 1) = ((m : ℤ), 0) ∧
        ∀ i ≤ p - 1, P (p - 1 - i) = (P i).swap

/-- **Existence and uniqueness of the sequence $a_{p,l}$.** Let $p$ be a prime with
$p \equiv 1 \pmod 4$ and let $l$ be an even natural number with $l \le p - 3$. Then exactly one
function $a : \mathbb{N} \to \mathbb{Z}$ satisfies the defining conditions of $a_{p,l}$:
$a(n) = \pm 1$ for $1 \le n \le p - 1$, $a(n) = 0$ for $n = 0$ and for $n \ge p$, $a(1) = 1$,
$a(n) = a(p - n)$ for $1 \le n \le (p - 1)/2$, $a(n) = -a(l + 1 - n)$ for $1 \le n \le l/2$, and
$a(n) = a(l + 1 + n)$ for $1 \le n \le p - l - 2$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note
on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026),
Article 26.3.8, Proposition 17. -/
public theorem_wanted existsUnique_gobelASequence
    (p l : ℕ) (hp : p.Prime) (hmod : p % 4 = 1) (hleven : Even l) (hl : l ≤ p - 3) :
    ∃! a : ℕ → ℤ, IsGobelASequence p l a

/-- **Existence and uniqueness of the sequence $b_{l,s}$.** Let $l$ be an even natural number and
$s$ a natural number with $s \le l$ such that $2s + 1$ and $l + 1$ are coprime. Then exactly one
function $b : \mathbb{Z} \to \mathbb{Z}$ satisfies the defining conditions of $b_{l,s}$:
$b(n) = \pm 1$ for every integer $n$, $b(n + l + 1) = b(n)$ for every $n$, $b(1) = 1$,
$b(n) = -b(l + 1 - n)$ for every $n$ not divisible by $l + 1$, and $b(s - n) = b(s + 1 + n)$ for
every $n$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on
Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article
26.3.8, Proposition 20. -/
public theorem_wanted existsUnique_gobelBSequence
    (l s : ℕ) (hleven : Even l) (hs : s ≤ l) (hcoprime : Nat.Coprime (2 * s + 1) (l + 1)) :
    ∃! b : ℤ → ℤ, IsGobelBSequence l s b

/-- **Complementary sequences $b_{l,s}$ and $b_{l,l-s}$.** Let $l \ge 2$ be an even natural
number and $s \le l$ a natural number such that $2s + 1$ and $l + 1$ are coprime. Let
$b_1, b_2 : \mathbb{Z} \to \mathbb{Z}$ satisfy the defining conditions of $b_{l,s}$ and of
$b_{l,l-s}$ respectively. Then for every integer $n$, $b_1(n) = b_2(n)$ if $l + 1$ does not divide
$n$, and $b_1(n) = -b_2(n)$ if $l + 1$ divides $n$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Lemma 22. -/
public theorem_wanted gobelBSequence_complement
    (l s : ℕ) (hleven : Even l) (hs : s ≤ l) (hl2 : 2 ≤ l)
    (hcoprime : Nat.Coprime (2 * s + 1) (l + 1))
    (b₁ b₂ : ℤ → ℤ) (hb₁ : IsGobelBSequence l s b₁)
    (hb₂ : IsGobelBSequence l (l - s) b₂) :
    ∀ n, (Int.emod n (l + 1 : ℤ) ≠ 0 → b₁ n = b₂ n) ∧
      (Int.emod n (l + 1 : ℤ) = 0 → b₁ n = -b₂ n)

/-- **Translation and reflection identities for $b_{l,s}$.** Let $l \ge 2$ be an even natural
number and $s \le l$ a natural number such that $2s + 1$ and $l + 1$ are coprime, let
$b : \mathbb{Z} \to \mathbb{Z}$ satisfy the defining conditions of $b_{l,s}$, and write
$t = l/2 - s$. Then the following hold. (a) For every integer $n$ such that neither $n$ nor
$n + 2s + 1$ is divisible by $l + 1$, $b(n) = -b(n + 2s + 1)$. (b) If $s < l/2$, then for every
integer $n$ such that neither $n$ nor $n + 2t$ is divisible by $l + 1$, $b(n) = -b(n + 2t)$.
(c) If $s < l/2$, then for every integer $n$ such that neither $t - n$ nor $t + n$ is divisible
by $l + 1$, $b(t - n) = b(t + n)$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Lemma 23. -/
public theorem_wanted gobelBSequence_translation_identities
    (l s : ℕ) (hleven : Even l) (hs : s ≤ l) (hl2 : 2 ≤ l)
    (hcoprime : Nat.Coprime (2 * s + 1) (l + 1))
    (b : ℤ → ℤ) (hb : IsGobelBSequence l s b) :
    (∀ n : ℤ, Int.emod n (l + 1 : ℤ) ≠ 0 →
      Int.emod (n + (2 * s + 1 : ℕ)) (l + 1 : ℤ) ≠ 0 →
      b n = -b (n + (2 * s + 1 : ℕ))) ∧
    (s < l / 2 →
      ∀ n : ℤ, Int.emod n (l + 1 : ℤ) ≠ 0 →
        Int.emod (n + (2 * (l / 2 - s) : ℕ)) (l + 1 : ℤ) ≠ 0 →
        b n = -b (n + (2 * (l / 2 - s) : ℕ))) ∧
    (s < l / 2 →
      ∀ n : ℤ, Int.emod (((l / 2 - s : ℕ) : ℤ) - n) (l + 1 : ℤ) ≠ 0 →
        Int.emod (((l / 2 - s : ℕ) : ℤ) + n) (l + 1 : ℤ) ≠ 0 →
        b (((l / 2 - s : ℕ) : ℤ) - n) = b (((l / 2 - s : ℕ) : ℤ) + n))

/-- **The sequence $a_{p,l}$ is not multiplicative at an even index.** Let $p \ge 13$ be a prime
with $p \equiv 1 \pmod 4$, let $l$ be an even natural number with $2 \le l \le p - 3$, and let
$a : \mathbb{N} \to \mathbb{Z}$ satisfy the defining conditions of $a_{p,l}$. Then there is a
positive integer $m$ with $2m \le p - 3$ such that $a(2m) \ne a(2)\,a(m)$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on
Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article
26.3.8, Theorem 25. -/
public theorem_wanted gobelASequence_not_multiplicative_at_even_index
    (p l : ℕ) (hp : p.Prime) (hp13 : 13 ≤ p) (hmod : p % 4 = 1)
    (hleven : Even l) (hl2 : 2 ≤ l) (hlp : l ≤ p - 3)
    (a : ℕ → ℤ) (ha : IsGobelASequence p l a) :
    ∃ m, 0 < m ∧ 2 * m ≤ p - 3 ∧ a (2 * m) ≠ a 2 * a m

/-- **The first non-integral term of $g_{2600725,2}$ is at index $9011$.** Let $g_{k,l}$ denote
the $(k,l)$-Göbel sequence. The rational number $g_{2600725,2}(9011)$ is not an integer, while
$g_{2600725,2}(n)$ is an integer for every natural number $n$ with $1 \le n < 9011$. Writing
$N_k$ for the first index at which $g_{k,2}$ is not an integer, as in the paper, this says
$N_{2600725} = 9011$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Theorem 26. -/
public theorem_wanted gobelSequence_first_nonintegral_2600725 :
    (¬∃ z : ℤ, gobelSequence 2600725 2 9011 = z) ∧
    ∀ n, 1 ≤ n → n < 9011 → ∃ z : ℤ, gobelSequence 2600725 2 n = z

/-- **A non-integral term of $g_{k,2}$ by index $9011$ for $2 \le k \le 10^7$.** Let $g_{k,l}$
denote the $(k, l)$-Göbel sequence. For every natural number $k$ with $2 \le k \le 10^7$, there
is a natural number $n$ with $1 \le n \le 9011$ such that the rational number $g_{k,2}(n)$ is
not an integer.

Writing $N_k$ for the first index at which $g_{k,2}$ is not an integer, as in the paper, this
says $N_k \le 9011$ for $2 \le k \le 10^7$; together with $N_{2600725} = 9011$, this makes $9011$
the largest of these thresholds. The paper also reports that each of these $N_k$ was determined
explicitly by computation; that claim is not part of this statement.

Source: Yuh
Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.3.8, Theorem 26. -/
public theorem_wanted gobelSequence_nonintegral_index_le_9011
    (k : ℕ) (hk2 : 2 ≤ k) (hkmax : k ≤ 10 ^ 7) :
    ∃ n, 1 ≤ n ∧ n ≤ 9011 ∧ ¬∃ z : ℤ, gobelSequence k 2 n = z

/-- **Counting prime first nonintegral indices of $g_{k,2}$ for $k \le 10^7$.** Exactly
$8649270$ natural numbers $k$ with $2 \le k \le 10^7$ have the following property: for the
$(k, 2)$-Göbel sequence $g_{k,2}$ there is a prime $q$ such that $g_{k,2}(q)$ is not an integer
and $g_{k,2}(n)$ is an integer for every $1 \le n < q$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-
Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Theorem 26. -/
public theorem_wanted card_gobelSequence_prime_first_nonintegral_index :
    Nat.card {k : ℕ // 2 ≤ k ∧ k ≤ 10 ^ 7 ∧
      ∃ q, q.Prime ∧ (¬∃ z : ℤ, gobelSequence k 2 q = z) ∧
        ∀ n, 1 ≤ n → n < q → ∃ z : ℤ, gobelSequence k 2 n = z} = 8649270

/-- **A non-integral term of $g_{k,2}$ by index $29363$ for $2 \le k \le 10^{14}$.** Let
$g_{k,l}$ denote the $(k, l)$-Göbel sequence. For every natural number $k$ with
$2 \le k \le 10^{14}$, there is a natural number $n$ with $1 \le n \le 29363$ such that the
rational number $g_{k,2}(n)$ is not an integer.

Writing $N_k$ for the first index at which $g_{k,2}$ is not an integer, as in the paper, this
says $N_k \le 29363$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on
Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article
26.3.8, Theorem 29. -/
public theorem_wanted gobelSequence_nonintegral_index_le_29363
    (k : ℕ) (hk2 : 2 ≤ k) (hkmax : k ≤ 10 ^ 14) :
    ∃ n, 1 ≤ n ∧ n ≤ 29363 ∧ ¬∃ z : ℤ, gobelSequence k 2 n = z

end

end MetaMathlibExt
