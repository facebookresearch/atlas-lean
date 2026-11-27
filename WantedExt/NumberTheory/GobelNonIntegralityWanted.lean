/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Hull
public import MathlibExt.NumberTheory.ArithmeticBilliardsRotatedRectangle
public import MathlibExt.NumberTheory.GobelBSequence
public import MathlibExt.NumberTheory.OddMultiplePrimeHalfSets
public import WantedExt.NumberTheory.GobelSequenceWanted
public import MathlibExt.NumberTheory.GobelNonIntegralityDiagonalIsZigzagBelowGobelResidueWalkOfOdd

/-!
# Non-integrality of `(k, l)`-Göbel sequences (statements)

Statement-only targets from Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of
the (k, l)-Göbel Sequences*. The theorem `diagonal_isZigzagBelow_gobelResidueWalk_of_odd` from
this paper is proved in
`MathlibExt.NumberTheory.GobelNonIntegralityDiagonalIsZigzagBelowGobelResidueWalkOfOdd`. The
sequence `g_{k,l}` is the existing `gobelSequence k l`;
`x ∈ ℤ_(p)` is `0 ≤ padicValRat p x`, as in `GobelSequenceWanted`. The thresholds `N_{k,l}`
are not defined; claims about them are stated directly through `gobelSequence`.
-/

namespace MetaMathlibExt

@[expose] public section

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
