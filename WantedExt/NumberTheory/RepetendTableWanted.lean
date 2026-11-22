/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Repetend tables

Statements from R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*,
INTEGERS 25 (2025), Article A26. The `j`-th base-`B` digit of `m/n` is written
`m * B ^ (j + 1) / n % B`; `E(L, n)` is the number of units of order `L` in `ZMod n`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Raising the base by multiples of $n$ shifts repetend digits linearly.** Let $m$ and $j$ be
natural numbers, $n \ge 1$ and $b \ge 2$. For a base $B$ write
$d_j(B) = \lfloor m B^{j+1} / n \rfloor \bmod B$ for the $j$-th base-$B$ digit of $m/n$. Then
there is a natural number $c < n$ such that $d_j(b + tn) = d_j(b) + tc$ for every natural number
$t$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Corollary 3 (`integers-2025-A26-cor-3`). -/
public theorem_wanted digit_add_mul_modulus_eq (m n b j : ℕ) (hn : 0 < n) (hb : 2 ≤ b) :
    ∃ c < n, ∀ t : ℕ,
      m * (b + t * n) ^ (j + 1) / n % (b + t * n) = m * b ^ (j + 1) / n % b + t * c

/-- **The number of units of order $L$ is a multiple of $\varphi(L)$.** For natural numbers
$n \ge 1$ and $L$, the number $E(L, n)$ of elements of order $L$ in the unit group
$(\mathbb{Z}/n\mathbb{Z})^\times$ is divisible by Euler's totient $\varphi(L)$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Corollary 4 (`integers-2025-A26-cor-4`). -/
public theorem_wanted totient_dvd_card_orderOf_eq (L n : ℕ) [NeZero n] : L.totient ∣
    (Finset.univ.filter fun u : (ZMod n)ˣ => orderOf u = L).card

/-- **Moduli with exactly $\varphi(L)$ units of even order $L$.** Let $n \ge 1$ and let $L \ge 2$
be even. If the number of elements of multiplicative order $L$ in
$(\mathbb{Z}/n\mathbb{Z})^\times$ equals $\varphi(L)$, then either $n = 4$ and $L = 2$, or $n = tq$
for some $t \in \{1, 2\}$ and some odd prime power $q$ with $L \mid \varphi(q)$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Corollary 5 (`integers-2025-A26-cor-5`). -/
public theorem_wanted card_orderOf_eq_totient_classification (L n : ℕ) [NeZero n] (hL0 : 0 < L)
    (hE : (Finset.univ.filter fun u : (ZMod n)ˣ => orderOf u = L).card = L.totient) (hL : 2 ∣ L) :
    (n = 4 ∧ L = 2) ∨
      ∃ t q : ℕ, (t = 1 ∨ t = 2) ∧ n = t * q ∧ Odd q ∧ IsPrimePow q ∧ L ∣ q.totient

/-- **Elements of order two modulo $n$.** For every $n \ge 1$, the number of elements of
multiplicative order $2$ in $(\mathbb{Z}/n\mathbb{Z})^\times$ is $2^k - 1$ for some natural
number $k$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Corollary 6 (`integers-2025-A26-cor-6`). -/
public theorem_wanted card_orderOf_eq_two_eq_two_pow_sub_one (n : ℕ) [NeZero n] :
    ∃ k : ℕ, (Finset.univ.filter fun u : (ZMod n)ˣ => orderOf u = 2).card = 2 ^ k - 1

/-- **Order-six elements modulo a power of a prime congruent to $1$ mod $6$.** Let $p$ be a prime
with $p \equiv 1 \pmod 6$, let $k \ge 1$ and put $n = p^k$. If $b \in \mathbb{Z}/n\mathbb{Z}$ has
multiplicative order $6$, then $b \ne 0$, $2b \ne 1$, $b \ne 1$, $b \ne -1$ and $b \ne 2$ in
$\mathbb{Z}/n\mathbb{Z}$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 16 (`integers-2025-A26-lem-16`). -/
public theorem_wanted orderOf_eq_six_ne_small_residues (p k : ℕ) (hp : p.Prime) (hp6 : p % 6 = 1)
    (hk : 0 < k) (b : ZMod (p ^ k))
    (hb : orderOf b = 6) :
    b ≠ 0 ∧ 2 * b ≠ 1 ∧ b ≠ 1 ∧ b ≠ -1 ∧ b ≠ 2

/-- **Sign balance for differences of shifted linear residues.** Let $p$ be prime, $j \ge 1$ and
$Q = p^j$. Let $g_1, g_2, f_1, f_2$ be natural numbers with $g_1, g_2 < Q$ and $f_1 \le f_2 < Q$
such that $p$ divides none of $g_1$, $g_2$, $g_2 - g_1$, and let $e_1, e_2$ be reals with
$0 < e_1 < e_2 < 1$. For natural $z$ put $c_i(z) = ((g_i z + f_i) \bmod Q) + e_i$ and
$d(z) = c_2(z) - c_1(z)$. Then (a) among $1 \le z \le Q - 1$, the number of $z$ with $d(z) > 0$
equals the number with $d(z) < 0$; and (b) if $f_1 \equiv 0 \pmod p$ or
$f_1 \equiv f_2 \pmod p$, the same holds among the $z$ with $1 \le z \le Q - 1$ and $p \nmid z$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Theorem 7 (`integers-2025-A26-thm-7`). -/
public theorem_wanted sign_balance_shifted_linear_residues (p j : ℕ) (hp : p.Prime) (hj : 0 < j)
    (g₁ g₂ f₁ f₂ : ℕ) (hg₁ : g₁ < p ^ j)
    (hg₂ : g₂ < p ^ j) (hf : f₁ ≤ f₂) (hf₂ : f₂ < p ^ j) (hcop₁ : ¬ p ∣ g₁)
    (hcop₂ : ¬ p ∣ g₂) (hcop : ¬ (p : ℤ) ∣ (g₂ : ℤ) - g₁) (e₁ e₂ : ℝ) (he₁ : 0 < e₁)
    (he : e₁ < e₂) (he₂ : e₂ < 1) :
    let d : ℕ → ℝ := fun z =>
      ((((g₂ * z + f₂) % p ^ j : ℕ) : ℝ) + e₂) - ((((g₁ * z + f₁) % p ^ j : ℕ) : ℝ) + e₁)
    ((Finset.Icc 1 (p ^ j - 1)).filter (fun z => 0 < d z)).card =
        ((Finset.Icc 1 (p ^ j - 1)).filter (fun z => d z < 0)).card ∧
      (f₁ % p = 0 ∨ f₁ % p = f₂ % p →
        ((Finset.Icc 1 (p ^ j - 1)).filter (fun z => ¬ p ∣ z ∧ 0 < d z)).card =
          ((Finset.Icc 1 (p ^ j - 1)).filter (fun z => ¬ p ∣ z ∧ d z < 0)).card)

/-- **Block sums of a repetend.** Let $B \ge 2$, $N$, $x < N$, $d \ge 1$ and $k \ge 1$ be natural
numbers, and let $a_i = \lfloor xB^{i+1}/N \rfloor \bmod B$ be the $i$-th base-$B$ digit of $x/N$.
Suppose $a_{i+dk} = a_i$ for every natural number $i$. Let
$S = \sum_{j<d} \sum_{i<k} a_{jk+i} B^{k-1-i}$ be the sum of the first $d$ blocks of $k$ digits,
each read as a base-$B$ number, and let $R = \sum_{j<d} (xB^{jk} \bmod N)$. Then
$SN = R(B^k - 1)$, and if $B^k - 1$ is coprime to $N$, then $B^k - 1$ divides $S$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Theorem 9 (`integers-2025-A26-thm-9`). -/
public theorem_wanted repetend_block_sum_eq (B N x d k : ℕ) (hB : 2 ≤ B) (hx : x < N) (hd : 0 < d)
    (hk : 0 < k)
    (hper : ∀ i, x * B ^ (i + d * k + 1) / N % B = x * B ^ (i + 1) / N % B) :
    let a : ℕ → ℕ := fun i => x * B ^ (i + 1) / N % B
    let S := ∑ j ∈ Finset.range d, ∑ i ∈ Finset.range k, a (j * k + i) * B ^ (k - 1 - i)
    let R := ∑ j ∈ Finset.range d, x * B ^ (j * k) % N
    S * N = R * (B ^ k - 1) ∧ (Nat.Coprime (B ^ k - 1) N → B ^ k - 1 ∣ S)


/-- **Long division of a proper fraction.** Let $m < n$ be natural numbers and $b \ge 1$. For
$j \ge 0$ let $c_j = m b^j \bmod n$ (the remainders of the long division of $m/n$ in base $b$) and
$r_j = \lfloor b c_j / n \rfloor$ (its digits). Then for every $k \ge 0$
$$\frac{m}{n} = \sum_{i<k} \frac{r_i}{b^{i+1}} + \frac{c_k}{n b^k},$$
and $r_j n = b c_j - c_{j+1}$ for every $j \ge 0$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 5 (`integers-2025-A26-lem-5`). -/
public theorem_wanted long_division_remainder_expansion (m n b : ℕ) (hmn : m < n) (hb : 0 < b) :
    let c : ℕ → ℕ := fun j => m * b ^ j % n
    let r : ℕ → ℕ := fun j => b * c j / n
    (∀ k : ℕ, (m : ℚ) / n =
      ∑ i ∈ Finset.range k, (r i : ℚ) / (b : ℚ) ^ (i + 1) + (c k : ℚ) / ((n : ℚ) * (b : ℚ) ^ k)) ∧
    ∀ j : ℕ, r j * n = b * c j - c (j + 1)

/-- **The last repetend digit is nonzero.** Let $n \ge 2$ and let $b \ge 2$ be prime to $n$,
with multiplicative order $L$ modulo $n$ (the repetend length of $1/n$ in base $b$). Then the
digit $\lfloor b^{(L-1)+1}/n \rfloor \bmod b$ of $1/n$ at position $L - 1$ is not $0$.

This holds for every such base, not only for the small bases $b < n$ that form the rows of the
paper's table.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 25 (`integers-2025-A26-lem-25`). -/
public theorem_wanted repetend_last_digit_ne_zero (n b : ℕ) (hn : 2 ≤ n) (hb : 2 ≤ b)
    (hcop : Nat.Coprime b n) :
    b ^ (orderOf (b : ZMod n) - 1 + 1) / n % b ≠ 0

/-- **A constraint on $b^2 + un$ between $2$ and $n - 2$.** Let $n$ and $b$ be natural numbers and
$u$ an integer, and put $b_2 = b^2 + un$. If $2 \le b_2 \le n - 2$, then $b \ne u + 1$.

The paper states this for a small base $b$; here $b$ is any natural number.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 31 (`integers-2025-A26-lem-31`). -/
public theorem_wanted ne_add_one_of_sq_add_mul_mem (n b : ℕ) (u : ℤ)
    (h2 : 2 ≤ (b : ℤ) ^ 2 + u * n) (hn : (b : ℤ) ^ 2 + u * n ≤ n - 2) :
    (b : ℤ) ≠ u + 1

/-- **Long-division remainders and small bases of prime order.** Let $n$ and $L$ be primes and
let $b$ be a natural number of multiplicative order $L$ modulo $n$. Suppose $m = 1$, or
$2 \le m \le n - 1$ and $m$ has multiplicative order $L$ modulo $n$. Then removing $1$ from the
set of remainders $\{m b^j \bmod n : 0 \le j < L\}$ leaves exactly the set of integers $a$ with
$2 \le a \le n - 1$ whose multiplicative order modulo $n$ is $L$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Corollary 2 (`integers-2025-A26-cor-2`). -/
public theorem_wanted long_division_remainders_erase_one_eq_small_bases (n L b m : ℕ)
    (hn : n.Prime) (hL : L.Prime) (hb : orderOf (b : ZMod n) = L)
    (hm : m = 1 ∨ (m ∈ Finset.Icc 2 (n - 1) ∧ orderOf (m : ZMod n) = L)) :
    ((Finset.range L).image fun j => m * b ^ j % n).erase 1 =
      (Finset.Icc 2 (n - 1)).filter fun a : ℕ => orderOf (a : ZMod n) = L

/-- **Small bases of order greater than two come in pairs.** For every natural number $n$ and
every $L > 2$, the number of integers $b$ with $1 \le b < n$ and $\gcd(b, n) = 1$ whose
multiplicative order modulo $n$ is $L$ is even.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 3 (`integers-2025-A26-lem-2`). -/
public theorem_wanted even_card_small_bases_orderOf (n L : ℕ) (hL : 2 < L) :
    Even ((Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = L).card

/-- **Repetend digits are symmetric under inverse indices.** Let $n, b, x, j, j'$ be natural
numbers and $L \ge 1$, and suppose $b$ has multiplicative order $L$ modulo $n$. For $y, c \ge 0$
put $b_y = b^y \bmod n$ and $r_{y,c} = \lfloor b_y^{c+1}/n \rfloor \bmod b_y$, the $c$-th digit
of $1/n$ in base $b_y$. If $\gcd(j, L) = 1$ and $j j' \equiv 1 \pmod L$, then
$r_{xj, j'} = r_{x, j}$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 6 (`integers-2025-A26-lem-6`). -/
public theorem_wanted repetend_digit_pow_mul_eq_of_mul_modEq_one (n b L x j j' : ℕ) (hL : 0 < L)
    (hb : orderOf (b : ZMod n) = L) (hj : Nat.Coprime j L) (hjj : j * j' ≡ 1 [MOD L]) :
    (b ^ (x * j) % n) ^ (j' + 1) / n % (b ^ (x * j) % n) = (b ^ x % n) ^ (j + 1) / n % (b ^ x % n)

/-- **Columns $j$ and $j^{-1}$ of a repetend table match.** Let $n$ and $L \ge 1$ be natural
numbers, and consider the repetend table of $1/n$ whose rows are the natural numbers $1 \le b < n$
coprime to $n$ of multiplicative order $L$ modulo $n$, and whose column $j$ holds the digits
$\lfloor b^{j+1}/n \rfloor \bmod b$. If $j$ and $j'$ are natural numbers with $j$ coprime to $L$,
$j^2 \not\equiv 1 \pmod L$ and $jj' \equiv 1 \pmod L$, then columns $j$ and $j'$ are equal as
multisets.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Theorem 2 (`integers-2025-A26-thm-2`). -/
public theorem_wanted repetend_column_eq_column_of_mul_modEq_one (n L j j' : ℕ) (hL : 0 < L)
    (hj : Nat.Coprime j L) (hjsq : ¬ j ^ 2 ≡ 1 [MOD L]) (hjj : j * j' ≡ 1 [MOD L]) :
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = L
    (B.val.map fun b => b ^ (j + 1) / n % b) = B.val.map fun b => b ^ (j' + 1) / n % b

/-- **Units modulo $L$ whose square is not $1$.** Let $L \ge 1$, let $e$ be the exponent of $2$
in $L$ and let $f$ be the number of distinct odd prime factors of $L$. Then the number of
integers $0 \le j < L$ with $\gcd(j, L) = 1$ and $j^2 \not\equiv 1 \pmod{L}$ is
$\varphi(L) - 2^{f + g(e)}$, where $g(e) = \max(0, \min(2, e - 1))$.

In the paper these $j$ index the Class A columns of a repetend table.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Theorem 2 (`integers-2025-A26-thm-2`). -/
public theorem_wanted card_coprime_not_sq_modEq_one (L : ℕ) (hL : 0 < L) :
    ((Finset.range L).filter fun j => Nat.Coprime j L ∧ ¬ j ^ 2 ≡ 1 [MOD L]).card =
      L.totient - 2 ^ ((L.primeFactors.filter Odd).card + min 2 (L.factorization 2 - 1))

/-- **The last column pairs a base with its inverse.** Let $n$ and $L \ge 1$ be natural numbers
and let $b < n$ have multiplicative order $L$ modulo $n$. Put $b' = b^{L-1} \bmod n$, the inverse
of $b$ modulo $n$. Then $b$ and $b'$ have the same digit in column $L - 1$:
$\lfloor b'^{L}/n \rfloor \bmod b' = \lfloor b^{L}/n \rfloor \bmod b$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Theorem 2 (`integers-2025-A26-thm-2`). -/
public theorem_wanted repetend_last_column_inv_eq (n L b : ℕ) (hL : 0 < L) (hbn : b < n)
    (hb : orderOf (b : ZMod n) = L) :
    (b ^ (L - 1) % n) ^ (L - 1 + 1) / n % (b ^ (L - 1) % n) = b ^ (L - 1 + 1) / n % b

/-- **Class B matched columns of repetend tables.** Let $a \ge 1$ and $L = 12a + 6$, let $p$ be a
prime with $p \equiv 1 \pmod L$, let $k \ge 1$ and $n = p^k$, and let $b$ be a natural number of
multiplicative order $L$ modulo $n$; write $b_i = b^i \bmod n$. Let the rows be the integers $c$
with $1 \le c < n$, $\gcd(c, n) = 1$ and multiplicative order $L$ modulo $n$, and let column $j$
be the multiset of the digits $\lfloor c^{j+1}/n \rfloor \bmod c$ over these rows. Then
$\lfloor (b_i + b_{i + L/3} + b_{i + 2L/3})/n \rfloor = 1$ for every $0 \le i < L$ coprime to $L$
if and only if columns $2a + 1$ and $4a + 2$ are equal and columns $8a + 4$ and $10a + 5$ are
equal.

The proportion conjectured in the source is not stated here.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Theorem 4 (`integers-2025-A26-thm-4`). -/
public theorem_wanted repetend_columns_match_iff_triple_sum_eq (p k a b : ℕ) (hp : p.Prime)
    (hk : 0 < k) (ha : 0 < a) (hpL : p % (12 * a + 6) = 1)
    (hb : orderOf (b : ZMod (p ^ k)) = 12 * a + 6) :
    let n := p ^ k
    let L := 12 * a + 6
    let B := (Finset.Ico 1 n).filter fun c => Nat.Coprime c n ∧ orderOf (c : ZMod n) = L
    let C : ℕ → Multiset ℕ := fun j => B.val.map fun c => c ^ (j + 1) / n % c
    (∀ i < L, Nat.Coprime i L →
        (b ^ i % n + b ^ (i + L / 3) % n + b ^ (i + 2 * L / 3) % n) / n = 1) ↔
      (C (2 * a + 1) = C (4 * a + 2) ∧ C (8 * a + 4) = C (10 * a + 5))

/-- **Differences of repetend digits.** Let $n \ge 1$ and $b$ be natural numbers with
$\gcd(b, n) = 1$. For $x, j \ge 0$ put $b_x = b^x \bmod n$ and
$r_{x,j} = \lfloor b_x^{j+1}/n \rfloor \bmod b_x$. Then for all natural numbers $y, m, d, e$,
$$n (r_{ym,e} - r_{y,d}) = b_{ym} b_{yme} - b_{ym(e+1)} - b_y b_{yd} + b_{y(d+1)}.$$

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 7 (`integers-2025-A26-lem-7`). -/
public theorem_wanted repetend_digit_sub_eq (n b y m d e : ℕ) (hn : 0 < n) (hb : Nat.Coprime b n) :
    let r : ℕ → ℕ → ℕ := fun x j => (b ^ x % n) ^ (j + 1) / n % (b ^ x % n)
    (n : ℤ) * ((r (y * m) e : ℤ) - r y d) =
      ((b ^ (y * m) % n : ℕ) : ℤ) * (b ^ (y * m * e) % n : ℕ) - (b ^ (y * m * (e + 1)) % n : ℕ) -
        ((b ^ y % n : ℕ) : ℤ) * (b ^ (y * d) % n : ℕ) + (b ^ (y * (d + 1)) % n : ℕ)

/-- **The $p$-adic valuation of $B^2 - B + 1$ for a base of order $6p^j$.** Let $p$ be a prime
with $p \equiv 1 \pmod 6$, let $i$ and $j$ be natural numbers with $j \ge 1$ and $i \ge 2j$, and
let $B$ be a natural number whose multiplicative order modulo $p^i$ is $6p^j$. Then the $p$-adic
valuation of $B^2 - B + 1$ is exactly $i - j$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 8 (`integers-2025-A26-lem-8`). -/
public theorem_wanted padicValNat_sq_sub_add_one_of_orderOf_eq (p i j B : ℕ) (hp : p.Prime)
    (hp6 : p % 6 = 1)
    (hj : 0 < j) (hij : 2 * j ≤ i) (hB : orderOf (B : ZMod (p ^ i)) = 6 * p ^ j) :
    padicValNat p (B ^ 2 - B + 1) = i - j

/-- **A power of $B$ equal to $B - 1$ modulo $p^i$.** Let $p$ be a prime with $p \equiv 1 \pmod 6$,
let $i$ and $j$ be natural numbers with $j \ge 1$ and $i \ge 2j$, put $n = p^i$ and $Q = p^j$, and
let $B < n$ be a natural number whose multiplicative order modulo $n$ is $6Q$. Let $z < 6Q$ be a
natural number with $z \equiv 2 \pmod 6$ such that $zB \equiv 1 \pmod Q$ or
$z \equiv 1 - B \pmod Q$. Then $B^z \bmod n = B - 1$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 9 (`integers-2025-A26-lem-9`). -/
public theorem_wanted pow_mod_eq_sub_one_of_orderOf_eq (p i j B z : ℕ) (hp : p.Prime)
    (hp6 : p % 6 = 1) (hj : 0 < j)
    (hij : 2 * j ≤ i) (hBn : B < p ^ i) (hB : orderOf (B : ZMod (p ^ i)) = 6 * p ^ j)
    (hzL : z < 6 * p ^ j) (hz6 : z ≡ 2 [MOD 6])
    (hzQ : z * B ≡ 1 [MOD p ^ j] ∨ (z : ℤ) ≡ 1 - B [ZMOD p ^ j]) :
    B ^ z % p ^ i = B - 1

/-- **Powers of a base of order $6p^j$ modulo $p^j$ depend only on the exponent modulo $6$.** Let
$p$ be a prime, let $i$ and $j$ be natural numbers with $j \ge 1$ and $i \ge 2j$, and let $b$ be a
natural number whose multiplicative order modulo $p^i$ is $6p^j$. If $y$ and $s$ are natural
numbers with $y \equiv s \pmod 6$, then $b^y \equiv b^s \pmod{p^j}$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 10 (`integers-2025-A26-lem-10`). -/
public theorem_wanted pow_modEq_pow_of_modEq_six (p i j b y s : ℕ) (hp : p.Prime) (hj : 0 < j)
    (hij : 2 * j ≤ i) (hb : orderOf (b : ZMod (p ^ i)) = 6 * p ^ j) (hys : y ≡ s [MOD 6]) :
    b ^ y ≡ b ^ s [MOD p ^ j]

/-- **Powers of $b^y \bmod p^i$ that differ by one.** Let $p$ be a prime with $p \equiv 1 \pmod 6$,
let $i$ and $j$ be natural numbers with $j \ge 1$ and $i \ge 2j$, put $n = p^i$ and $Q = p^j$, and
let $b$ be a natural number whose multiplicative order modulo $n$ is $6Q$. Let $f \in \{1, -1\}$,
let $y$ be a natural number with $y \equiv s \pmod 6$ for some $s \in \{1, -1\}$, and put $e = 1$
if $sf = 1$ and $e = 5$ if $sf = -1$. Let $d$ be a natural number with $d \equiv 2f \pmod 6$, and
let $k < 6Q$ be a natural number with $k \equiv f \pmod 6$ and $k \equiv b^e d \pmod Q$. Then, with
$B = b^y \bmod n$, we have $B^k \bmod n = (B^d \bmod n) + 1$.

Here $b^5$ stands for $b^{-1}$ modulo $Q$, as $b^6 \equiv 1 \pmod Q$, so $b^e$ is $b^{sf}$ modulo
$Q$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 11 (`integers-2025-A26-lem-11`). -/
public theorem_wanted pow_mod_eq_pow_mod_add_one_of_crt (p i j b y d k : ℕ) (f : ℤ) (hp : p.Prime)
    (hp6 : p % 6 = 1) (hj : 0 < j) (hij : 2 * j ≤ i) (hb : orderOf (b : ZMod (p ^ i)) = 6 * p ^ j)
    (hf : f = 1 ∨ f = -1) (hy : y % 6 = 1 ∨ y % 6 = 5) (hd : (d : ℤ) ≡ 2 * f [ZMOD 6])
    (hk : k < 6 * p ^ j) (hk6 : (k : ℤ) ≡ f [ZMOD 6])
    (hkQ : k ≡ b ^ (if (y % 6 = 1 ↔ f = 1) then 1 else 5) * d [MOD p ^ j]) :
    (b ^ y % p ^ i) ^ k % p ^ i = (b ^ y % p ^ i) ^ d % p ^ i + 1

/-- **Relations among the powers $B^{zp^j} \bmod p^i$ for a base of order $6p^j$.** Let $p$ be a
prime with $p \equiv 1 \pmod 6$, let $i$ and $j$ be natural numbers, put $n = p^i$ and $Q = p^j$,
and let $B$ be a natural number whose multiplicative order modulo $n$ is $6Q$. Write
$B_z = B^z \bmod n$. Then $B_{2Q} = B_Q - 1$, $B_{4Q} = B_{5Q} - 1$, $B_Q + B_{5Q} = n + 1$ and
$B_{3Q} = n - 1$; moreover $Q^2 \equiv Q \pmod{6Q}$.

Since $B^{6Q} \equiv 1 \pmod n$, the residues $B_{5Q}$ and $B_{4Q}$ are those of $B^{-Q}$ and
$B^{-2Q}$. The paper assumes $j \ge 1$ and $i \ge 2j$; these are not needed here.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 13 (`integers-2025-A26-lem-13`). -/
public theorem_wanted pow_mod_relations_of_orderOf_eq_six_mul (p i j B : ℕ) (hp : p.Prime)
    (hp6 : p % 6 = 1)
    (hB : orderOf (B : ZMod (p ^ i)) = 6 * p ^ j) :
    let n := p ^ i
    let Q := p ^ j
    B ^ (2 * Q) % n = B ^ Q % n - 1 ∧ B ^ (4 * Q) % n = B ^ (5 * Q) % n - 1 ∧
      B ^ Q % n + B ^ (5 * Q) % n = n + 1 ∧ B ^ (3 * Q) % n = n - 1 ∧ Q ^ 2 ≡ Q [MOD 6 * Q]

/-- **Digit differences for a base of order $6p^j$ modulo $p^i$.** Let $p$ be a prime with
$p \equiv 1 \pmod 6$, let $i$ and $j$ be natural numbers, and put $n = p^i$ and $Q = p^j$. Let
$B < n$ be a natural number whose multiplicative order modulo $n$ is $6Q$, let $f \in \{1, -1\}$,
and let $d$ and $e$ be natural numbers with $d \equiv 2fQ \pmod{6Q}$ and $e \equiv fQ \pmod{6Q}$.
For natural $s$ write $r_s = \lfloor B^{s+1}/n \rfloor \bmod B$ for the $s$-th base-$B$ digit of
$1/n$, and put $D = n(r_e - r_d)$. Then $D = B + (B^{d+1} \bmod n) - (B^{e+1} \bmod n)$, and
$D = 0$ or $D = n$.

The statement is made for all natural numbers $i$ and $j$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 14 (`integers-2025-A26-lem-14`). -/
public theorem_wanted repetend_digit_sub_mem_zero_n (p i j B d e : ℕ) (f : ℤ) (hp : p.Prime)
    (hp6 : p % 6 = 1)
    (hBn : B < p ^ i) (hB : orderOf (B : ZMod (p ^ i)) = 6 * p ^ j) (hf : f = 1 ∨ f = -1)
    (hd : (d : ℤ) ≡ 2 * f * p ^ j [ZMOD 6 * p ^ j]) (he : (e : ℤ) ≡ f * p ^ j [ZMOD 6 * p ^ j]) :
    let n := p ^ i
    let D : ℤ := (n : ℤ) * (((B ^ (e + 1) / n % B : ℕ) : ℤ) - (B ^ (d + 1) / n % B : ℕ))
    D = B + (B ^ (d + 1) % n : ℕ) - (B ^ (e + 1) % n : ℕ) ∧ (D = 0 ∨ D = n)

/-- **Class C matched columns of repetend tables.** Let $p$ be a prime with $p \equiv 1 \pmod 6$,
let $j \ge 1$ and $i \ge 2j$, and put $n = p^i$, $Q = p^j$ and $L = 6Q$. Let $b$ be a natural
number of multiplicative order $L$ modulo $n$, and let $d, e < L$ be natural numbers with
$d \equiv b^2 \pmod Q$, $e \equiv b^4 \pmod Q$ and $d \equiv e \equiv 4 \pmod 6$. Let the rows be
the integers $c$ with $1 \le c < n$, $\gcd(c, n) = 1$ and multiplicative order $L$ modulo $n$, and
let column $s$ be the multiset of the digits $\lfloor c^{s+1}/n \rfloor \bmod c$ over these rows.
Then columns $d$ and $e$ are equal.

Theorem 6 of the source also says when the digit difference between these columns is $0$; that
clause is not stated here.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Theorem 6 (`integers-2025-A26-thm-6`). -/
public theorem_wanted repetend_columns_eq_of_crt_sq (p i j b d e : ℕ) (hp : p.Prime)
    (hp6 : p % 6 = 1) (hj : 0 < j)
    (hij : 2 * j ≤ i) (hb : orderOf (b : ZMod (p ^ i)) = 6 * p ^ j) (hdL : d < 6 * p ^ j)
    (heL : e < 6 * p ^ j) (hdQ : d ≡ b ^ 2 [MOD p ^ j]) (heQ : e ≡ b ^ 4 [MOD p ^ j])
    (hd6 : d ≡ 4 [MOD 6]) (he6 : e ≡ 4 [MOD 6]) :
    let n := p ^ i
    let B := (Finset.Ico 1 n).filter fun c => Nat.Coprime c n ∧ orderOf (c : ZMod n) = 6 * p ^ j
    (B.val.map fun c => c ^ (d + 1) / n % c) = B.val.map fun c => c ^ (e + 1) / n % c

/-- **Repetend tables of length at most $2$ have no matched columns.** Let $n$ and $L \le 2$ be
natural numbers, let the rows be the integers $b$ with $1 \le b < n$, $\gcd(b, n) = 1$ and
multiplicative order $L$ modulo $n$, and let column $j$ be the multiset of the digits
$\lfloor b^{j+1}/n \rfloor \bmod b$ over these rows. If there is at least one row, then for all
distinct $i, j < L$ columns $i$ and $j$ are different.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 26 (`integers-2025-A26-lem-26`). -/
public theorem_wanted repetend_columns_ne_of_le_two (n L : ℕ) (hL : L ≤ 2) :
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = L
    B.Nonempty → ∀ i < L, ∀ j < L, i ≠ j →
      (B.val.map fun b => b ^ (i + 1) / n % b) ≠ B.val.map fun b => b ^ (j + 1) / n % b

/-- **Repetend tables with one or three rows have no matched columns.** For natural numbers $n$
and $L$, let the rows be the integers $b$ with $1 \le b < n$, $\gcd(b, n) = 1$ and multiplicative
order $L$ modulo $n$, and let column $j$ be the multiset of the digits
$\lfloor b^{j+1}/n \rfloor \bmod b$ over these rows. If there are exactly one or exactly three
rows, then for all distinct $i, j < L$ columns $i$ and $j$ are different.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 27 (`integers-2025-A26-lem-27`). -/
public theorem_wanted repetend_columns_ne_of_card_eq_one_or_three (n L : ℕ) :
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = L
    (B.card = 1 ∨ B.card = 3) → ∀ i < L, ∀ j < L, i ≠ j →
      (B.val.map fun b => b ^ (i + 1) / n % b) ≠ B.val.map fun b => b ^ (j + 1) / n % b

/-- **Matching columns of a two-row repetend table.** Let $n$ and $L$ be natural numbers and let
$B$ be the set of integers $c$ with $1 \le c < n$, $\gcd(c, n) = 1$ and multiplicative order $L$
modulo $n$. For $c \in B$ and $k \ge 0$ let $r_k(c) = \lfloor c^{k+1}/n \rfloor \bmod c$, and let
$C_k$ be the multiset of the $r_k(c)$ over $c \in B$. Suppose $B$ has exactly two elements, $b$
and $b' \ne b$, and put $D_k = r_k(b') - r_k(b)$. Then for all $i, j \ge 0$ with $C_i = C_j$,
$D_i = D_j$ or $D_i = -D_j$, and the sum of the elements of $C_i$ equals that of $C_j$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 28 (`integers-2025-A26-lem-28`). -/
public theorem_wanted repetend_digit_diff_of_columns_eq (n L b b' i j : ℕ) :
    let B := (Finset.Ico 1 n).filter fun c => Nat.Coprime c n ∧ orderOf (c : ZMod n) = L
    let C : ℕ → Multiset ℕ := fun k => B.val.map fun c => c ^ (k + 1) / n % c
    let D : ℕ → ℤ := fun k => ((b' ^ (k + 1) / n % b' : ℕ) : ℤ) - (b ^ (k + 1) / n % b : ℕ)
    B.card = 2 → b ∈ B → b' ∈ B → b ≠ b' → C i = C j →
      (D i = D j ∨ D i = -D j) ∧ (C i).sum = (C j).sum

/-- **Half-period symmetry of the repetend of $1/n$.** Let $n$ be a natural number whose unit
group $(\mathbb{Z}/n\mathbb{Z})^\times$ is cyclic, let $L > 0$ be even, and let $b < n$ be a
natural number whose multiplicative order modulo $n$ is $L$. For natural numbers $m$ write
$b_m = b^m \bmod n$ and $r_m = \lfloor b^{m+1}/n \rfloor \bmod b$, the $m$-th base-$b$ digit of
$1/n$. Then for every natural number $j$ we have $b_{j+L/2} = n - b_j$ and
$r_j + r_{j+L/2} = r_{L/2}$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 29 (`integers-2025-A26-lem-29`). -/
public theorem_wanted pow_add_half_mod_eq_and_digit_add (n L b j : ℕ) [IsCyclic (ZMod n)ˣ]
    (hL : Even L) (hL0 : 0 < L) (hbn : b < n) (hb : orderOf (b : ZMod n) = L) :
    b ^ (j + L / 2) % n = n - b ^ j % n ∧
      b ^ (j + 1) / n % b + b ^ (j + L / 2 + 1) / n % b = b ^ (L / 2 + 1) / n % b

/-- **Two-row repetend tables of length $3$ have no matched columns.** For a natural number $n$,
let the rows be the integers $b$ with $1 \le b < n$, $\gcd(b, n) = 1$ and multiplicative order $3$
modulo $n$, and let column $j$ be the multiset of the digits $\lfloor b^{j+1}/n \rfloor \bmod b$
over these rows. If there are exactly two rows, then for all distinct $i, j < 3$ columns $i$ and
$j$ are different.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 30 (`integers-2025-A26-lem-30`). -/
public theorem_wanted repetend_columns_ne_of_card_two_of_three (n : ℕ) :
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = 3
    B.card = 2 → ∀ i < 3, ∀ j < 3, i ≠ j →
      (B.val.map fun b => b ^ (i + 1) / n % b) ≠ B.val.map fun b => b ^ (j + 1) / n % b

/-- **Two-row repetend tables of length $4$ have no matched columns.** For a natural number $n$,
let the rows be the integers $b$ with $1 \le b < n$, $\gcd(b, n) = 1$ and multiplicative order $4$
modulo $n$, and let column $j$ be the multiset of the digits $\lfloor b^{j+1}/n \rfloor \bmod b$
over these rows. If there are exactly two rows, then for all distinct $i, j < 4$ columns $i$ and
$j$ are different.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 32 (`integers-2025-A26-lem-32`). -/
public theorem_wanted repetend_columns_ne_of_card_two_of_four (n : ℕ) :
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = 4
    B.card = 2 → ∀ i < 4, ∀ j < 4, i ≠ j →
      (B.val.map fun b => b ^ (i + 1) / n % b) ≠ B.val.map fun b => b ^ (j + 1) / n % b

/-- **Moduli with exactly two small bases of order six.** Let $n$ be a natural number. If exactly
two integers $b$ with $1 \le b < n$ and $\gcd(b, n) = 1$ have multiplicative order $6$ modulo $n$,
then either $n = 3^k t \ge 9$ for some natural number $k$ and some $t \in \{1, 2\}$, or
$n = p^k t$ for some prime $p \equiv 1 \pmod 6$, some $k \ge 1$ and some $t \in \{1, 2\}$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 33 (`integers-2025-A26-lem-33`). -/
public theorem_wanted eq_of_card_small_bases_orderOf_six_eq_two (n : ℕ)
    (h : ((Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = 6).card = 2) :
    (∃ k t : ℕ, (t = 1 ∨ t = 2) ∧ n = 3 ^ k * t ∧ 9 ≤ n) ∨
      ∃ p k t : ℕ, p.Prime ∧ p % 6 = 1 ∧ 0 < k ∧ (t = 1 ∨ t = 2) ∧ n = p ^ k * t

/-- **Order-$6$ repetend tables of $3^k t$ have no matched columns.** Let $k \ge 2$ and
$t \in \{1, 2\}$, and put $n = 3^k t$. Let the rows be the integers $b$ with $1 \le b < n$,
$\gcd(b, n) = 1$ and multiplicative order $6$ modulo $n$, and let column $j$ be the multiset of
the digits $\lfloor b^{j+1}/n \rfloor \bmod b$ over these rows. Then for all distinct $i, j < 6$
columns $i$ and $j$ are different.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 34 (`integers-2025-A26-lem-34`). -/
public theorem_wanted repetend_columns_ne_of_three_pow_of_six (k t : ℕ) (hk : 2 ≤ k)
    (ht : t = 1 ∨ t = 2) :
    let n := 3 ^ k * t
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = 6
    ∀ i < 6, ∀ j < 6, i ≠ j →
      (B.val.map fun b => b ^ (i + 1) / n % b) ≠ B.val.map fun b => b ^ (j + 1) / n % b

/-- **Powers of a base of order $6$ modulo $tp^k$.** Let $p$ be a prime with $p \equiv 1 \pmod 6$,
let $k \ge 1$ and $t \in \{1, 2\}$ be natural numbers, and put $n = tp^k$. Let $b_1 < n$ be a
natural number whose multiplicative order modulo $n$ is $6$, write $b_m = b_1^m \bmod n$, and put
$H = 0$ if $t = 1$, $H = p^k$ if $t = 2$ and $b_1 < p^k$, and $H = -p^k$ if $t = 2$ and
$b_1 \ge p^k$. Then $b_2 = b_1 - 1 + H$, $b_3 = n - 1$, $b_4 = n - b_1$ and
$b_5 = n - b_1 + 1 - H$, and there is an integer $u$ with $b_1^2 = un + b_1 - 1 + H$,
$b_2^2 = un - b_1 + (H + 2b_1 - 1)H$ and $b_1 b_2 = un - 1 + (b_1 + 1)H$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 35 (`integers-2025-A26-lem-35`). -/
public theorem_wanted pow_mod_eqs_of_orderOf_eq_six (p k t b₁ : ℕ) (hp : p.Prime) (hp6 : p % 6 = 1)
    (hk : 0 < k) (ht : t = 1 ∨ t = 2) (hb₁ : b₁ < t * p ^ k)
    (hb : orderOf (b₁ : ZMod (t * p ^ k)) = 6) :
    let n := t * p ^ k
    let H : ℤ := if t = 1 then 0 else if b₁ < p ^ k then (p ^ k : ℕ) else -((p ^ k : ℕ) : ℤ)
    let c : ℕ → ℤ := fun j => ((b₁ ^ j % n : ℕ) : ℤ)
    ∃ u : ℤ, c 2 = b₁ - 1 + H ∧ c 3 = n - 1 ∧ c 4 = n - b₁ ∧ c 5 = n - b₁ + 1 - H ∧
      (b₁ : ℤ) ^ 2 = u * n + b₁ - 1 + H ∧ c 2 ^ 2 = u * n - b₁ + (H + 2 * b₁ - 1) * H ∧
      b₁ * c 2 = u * n - 1 + (b₁ + 1) * H

/-- **Digit differences between the rows $b_1$ and $b_1^5$ of the order-$6$ table.** Let
$p \equiv 1 \pmod 6$ be prime, $k \ge 1$, $t \in \{1, 2\}$ and $n = t p^k$, and let $b_1 < n$
have multiplicative order $6$ modulo $n$. Put $H = 0$ if $t = 1$, $H = p^k$ if $t = 2$ and
$b_1 < p^k$, and $H = -p^k$ if $t = 2$ and $b_1 \ge p^k$. Let $b_5 = b_1^5 \bmod n$ and, for
$i \ge 0$, $D_i = r_i(b_5) - r_i(b_1)$, where $r_i(c) = \lfloor c^{i+1}/n \rfloor \bmod c$. Then
$D_0 = D_5 = 0$, $D_2 = n - b_1 - (b_1^2 \bmod n) = 1 - 2 b_1 + n - H$,
$n D_1 = (n - H) D_2$, $D_3 = D_2$ and $n D_4 = H D_2$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 36 (`integers-2025-A26-lem-36`). -/
public theorem_wanted repetend_digit_diffs_of_orderOf_eq_six (p k t b₁ : ℕ) (hp : p.Prime)
    (hp6 : p % 6 = 1) (hk : 0 < k) (ht : t = 1 ∨ t = 2) (hb₁ : b₁ < t * p ^ k)
    (hb : orderOf (b₁ : ZMod (t * p ^ k)) = 6) :
    let n := t * p ^ k
    let H : ℤ := if t = 1 then 0 else if b₁ < p ^ k then (p ^ k : ℕ) else -((p ^ k : ℕ) : ℤ)
    let b₅ := b₁ ^ 5 % n
    let D : ℕ → ℤ := fun i => ((b₅ ^ (i + 1) / n % b₅ : ℕ) : ℤ) - (b₁ ^ (i + 1) / n % b₁ : ℕ)
    D 0 = 0 ∧ D 5 = 0 ∧ D 2 = n - b₁ - (b₁ ^ 2 % n : ℕ) ∧ D 2 = 1 - 2 * b₁ + n - H ∧
      n * D 1 = (n - H) * D 2 ∧ D 3 = D 2 ∧ n * D 4 = H * D 2

/-- **Columns $0$ and $5$ of the order-$6$ repetend table of $t p^k$ differ.** Let $p$ be a prime
with $p \equiv 1 \pmod 6$, let $k \ge 1$ and $t \in \{1, 2\}$, and put $n = t p^k$. Let the rows be
the integers $b$ with $1 \le b < n$, $\gcd(b, n) = 1$ and multiplicative order $6$ modulo $n$, and
let column $j$ be the multiset of the digits $\lfloor b^{j+1}/n \rfloor \bmod b$ over these rows.
Then columns $0$ and $5$ are different.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 37 (`integers-2025-A26-lem-37`). -/
public theorem_wanted repetend_column_zero_ne_five (p k t : ℕ) (hp : p.Prime) (hp6 : p % 6 = 1)
    (hk : 0 < k) (ht : t = 1 ∨ t = 2) :
    let n := t * p ^ k
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = 6
    (B.val.map fun b => b ^ (0 + 1) / n % b) ≠ B.val.map fun b => b ^ (5 + 1) / n % b

/-- **Columns $1$, $2$, $3$ of the order-$6$ repetend table differ from columns $0$ and $5$.** Let
$p \equiv 1 \pmod 6$ be prime, $k \ge 1$, $t \in \{1, 2\}$ and $n = t p^k$, and let $B$ be the set
of integers $b$ with $1 \le b < n$, $\gcd(b, n) = 1$ and multiplicative order $6$ modulo $n$. For
$c \ge 0$ let column $c$ be the multiset of the digits $\lfloor b^{c+1}/n \rfloor \bmod b$ over
$b \in B$. Then for every $i \in \{1, 2, 3\}$ and $j \in \{0, 5\}$, columns $i$ and $j$ are
different multisets.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 38 (`integers-2025-A26-lem-38`). -/
public theorem_wanted repetend_columns_one_to_three_ne_zero_five (p k t : ℕ) (hp : p.Prime)
    (hp6 : p % 6 = 1) (hk : 0 < k) (ht : t = 1 ∨ t = 2) :
    let n := t * p ^ k
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = 6
    ∀ i ∈ ({1, 2, 3} : Finset ℕ), ∀ j ∈ ({0, 5} : Finset ℕ),
      (B.val.map fun b => b ^ (i + 1) / n % b) ≠ B.val.map fun b => b ^ (j + 1) / n % b

/-- **Column $4$ of the order-$6$ repetend table of $t p^k$ differs from columns $0$ and $5$.**
Let $p$ be a prime with $p \equiv 1 \pmod 6$, let $k \ge 1$ and $t \in \{1, 2\}$, and put
$n = t p^k$. Let the rows be the integers $b$ with $1 \le b < n$, $\gcd(b, n) = 1$ and
multiplicative order $6$ modulo $n$, and let column $j$ be the multiset of the digits
$\lfloor b^{j+1}/n \rfloor \bmod b$ over these rows. Then column $4$ is different from column $0$
and from column $5$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 39 (`integers-2025-A26-lem-39`). -/
public theorem_wanted repetend_column_four_ne_zero_five (p k t : ℕ) (hp : p.Prime)
    (hp6 : p % 6 = 1) (hk : 0 < k) (ht : t = 1 ∨ t = 2) :
    let n := t * p ^ k
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = 6
    ∀ j ∈ ({0, 5} : Finset ℕ),
      (B.val.map fun b => b ^ (4 + 1) / n % b) ≠ B.val.map fun b => b ^ (j + 1) / n % b

/-- **Columns $1$ to $4$ of the order-$6$ repetend table of $t p^k$ are pairwise different.** Let
$p$ be a prime with $p \equiv 1 \pmod 6$, let $k \ge 1$ and $t \in \{1, 2\}$, and put $n = t p^k$.
Let the rows be the integers $b$ with $1 \le b < n$, $\gcd(b, n) = 1$ and multiplicative order $6$
modulo $n$, and let column $j$ be the multiset of the digits $\lfloor b^{j+1}/n \rfloor \bmod b$
over these rows. Then for all distinct $i, j \in \{1, 2, 3, 4\}$ columns $i$ and $j$ are
different.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 40 (`integers-2025-A26-lem-40`). -/
public theorem_wanted repetend_columns_one_to_four_pairwise_ne (p k t : ℕ) (hp : p.Prime)
    (hp6 : p % 6 = 1) (hk : 0 < k) (ht : t = 1 ∨ t = 2) :
    let n := t * p ^ k
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = 6
    ∀ i ∈ Finset.Icc 1 4, ∀ j ∈ Finset.Icc 1 4, i ≠ j →
      (B.val.map fun b => b ^ (i + 1) / n % b) ≠ B.val.map fun b => b ^ (j + 1) / n % b

/-- **Repetend tables with at most three rows have no matched columns.** For natural numbers $n$
and $L$, let the rows be the integers $b$ with $1 \le b < n$, $\gcd(b, n) = 1$ and multiplicative
order $L$ modulo $n$, and let column $j$ be the multiset of the digits
$\lfloor b^{j+1}/n \rfloor \bmod b$ over these rows. If there are at least one and at most three
rows, then for all distinct $i, j < L$ columns $i$ and $j$ are different.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Theorem 12 (`integers-2025-A26-thm-12`). -/
public theorem_wanted repetend_columns_ne_of_card_le_three (n L : ℕ) :
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = L
    1 ≤ B.card → B.card ≤ 3 → ∀ i < L, ∀ j < L, i ≠ j →
      (B.val.map fun b => b ^ (i + 1) / n % b) ≠ B.val.map fun b => b ^ (j + 1) / n % b

/-- **Tail bound for sums of inverse powers.** For natural numbers $m \ge 2$ and $s \ge 1$,
$\sum_{n = s+1}^{\infty} n^{-m} < \dfrac{1}{(m-1)\, s^{m-1}}$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 42 (`integers-2025-A26-lem-42`). -/
public theorem_wanted tsum_inv_pow_succ_lt (m s : ℕ) (hm : 2 ≤ m) (hs : 0 < s) :
    ∑' k : ℕ, (((k + s + 1 : ℕ) : ℝ) ^ m)⁻¹ < (((m - 1 : ℕ) : ℝ) * (s : ℝ) ^ (m - 1))⁻¹

end

end MetaMathlibExt
