/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Proofs of ten conjectures from the OEIS

Statements from Sela Fried, "Proofs of Ten Conjectures From the OEIS", *Journal of Integer
Sequences* 29 (2026), Article 26.1.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Fried/fried21.html>).

Stated: Lemma 1 (a binomial identity), Theorem 2 (a diagonal coefficient), Theorem 3
(triangular numbers near squares along `⌊n√2⌋`), Theorem 5 (arithmetic progressions of `[n]`),
Theorem 6 (digit insertion and the digit sum), Theorem 7 (a binomial sum modulo `4`), Theorem 8
(the Bala-Somos parity conjectures from A067567 and A305123), Lemmas 9-11 and Theorem 12 (the
ceiling of `cot (π / (2m))`), Theorem 13 (A285273), Theorem 14 and Corollary 15 (cevians), and
Theorem 16 and Corollaries 17 and 21 (intersections and regions in the two-fan construction).
Theorems 18 and 20 and Corollary 19 stay blocked (see the source audit table).
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Rat.Floor
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Topology.Connected.Clopen
public import MathlibExt.Combinatorics.AP.Basic

namespace MetaMathlibExt

open MvPolynomial

@[expose] public section

/-- **Fried's alternating binomial identity.** For integers $a$ and $b$ let $\binom{a}{b}$ be the
binomial coefficient when $a, b \ge 0$ (so $0$ when $b > a$), and $0$ when $a < 0$ or $b < 0$.
For natural numbers $n$, $r$, $s$ with $r \le n$ and $s \le 2r$, with all arguments computed in
the integers,
$$\sum_{k=0}^{n} (-1)^k \binom{n}{k} \binom{2n-2r}{n-k} \binom{n-k}{n-2r+s}
\binom{2r-k-s}{n-s} = (-1)^n \binom{n}{2r-n} \binom{2n-2r}{n-s}.$$

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Lemma 1 (`jis-2026-26.1.8-lem-1`). -/
public theorem_wanted fried_alternating_binomial_identity (n r s : ℕ) (hr : r ≤ n)
    (hs : s ≤ 2 * r) :
    let C : ℤ → ℤ → ℤ := fun a b => if 0 ≤ a ∧ 0 ≤ b then (a.toNat.choose b.toNat : ℤ) else 0
    ∑ k ∈ Finset.range (n + 1),
        (-1) ^ k * C n k * C (2 * n - 2 * r) (n - k) * C (n - k) (n - 2 * r + s) *
          C (2 * r - k - s) (n - s) =
      (-1) ^ n * C n (2 * r - n) * C (2 * n - 2 * r) (n - s)

/-- **The Bala–Somos parity conjectures.** For a natural number $k$ let $p(k)$ be the number of
partitions of $k$. For natural numbers $m$ and $N$ let
$b_m(N) = \sum_{k=1}^{N} k^{2m+1} p(k) p(N-k)$ and $a(N) = \sum_{j=0}^{N} c(j)\, p(N-j)$, where
$c(0) = 0$ and $c(j) = \sum_{d \mid j,\ d \text{ odd}} (-1)^{j/d - 1}$ for $j \ge 1$. Then for all
$m \ge 1$ and $n \ge 1$: (a) if $n$ is odd, then $n$ divides $b_m(n)$; (b) $n$ divides $b_m(2n)$,
and $b_m(2n)/n$ is odd if and only if $n$ and $p(n)$ are both odd; (c) $a(n)$ is odd if and only
if $n$ and $p(n)$ are both odd; (d) twice the fractional part of the rational number $b_1(n)/n$
equals $1$ if and only if $n$ is even and $n/2$ and $p(n/2)$ are both odd.

Here $c(j)$ is the coefficient of $x^j$ in $\sum_{k \ge 1} x^{2k-1}/(1 + x^{2k-1})$, so $a(N)$ is
the coefficient of $x^N$ in $\bigl(\sum_{k \ge 1} x^{2k-1}/(1 + x^{2k-1})\bigr)
\prod_{k \ge 1} 1/(1 - x^k)$ (A305123). The paper calls the left side of (d) $c(n)$, a different
sequence from the coefficients $c(j)$ above.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 8 (`jis-2026-26.1.8-thm-8`). -/
public theorem_wanted bala_somos_partition_parity (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    let p : ℕ → ℕ := fun k => Fintype.card (Nat.Partition k)
    let b : ℕ → ℕ → ℕ := fun m n => ∑ k ∈ Finset.Icc 1 n, k ^ (2 * m + 1) * p k * p (n - k)
    let a : ℕ → ℤ := fun n => ∑ j ∈ Finset.range (n + 1),
      (∑ d ∈ j.divisors.filter Odd, (-1 : ℤ) ^ (j / d - 1)) * p (n - j)
    (Odd n → n ∣ b m n) ∧
      (n ∣ b m (2 * n) ∧ (Odd (b m (2 * n) / n) ↔ Odd n ∧ Odd (p n))) ∧
      (Odd (a n) ↔ Odd n ∧ Odd (p n)) ∧
      (2 * Int.fract ((b 1 n : ℚ) / n) = 1 ↔ Even n ∧ Odd (n / 2) ∧ Odd (p (n / 2)))

/-- **A diagonal coefficient equal to a signed Franel number.** For every $n \ge 0$, the
coefficient of $x^n y^n z^n$ in the integer polynomial
$(1 + x + y - z)^n (1 + x - y + z)^n (1 - x + y + z)^n$ equals
$(-1)^n \sum_{k=0}^{n} \binom{n}{k}^3$ (A000172).

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 2 (`jis-2026-26.1.8-thm-2`). -/
public theorem_wanted coeff_diag_trinomial_product_eq_franel (n : ℕ) :
    (((1 + X 0 + X 1 - X 2 : MvPolynomial (Fin 3) ℤ) ^ n * (1 + X 0 - X 1 + X 2) ^ n *
        (1 - X 0 + X 1 + X 2) ^ n).coeff (Finsupp.equivFunOnFinite.symm fun _ => n)) =
      (-1) ^ n * ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℤ)) ^ 3

/-- **Triangular numbers near squares along $\lfloor n\sqrt{2} \rfloor$.** For a natural number
$n$ let $a = \lfloor n\sqrt{2} \rfloor$ (A001951) and $T_a = a(a+1)/2$. Then some integer $k$
satisfies $|T_a - k^2| \le \lfloor a/2 \rfloor$; that is, the distance from $T_a$ to the nearest
perfect square is at most $\lfloor a/2 \rfloor$.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 3 (`jis-2026-26.1.8-thm-3`). -/
public theorem_wanted exists_sq_near_triangular_beatty_sqrt_two (n : ℕ) :
    let a : ℕ := ⌊(n : ℝ) * Real.sqrt 2⌋₊
    ∃ k : ℤ, |((a * (a + 1) / 2 : ℕ) : ℤ) - k ^ 2| ≤ (a / 2 : ℕ)

/-- **Counting arithmetic progressions in $\{1, \dots, n\}$.** For every integer $n \ge 1$, the
number of subsets $S \subseteq \{1, \dots, n\}$ with $|S| \ge 2$ that are arithmetic progressions,
that is, $S = \{a, a + d, \dots, a + (|S| - 1)d\}$ for some natural numbers $a$ and $d \ge 1$,
equals $\sum_{m=0}^{n-1} D(m)$, where $D(m) = \sum_{k=1}^{m} \lfloor m/k \rfloor$ (A078567,
A006218).

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 5 (`jis-2026-26.1.8-thm-5`). -/
public theorem_wanted ncard_arithProg_eq_sum_divisorSummatory (n : ℕ) (hn : 1 ≤ n) :
    {S : Finset ℕ | S ⊆ Finset.Icc 1 n ∧ 2 ≤ S.card ∧
        ∃ a d : ℕ, 1 ≤ d ∧ (S : Set ℕ).IsAPOfLengthWith S.card a d}.ncard =
      ∑ m ∈ Finset.range n, ∑ k ∈ Finset.Icc 1 m, m / k

/-- **Inserting a digit and the digit sum.** Let $n \ge 1$ have the $\ell$ decimal digits
$d_{\ell-1} \dots d_1 d_0$, so that $n = \sum_{j<\ell} d_j 10^j$. Let $S(n)$ be the set of the
numbers $\sum_{j<i} d_j 10^j + x \cdot 10^i + \sum_{i \le j < \ell} d_j 10^{j+1}$ with
$0 \le i \le \ell$ and $x \in \{0, \dots, 9\}$, excluding $i = \ell$ with $x = 0$: these are the
numbers obtained by inserting one decimal digit $x$ anywhere in the decimal expansion of $n$,
without creating a leading zero. Then the number of elements of $S(n)$ that are at most $10n$,
that is, the position of $10n$ when $S(n)$ is listed in increasing order, equals the digit sum
$d_0 + d_1 + \dots + d_{\ell-1}$ of $n$ (A007953).

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 6 (`jis-2026-26.1.8-thm-6`). -/
public theorem_wanted card_digitInsertion_le_ten_mul_eq_digitSum (n : ℕ) (hn : 1 ≤ n) :
    let L := Nat.digits 10 n
    let S : Finset ℕ := (((Finset.range (L.length + 1)) ×ˢ Finset.range 10).filter
        fun p => ¬(p.1 = L.length ∧ p.2 = 0)).image fun p => Nat.ofDigits 10 (L.insertIdx p.1 p.2)
    (S.filter (· ≤ 10 * n)).card = L.sum

/-- **Odd values of Bala's binomial sum are $1$ modulo $4$.** For a natural number $n$, let
$a(n) = \sum_{k=0}^{n} \binom{2n+1}{n+k+1} (-2)^k$. If $a(n)$ is odd, then $a(n) \equiv 1 \pmod 4$.

The paper's $a(n)$ is A026641 (the number of even-outdegree nodes in all ordered trees with $n$
edges); its proof works with this binomial sum (Bala's formula, display (13)), which is taken as
the definition here.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 7 (`jis-2026-26.1.8-thm-7`). -/
public theorem_wanted bala_binomial_sum_odd_imp_mod_four (n : ℕ)
    (h : Odd (∑ k ∈ Finset.range (n + 1), ((2 * n + 1).choose (n + k + 1) : ℤ) * (-2) ^ k)) :
    (∑ k ∈ Finset.range (n + 1), ((2 * n + 1).choose (n + k + 1) : ℤ) * (-2) ^ k) % 4 = 1

/-- **The ceiling of $\cot(\pi/(2m))$ rises in steps of $0$ or $1$.** For $m \ge 1$ let
$g(m) = \lceil \cot(\pi/(2m)) \rceil$. Then for every $m \ge 1$, $g(m) \le g(m+1)$ and
$g(m+1) - g(m) \in \{0, 1\}$; and for every integer $n \ge 1$, the number of $m \ge 1$ with
$g(m) = n$ is $1$ or $2$.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Lemma 9 (`jis-2026-26.1.8-lem-9`). -/
public theorem_wanted ceil_cot_pi_div_two_mul_steps :
    let g : ℕ → ℤ := fun m => ⌈Real.cot (Real.pi / (2 * m))⌉
    (∀ m, 1 ≤ m → g m ≤ g (m + 1)) ∧ (∀ m, 1 ≤ m → g (m + 1) - g m ∈ ({0, 1} : Set ℤ)) ∧
      ∀ n : ℕ, 1 ≤ n → {m : ℕ | 1 ≤ m ∧ g m = n}.ncard ∈ ({1, 2} : Set ℕ)

/-- **Counting $m$ with $\lceil \cot(\pi/(2m)) \rceil \le r$.** Let
$g(m) = \lceil \cot(\pi / (2m)) \rceil$ for integers $m \ge 1$, and call an integer $j$ a
singleton if exactly one integer $m \ge 1$ satisfies $g(m) = j$. For an integer $r \ge 1$, let
$s(r)$ be the number of singletons in $\{1, \dots, r\}$. Then the number of integers $m \ge 2$
with $g(m) \le r$ equals $2r - s(r)$.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Lemma 10 (`jis-2026-26.1.8-lem-10`). -/
public theorem_wanted ncard_ceil_cot_le_eq_two_mul_sub_singletons (r : ℕ) (hr : 1 ≤ r) :
    let g : ℕ → ℤ := fun m => ⌈Real.cot (Real.pi / (2 * m))⌉
    let mult : ℕ → ℕ := fun j => {m : ℕ | 1 ≤ m ∧ g m = j}.ncard
    {m : ℕ | 2 ≤ m ∧ g m ≤ r}.ncard = 2 * r - ((Finset.Icc 1 r).filter fun j => mult j = 1).card

/-- **Values taken once by the ceiling of $\cot(\pi/(2m))$.** For $m \ge 1$ let
$g(m) = \lceil \cot(\pi/(2m)) \rceil$. Let $r \ge 1$ and $m \ge 2$ be integers. Then $m$ is the
only integer $m' \ge 1$ with $g(m') = r$ if and only if $g(m-1) = r - 1$, $g(m) = r$ and
$g(m+1) = r + 1$.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Lemma 11 (`jis-2026-26.1.8-lem-11`). -/
public theorem_wanted ceil_cot_singleton_iff (r m : ℕ) (hr : 1 ≤ r) (hm : 2 ≤ m) :
    let g : ℕ → ℤ := fun m => ⌈Real.cot (Real.pi / (2 * m))⌉
    {m' : ℕ | 1 ≤ m' ∧ g m' = r} = {m} ↔
      g (m - 1) = (r : ℤ) - 1 ∧ g m = r ∧ g (m + 1) = (r : ℤ) + 1

/-- **Jeffery's conjecture on singletons of $\lfloor \cot(\pi/(2m)) \rfloor$.** Let
$f(m) = \lfloor \cot(\pi / (2m)) \rfloor$ for nonzero integers $m$. Let $a_1 < a_2 < \cdots$ list
the integers $k \ge 1$ for which exactly one integer $m \ge 2$ satisfies $f(-m) = -k$, and let
$b_1 < b_2 < \cdots$ list the integers $k \ge 2$ with $f(-k-1) < f(-k) < f(-k+1)$. Then for every
integer $n \ge 1$, $2a_n = b_n + n - 1$ (A223577, A223578).

If either list has fewer than $n$ terms, its $n$-th term is taken to be $0$.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 12 (`jis-2026-26.1.8-thm-12`). -/
public theorem_wanted jeffery_floor_cot_singletons (n : ℕ) (hn : 1 ≤ n) :
    let f : ℤ → ℤ := fun m => ⌊Real.cot (Real.pi / (2 * m))⌋
    let A : ℕ → Prop := fun k => 1 ≤ k ∧ ∃! m : ℕ, 2 ≤ m ∧ -(k : ℤ) = f (-(m : ℤ))
    let B : ℕ → Prop := fun k => 2 ≤ k ∧ f (-(k : ℤ) - 1) < f (-(k : ℤ)) ∧ f (-(k : ℤ)) < f (-(k : ℤ) + 1)
    2 * Nat.nth A (n - 1) = Nat.nth B (n - 1) + n - 1

/-- **Counting solutions of a repeating-decimal ratio equation.** For every natural number
$n \ge 1$, the number of natural numbers $x$ with $10^n \le x < 10^{n+1}$ for which there is a
natural number $k$ with $x \le k < 2x$ and $k / x = 1 + (x - 10^n) / (10^n - 1)$, computed in the
rationals, (OEIS A285273) equals $2^{\omega(10^n - 1)}$, where $\omega(m)$ is the number of
distinct prime factors of $m$.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 13 (`jis-2026-26.1.8-thm-13`). -/
public theorem_wanted ncard_repeating_decimal_ratio_eq_two_pow_omega (n : ℕ) (hn : 1 ≤ n) :
    {x : ℕ | 10 ^ n ≤ x ∧ x < 10 ^ (n + 1) ∧ ∃ k : ℕ, x ≤ k ∧ k < 2 * x ∧
        (k : ℚ) / x = 1 + ((x : ℚ) - 10 ^ n) / (10 ^ n - 1)}.ncard =
      2 ^ ArithmeticFunction.cardDistinctFactors (10 ^ n - 1)

/-- **Zakharov's conjecture on regions cut by cevians.** Let $A$, $B$, $C$ be affinely independent
points of $\mathbb{R}^2$ and $T$ the triangle they span; a cevian is a segment joining a vertex
of $T$ to a point of the open side opposite it. The regions cut out by cevians
$c_1, \dots, c_n$ are the connected components of the interior of $T$ minus
$c_1 \cup \dots \cup c_n$. Then for every $n \ge 0$, the maximum number of regions cut out by
$n$ cevians (not necessarily distinct) is $\lceil (n+1)(n+2)/3 \rceil$ (A007980).

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 14 (`jis-2026-26.1.8-thm-14`). -/
public theorem_wanted cevian_max_regions (A B C : ℝ × ℝ) (hT : AffineIndependent ℝ ![A, B, C])
    (n : ℕ) :
    let T := convexHull ℝ {A, B, C}
    let IsCevian : Set (ℝ × ℝ) → Prop := fun c =>
      (∃ P ∈ openSegment ℝ B C, c = segment ℝ A P) ∨ (∃ P ∈ openSegment ℝ C A, c = segment ℝ B P) ∨
        ∃ P ∈ openSegment ℝ A B, c = segment ℝ C P
    IsGreatest {r : ℕ | ∃ c : Fin n → Set (ℝ × ℝ), (∀ i, IsCevian (c i)) ∧
        Nat.card (ConnectedComponents ↥(interior T \ ⋃ i, c i)) = r}
      ⌈((n + 1) * (n + 2) : ℚ) / 3⌉₊

/-- **Zakharov's conjecture on intersection points of cevians.** Let $A$, $B$, $C$ be affinely
independent points of $\mathbb{R}^2$ and $T$ the triangle they span; a cevian is a segment
joining a vertex of $T$ to a point of the open side opposite it. Let $n \ge 0$ and let
$c_1, \dots, c_n$ be cevians such that the interior of $T$ minus $c_1 \cup \dots \cup c_n$ has
exactly $\lceil (n+1)(n+2)/3 \rceil$ connected components. Then the number of points of the
interior of $T$ that lie on $c_i$ and on $c_j$ for some $i \ne j$ is $\lfloor n^2/3 \rfloor$
(A000212).

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Corollary 15 (`jis-2026-26.1.8-cor-15`). -/
public theorem_wanted cevian_max_regions_intersection_count (A B C : ℝ × ℝ)
    (hT : AffineIndependent ℝ ![A, B, C]) (n : ℕ) :
    let T := convexHull ℝ {A, B, C}
    let IsCevian : Set (ℝ × ℝ) → Prop := fun c =>
      (∃ P ∈ openSegment ℝ B C, c = segment ℝ A P) ∨ (∃ P ∈ openSegment ℝ C A, c = segment ℝ B P) ∨
        ∃ P ∈ openSegment ℝ A B, c = segment ℝ C P
    ∀ c : Fin n → Set (ℝ × ℝ), (∀ i, IsCevian (c i)) →
      Nat.card (ConnectedComponents ↥(interior T \ ⋃ i, c i)) = ⌈((n + 1) * (n + 2) : ℚ) / 3⌉₊ →
        {X | X ∈ interior T ∧ ∃ i j, i ≠ j ∧ X ∈ c i ∧ X ∈ c j}.ncard = n ^ 2 / 3

/-- **Intersection points of two fans of rays.** Let $m, n \ge 1$, $P = (-1, 0)$ and
$Q = (1, 0)$. From $P$ draw the $m$ closed rays at angles $\pi - 2\pi s/m$ for $0 \le s < m$, and
from $Q$ the $n$ closed rays at angles $2\pi t/n$ for $0 \le t < n$. Let
$h = \lfloor (m - 1)/2 \rfloor$. Then the number of points that are $P$, $Q$, or a point off the
$x$-axis lying on a ray from $P$ and on a ray from $Q$ is
$2 \sum_{s=1}^{h} \lceil ns/m - 1/2 \rceil + 2$ for odd $n$ and
$2 \sum_{s=1}^{h} \lceil ns/m \rceil - 2h + 2$ for even $n$.

Off the $x$-axis these are exactly the points where two rays meet; on the axis, rays meet only at
$P$, $Q$ or along overlapping segments, which the paper does not count.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 16 (`jis-2026-26.1.8-thm-16`). -/
public theorem_wanted two_fan_ray_intersection_count (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    let rayP : ℕ → Set (ℝ × ℝ) := fun s => {X | ∃ r : ℝ, 0 ≤ r ∧
      X = (-1 + r * Real.cos (Real.pi - 2 * Real.pi * s / m), r * Real.sin (Real.pi - 2 * Real.pi * s / m))}
    let rayQ : ℕ → Set (ℝ × ℝ) := fun t => {X | ∃ r : ℝ, 0 ≤ r ∧
      X = (1 + r * Real.cos (2 * Real.pi * t / n), r * Real.sin (2 * Real.pi * t / n))}
    let pts : Set (ℝ × ℝ) := {(-1, 0), (1, 0)} ∪
      {X | X.2 ≠ 0 ∧ ∃ s < m, ∃ t < n, X ∈ rayP s ∧ X ∈ rayQ t}
    (pts.ncard : ℤ) =
      if Odd n then 2 * ∑ s ∈ Finset.Icc 1 ((m - 1) / 2), ⌈(n * s : ℚ) / m - 1 / 2⌉ + 2
      else 2 * ∑ s ∈ Finset.Icc 1 ((m - 1) / 2), ⌈(n * s : ℚ) / m⌉ - 2 * ((m - 1) / 2 : ℕ) + 2

/-- **Blomberg's conjecture on intersection points of two equal fans.** Let $n \ge 1$,
$P = (-1, 0)$ and $Q = (1, 0)$. From $P$ draw the $n$ closed rays at angles $\pi - 2\pi s/n$ for
$0 \le s < n$, and from $Q$ the $n$ closed rays at angles $2\pi t/n$ for $0 \le t < n$. Then the
number of points that are $P$, $Q$, or a point off the $x$-axis lying on a ray from $P$ and on a
ray from $Q$ is $(n^2 + 7)/4$ for odd $n$ and $(n^2 - 6n + 16)/4$ for even $n$ (A338042).

Off the $x$-axis these are exactly the points where two rays meet; on the axis, rays meet only at
$P$, $Q$ or along overlapping segments, which are not counted.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Corollary 17 (`jis-2026-26.1.8-cor-17`). -/
public theorem_wanted two_fan_ray_intersection_count_diag (n : ℕ) (hn : 1 ≤ n) :
    let rayP : ℕ → Set (ℝ × ℝ) := fun s => {X | ∃ r : ℝ, 0 ≤ r ∧
      X = (-1 + r * Real.cos (Real.pi - 2 * Real.pi * s / n), r * Real.sin (Real.pi - 2 * Real.pi * s / n))}
    let rayQ : ℕ → Set (ℝ × ℝ) := fun t => {X | ∃ r : ℝ, 0 ≤ r ∧
      X = (1 + r * Real.cos (2 * Real.pi * t / n), r * Real.sin (2 * Real.pi * t / n))}
    let pts : Set (ℝ × ℝ) := {(-1, 0), (1, 0)} ∪
      {X | X.2 ≠ 0 ∧ ∃ s < n, ∃ t < n, X ∈ rayP s ∧ X ∈ rayQ t}
    (pts.ncard : ℚ) = if Odd n then ((n : ℚ) ^ 2 + 7) / 4 else ((n : ℚ) ^ 2 - 6 * n + 16) / 4

/-- **Blomberg's conjecture on regions cut out by two equal fans.** Let $n \ge 3$, $P = (-1, 0)$
and $Q = (1, 0)$. From $P$ draw the $n$ closed rays at angles $\pi - 2\pi s/n$ for $0 \le s < n$,
and from $Q$ the $n$ closed rays at angles $2\pi t/n$ for $0 \le t < n$, and let $U$ be the union
of these rays. Then there is a real $R_0$ such that for every real $R \ge R_0$, if $K_R$ is the
convex hull of the points of $U$ on the circle $x^2 + y^2 = R^2$, the interior of $K_R$ minus $U$
has $(n^2 + 8n - 5)/4$ connected components for odd $n$ and $(n^2 + 2n)/4$ for even $n$
(A338041).

The points lie on the circle, so $K_R$ is the polygon joining consecutive points, and the
connected components are the regions into which the rays cut it.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Corollary 21 (`jis-2026-26.1.8-cor-21`). -/
public theorem_wanted two_fan_region_count_diag (n : ℕ) (hn : 3 ≤ n) :
    let rayP : ℕ → Set (ℝ × ℝ) := fun s => {X | ∃ r : ℝ, 0 ≤ r ∧
      X = (-1 + r * Real.cos (Real.pi - 2 * Real.pi * s / n), r * Real.sin (Real.pi - 2 * Real.pi * s / n))}
    let rayQ : ℕ → Set (ℝ × ℝ) := fun t => {X | ∃ r : ℝ, 0 ≤ r ∧
      X = (1 + r * Real.cos (2 * Real.pi * t / n), r * Real.sin (2 * Real.pi * t / n))}
    let rays : Set (ℝ × ℝ) := (⋃ s ∈ Finset.range n, rayP s) ∪ ⋃ t ∈ Finset.range n, rayQ t
    ∃ R₀ : ℝ, ∀ R ≥ R₀,
      (Nat.card (ConnectedComponents
          ↥(interior (convexHull ℝ {X | X.1 ^ 2 + X.2 ^ 2 = R ^ 2 ∧ X ∈ rays}) \ rays)) : ℚ) =
        if Odd n then ((n : ℚ) ^ 2 + 8 * n - 5) / 4 else ((n : ℚ) ^ 2 + 2 * n) / 4

end

end MetaMathlibExt
