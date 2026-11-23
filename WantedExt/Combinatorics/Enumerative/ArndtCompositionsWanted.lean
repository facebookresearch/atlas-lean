/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Arndt compositions with restricted parts

Statements from Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez,
"Arndt Compositions with Restricted Parts, Palindromes, and Colored Variants", *Journal of
Integer Sequences* 28 (2025), Article 25.3.6
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Ramirez/ramirez19.html>).

An Arndt composition is a composition `(σ₁, σ₂, …, σ_k)` with `σ_{2i-1} > σ_{2i}` for every
`i` with `2i ≤ k` (Hopkins and Tangboonduangjit; notation of D. F. Checa and J. L. Ramírez,
*Arndt compositions: a generating functions approach*, arXiv:2311.15388, Section 1).
`arndtCompositionCount S n k` counts Arndt compositions of `n` with `k` parts, all in the set
`S` (given as a decidable predicate), represented as `k`-tuples of positive integers summing
to `n` (0-based: the pairs are positions `(2i, 2i + 1)`). `arndtGF S` is the bivariate
generating function `A_S(x, y) = ∑ a_S(n, k) xⁿ yᵏ` in `ℤ[y][[x]]`; `S = fun _ => True` gives
the unrestricted `A(x, y)`.

Section 3 (palindromic Arndt compositions) uses trivariate power series in
`MvPowerSeries (Fin 3) ℚ` with `X 0 = x` (weight), `X 1 = y` (number of parts) and `X 2 = z`
(last or middle summand); infinite `q`-series sums are taken in the coefficientwise (pi)
topology. Section 4 counts colored (`n`-color) Arndt compositions, where a part of size `m`
comes in one of `m` colors.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.NarayanaSequence
public import MathlibExt.NumberTheory.PadovanSequence

open scoped MvPowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

/-- **Number of Arndt compositions with parts in a set.** For a set $S$ of natural numbers and
natural numbers $n$ and $k$, $a_S(n, k)$ is the number of $k$-tuples $(c_1, \dots, c_k)$ of
positive integers such that $c_1 + \dots + c_k = n$, every $c_i$ lies in $S$, and
$c_{2i-1} > c_{2i}$ for every $i$ with $2i \le k$. These tuples are the Arndt compositions of
$n$ with $k$ parts in $S$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 1 (definition of Arndt compositions, after
D. F. Checa and J. L. Ramírez, arXiv:2311.15388, Section 1). -/
def arndtCompositionCount (S : ℕ → Prop) [DecidablePred S] (n k : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple k n).filter fun c =>
    (∀ i, 0 < c i ∧ S (c i)) ∧
      ∀ i j : Fin k, (i : ℕ) % 2 = 0 → (j : ℕ) = i + 1 → c j < c i).card

/-- **Arndt compositions of 6 with two parts.** There are exactly $2$ Arndt compositions of $6$
with two parts.

They are $(5, 1)$ and $(4, 2)$.

Source: D. F. Checa and J. L. Ramírez, *Arndt compositions: a generating functions approach*,
arXiv:2311.15388, Section 1 (list of the Arndt compositions of `6`). -/
theorem arndtCompositionCount_six_two : arndtCompositionCount (fun _ => True) 6 2 = 2 := by
  decide

/-- **Arndt compositions of 6 with three parts.** There are exactly $4$ Arndt compositions of $6$
with three parts.

They are $(4, 1, 1)$, $(3, 2, 1)$, $(3, 1, 2)$ and $(2, 1, 3)$.

Source: D. F. Checa and J. L. Ramírez, *Arndt compositions: a generating functions approach*,
arXiv:2311.15388, Section 1 (list of the Arndt compositions of `6`). -/
theorem arndtCompositionCount_six_three : arndtCompositionCount (fun _ => True) 6 3 = 4 := by
  decide

/-- **Arndt compositions of 6 with four parts.** There is exactly one Arndt composition of $6$
with four parts.

It is $(2, 1, 2, 1)$.

Source: D. F. Checa and J. L. Ramírez, *Arndt compositions: a generating functions approach*,
arXiv:2311.15388, Section 1 (list of the Arndt compositions of `6`). -/
theorem arndtCompositionCount_six_four : arndtCompositionCount (fun _ => True) 6 4 = 1 := by
  decide

/-- **Generating function of Arndt compositions with parts in a set.** An Arndt composition is a
finite sequence $(\sigma_1, \dots, \sigma_k)$ of positive integers such that
$\sigma_{2i-1} > \sigma_{2i}$ for every $i$ with $2i \le k$. For a set $S$ of natural numbers, let
$a_S(n, k)$ be the number of Arndt compositions of $n$ with $k$ parts, all in $S$. The bivariate
generating function of these compositions, by weight ($x$) and number of parts ($y$), is the power
series $A_S(x, y) = \sum_{n \ge 0} \left(\sum_{k=0}^{n} a_S(n, k)\, y^k\right) x^n$ in
$\mathbb{Z}[y][[x]]$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 2. -/
noncomputable def arndtGF (S : ℕ → Prop) [DecidablePred S] : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), (arndtCompositionCount S n k : Polynomial ℤ) * Polynomial.X ^ k

/-- **Coefficients of the generating function of Arndt compositions.** For a set $S$ of natural
numbers and every $n \ge 0$, the coefficient of $x^n$ in the generating function $A_S(x, y)$ of
Arndt compositions with parts in $S$ is the polynomial $\sum_{k=0}^{n} a_S(n, k)\, y^k$ in
$\mathbb{Z}[y]$, where $a_S(n, k)$ is the number of Arndt compositions of $n$ with $k$ parts, all
in $S$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 2. -/
theorem coeff_arndtGF (S : ℕ → Prop) [DecidablePred S] (n : ℕ) :
    PowerSeries.coeff n (arndtGF S) =
      ∑ k ∈ Finset.range (n + 1),
        (arndtCompositionCount S n k : Polynomial ℤ) * Polynomial.X ^ k := by
  simp [arndtGF]

/-- **Pair decomposition of the Arndt generating function.** Let $S$ be a set of positive
integers and let $A_S(x, y)$ be the generating function of Arndt compositions with parts in $S$:
the formal power series in $x$ over $\mathbb{Z}[y]$ whose coefficient of $x^n y^k$ is the number
of Arndt compositions of $n$ with $k$ parts, all in $S$. Put $P_S(x) = \sum_{i \in S} x^i$ and
$Q_S(x) = \sum_{i, j \in S,\ j < i} x^{i+j}$. Then
$$A_S(x, y) \, (1 - y^2 Q_S(x)) = 1 + y P_S(x).$$

Equivalently, $A_S(x, y) = (1 + y P_S(x)) \sum_{m \ge 0} Q_S(x)^m y^{2m}$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 1 (`jis-2025-25.3.6-thm-1`). -/
public theorem_wanted arndtGF_mul_one_sub_pairs (S : ℕ → Prop) [DecidablePred S]
    (hS : ¬ S 0) :
    arndtGF S *
        (1 - PowerSeries.C (Polynomial.X ^ 2) *
          PowerSeries.mk fun n =>
            ((((Finset.range n) ×ˢ (Finset.range n)).filter fun ij =>
              ij.2 < ij.1 ∧ S ij.1 ∧ S ij.2 ∧ ij.1 + ij.2 = n).card : Polynomial ℤ)) =
      1 + PowerSeries.C Polynomial.X *
        PowerSeries.mk fun i => if S i then (1 : Polynomial ℤ) else 0

/-- **Generating function of all Arndt compositions.** Let $A(x, y)$ be the formal power series
in $x$ over $\mathbb{Z}[y]$ whose coefficient of $x^n y^k$ is the number of Arndt compositions of
$n$ with $k$ parts. Then
$$A(x, y) \left((1 - x)(1 - x^2) - y^2 x^3\right) = (1 - x + xy)(1 - x^2).$$

Equivalently, $A(x, y) = (1 + xy/(1 - x)) \sum_{m \ge 0} y^{2m} x^{3m} / (x; x)_2^m$ with
$(x; x)_2 = (1 - x)(1 - x^2)$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 9 (`jis-2025-25.3.6-thm-9`). -/
public theorem_wanted arndtGF_univ_mul :
    arndtGF (fun _ => True) *
        ((1 - PowerSeries.X) * (1 - PowerSeries.X ^ 2) -
          PowerSeries.C (Polynomial.X ^ 2) * PowerSeries.X ^ 3) =
      (1 - PowerSeries.X + PowerSeries.C Polynomial.X * PowerSeries.X) *
        (1 - PowerSeries.X ^ 2)

/-- **Arndt compositions with a given number of parts as a sum of products.** For all natural
numbers $n$ and $\ell$, the number of Arndt compositions of $n$ with $2\ell$ parts is
$$\sum_{(a_1, \dots, a_\ell)} \prod_{i=1}^{\ell} \left\lfloor \frac{a_i - 1}{2} \right\rfloor,$$
the sum running over the $\ell$-tuples of natural numbers with $a_1 + \dots + a_\ell = n$ and
every $a_i \ge 3$; and the number of Arndt compositions of $n$ with $2\ell + 1$ parts is the same
sum of products $\prod_{i=1}^{\ell} \lfloor (a_i - 1)/2 \rfloor$, now running over the
$(\ell + 1)$-tuples $(a_1, \dots, a_{\ell+1})$ of natural numbers with
$a_1 + \dots + a_{\ell+1} = n$, $a_1, \dots, a_\ell \ge 3$ and $a_{\ell+1} \ge 1$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 10 (`jis-2025-25.3.6-thm-10`). -/
public theorem_wanted arndtCompositionCount_eq_sum_prod (n ℓ : ℕ) :
    arndtCompositionCount (fun _ => True) n (2 * ℓ) =
        (∑ a ∈ (Finset.Nat.antidiagonalTuple ℓ n).filter (fun a => ∀ i, 3 ≤ a i),
          ∏ i, (a i - 1) / 2) ∧
      arndtCompositionCount (fun _ => True) n (2 * ℓ + 1) =
        (∑ a ∈ (Finset.Nat.antidiagonalTuple (ℓ + 1) n).filter
            (fun a => (∀ i : Fin ℓ, 3 ≤ a i.castSucc) ∧ 1 ≤ a (Fin.last ℓ)),
          ∏ i : Fin ℓ, (a i.castSucc - 1) / 2)


/-- **Arndt compositions with parts at most 3 and the Padovan numbers.** For every $n \ge 0$, the
number of Arndt compositions of $n$ (compositions $(\sigma_1, \dots, \sigma_k)$ with
$\sigma_{2i-1} > \sigma_{2i}$ whenever $2i \le k$) with all parts in $\{1, 2, 3\}$, counting the
empty composition when $n = 0$, equals the shifted Padovan number $s_{n+2}$, where $s_0 = 1$,
$s_1 = 0$, $s_2 = 1$ and $s_{m+3} = s_{m+1} + s_m$. Equivalently, it is the Padovan number $P(n)$
given by $P(0) = P(1) = P(2) = 1$ and $P(n) = P(n-2) + P(n-3)$ for $n \ge 3$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 2 (`jis-2025-25.3.6-thm-2`). -/
public theorem_wanted sum_arndtCompositionCount_le_three (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), arndtCompositionCount (fun i => i ≤ 3) n k =
      shiftedPadovanSequence (n + 2)

/-- **Arndt compositions with parts at most 4 and Narayana's cows sequence.** For every
$n \ge 0$, the number of Arndt compositions of $n$ (compositions $(\sigma_1, \dots, \sigma_k)$
with $\sigma_{2i-1} > \sigma_{2i}$ whenever $2i \le k$) with all parts in $\{1, 2, 3, 4\}$,
counting the empty composition when $n = 0$, equals $N_{n+1}$, where $(N_m)$ is Narayana's cows
sequence: $N_0 = 0$, $N_1 = N_2 = 1$ and $N_m = N_{m-1} + N_{m-3}$ for $m \ge 3$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 4 (`jis-2025-25.3.6-thm-4`). -/
public theorem_wanted sum_arndtCompositionCount_le_four (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), arndtCompositionCount (fun i => i ≤ 4) n k =
      narayanaCowsSequence (n + 1)

/-- **Generating function of Arndt compositions with bounded largest part.** For a natural number
$\ell$, let $A(x, y; \ell)$ be the formal power series in $x$ over $\mathbb{Z}[y]$ whose
coefficient of $x^n y^k$ is the number of Arndt compositions of $n$ with $k$ parts, all at most
$\ell$, and let
$$D_\ell(x, y) = 1 - x^{2+2\ell} y^2 + x^{2+\ell} (1 + x) y^2 - x (1 + x + x^2 (y^2 - 1)).$$
Then
$$A(x, y; \ell) \, D_\ell(x, y) = (1 - x^2)\left(1 - x + x (1 - x^\ell) y\right).$$

The paper assumes $\ell \ge 2$; the identity also holds for $\ell = 0, 1$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Corollary 5 (`jis-2025-25.3.6-cor-5`). -/
public theorem_wanted arndtGF_le_mul (ℓ : ℕ) :
    arndtGF (fun i => i ≤ ℓ) *
        (1 - PowerSeries.X ^ (2 + 2 * ℓ) * PowerSeries.C (Polynomial.X ^ 2) +
          PowerSeries.X ^ (2 + ℓ) * (1 + PowerSeries.X) * PowerSeries.C (Polynomial.X ^ 2) -
          PowerSeries.X * (1 + PowerSeries.X +
            PowerSeries.X ^ 2 * (-1 + PowerSeries.C (Polynomial.X ^ 2)))) =
      (1 - PowerSeries.X ^ 2) *
        (1 - PowerSeries.X + PowerSeries.X * (1 - PowerSeries.X ^ ℓ) * PowerSeries.C Polynomial.X)

/-- **Generating function of Arndt compositions with bounded smallest part.** For a natural
number $\ell \ge 1$, let $B(x, y; \ell)$ be the formal power series in $x$ over $\mathbb{Z}[y]$
whose coefficient of $x^n y^k$ is the number of Arndt compositions of $n$ with $k$ parts, all at
least $\ell$. Then
$$B(x, y; \ell) \left(1 - x - x^2 + x^3 - x^{2\ell+1} y^2\right) = (1 - x^2)(1 - x + x^\ell y).$$

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Corollary 6 (`jis-2025-25.3.6-cor-6`). -/
public theorem_wanted arndtGF_ge_mul (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    arndtGF (fun i => ℓ ≤ i) *
        (1 - PowerSeries.X - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 -
          PowerSeries.X ^ (2 * ℓ + 1) * PowerSeries.C (Polynomial.X ^ 2)) =
      (1 - PowerSeries.X ^ 2) *
        (1 - PowerSeries.X + PowerSeries.X ^ ℓ * PowerSeries.C Polynomial.X)

/-- **Generating functions of Arndt compositions with even parts and with odd parts.** Let
$A_E(x, y)$ and $A_O(x, y)$ be the formal power series in $x$ over $\mathbb{Z}[y]$ whose
coefficient of $x^n y^k$ is the number of Arndt compositions of $n$ with $k$ parts, all even,
respectively all odd. Then
$$A_E(x, y) \left(1 - x^2 - x^4 + x^6 (1 - y^2)\right) = (1 - x^4)\left(1 - x^2 (1 - y)\right)$$
and
$$A_O(x, y) \left(1 - x^2 + x^6 - x^4 (1 + y^2)\right) = (1 - x^4)(1 - x^2 + x y).$$

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Corollary 7 (`jis-2025-25.3.6-cor-7`). -/
public theorem_wanted arndtGF_even_odd_mul :
    arndtGF (fun i => i % 2 = 0) *
          (1 - PowerSeries.X ^ 2 - PowerSeries.X ^ 4 +
            PowerSeries.X ^ 6 * (1 - PowerSeries.C (Polynomial.X ^ 2))) =
        (1 - PowerSeries.X ^ 4) *
          (1 - PowerSeries.X ^ 2 * (1 - PowerSeries.C Polynomial.X)) ∧
      arndtGF (fun i => i % 2 = 1) *
          (1 - PowerSeries.X ^ 2 + PowerSeries.X ^ 6 -
            PowerSeries.X ^ 4 * (1 + PowerSeries.C (Polynomial.X ^ 2))) =
        (1 - PowerSeries.X ^ 4) *
          (1 - PowerSeries.X ^ 2 + PowerSeries.X * PowerSeries.C Polynomial.X)

/-! ### Palindromic Arndt compositions (Section 3) -/

/-- **Down/up compositions.** A down/up (descending wiggly) composition of $n$ with $k$ parts is a
sequence $(\sigma_1, \dots, \sigma_k)$ of positive integers with sum $n$ such that
$\sigma_1 > \sigma_2 < \sigma_3 > \sigma_4 < \cdots$, that is, $\sigma_i > \sigma_{i+1}$ for odd
$i$ and $\sigma_i < \sigma_{i+1}$ for even $i$. For $n, k, j \ge 0$, $w(n, k, j)$ is the number of
down/up compositions of $n$ with $k$ parts whose last part $\sigma_k$ equals $j$, where the empty
composition ($k = 0$) is taken to have last part $0$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 3 (the set `W`, OEIS A025049). -/
def downUpCompositionCount (n k j : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple k n).filter fun c =>
    (∀ i, 0 < c i) ∧
      (∀ i i' : Fin k, (i' : ℕ) = i + 1 →
        ((i : ℕ) % 2 = 0 → c i' < c i) ∧ ((i : ℕ) % 2 = 1 → c i < c i')) ∧
      (if h : 0 < k then c ⟨k - 1, by omega⟩ else 0) = j).card

/-- **Down/up compositions of 5 with two parts.** Among the down/up compositions of $5$ with two
parts (pairs $(\sigma_1, \sigma_2)$ of positive integers with $\sigma_1 + \sigma_2 = 5$ and
$\sigma_1 > \sigma_2$), exactly one has last part $1$, exactly one has last part $2$, and none has
last part $3$.

The compositions counted are $(4, 1)$ and $(3, 2)$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 3 (the set `W`). -/
theorem downUpCompositionCount_five_two : downUpCompositionCount 5 2 1 = 1 ∧
    downUpCompositionCount 5 2 2 = 1 ∧ downUpCompositionCount 5 2 3 = 0 := by
  decide

/-- **Down/up compositions of 6 with three parts.** Among the down/up compositions of $6$ with
three parts (triples $(\sigma_1, \sigma_2, \sigma_3)$ of positive integers with sum $6$ and
$\sigma_1 > \sigma_2 < \sigma_3$), exactly one has last part $3$, exactly one has last part $2$,
and none has last part $1$.

The compositions counted are $(2, 1, 3)$ and $(3, 1, 2)$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 3 (the set `W`). -/
theorem downUpCompositionCount_six_three : downUpCompositionCount 6 3 3 = 1 ∧
    downUpCompositionCount 6 3 2 = 1 ∧ downUpCompositionCount 6 3 1 = 0 := by
  decide

/-- **Generating function of down/up compositions with an even number of parts.** $F(x, y, z)$ is
the formal power series in $\mathbb{Q}[[x, y, z]]$ whose coefficient of $x^n y^k z^j$ is the
number of down/up compositions of $n$ with $k$ parts and last part $j$ when $k$ is even, and $0$
when $k$ is odd. The empty composition, with last part $0$, contributes the constant term $1$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 3.1 (definition of `F`). -/
noncomputable def downUpEvenGF : MvPowerSeries (Fin 3) ℚ := fun e =>
  if e 1 % 2 = 0 then (downUpCompositionCount (e 0) (e 1) (e 2) : ℚ) else 0

/-- **Generating function of down/up compositions with an odd number of parts.** $G(x, y, z)$ is
the formal power series in $\mathbb{Q}[[x, y, z]]$ whose coefficient of $x^n y^k z^j$ is the
number of down/up compositions of $n$ with $k$ parts and last part $j$ when $k$ is odd, and $0$
when $k$ is even.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 3.1 (definition of `G`). -/
noncomputable def downUpOddGF : MvPowerSeries (Fin 3) ℚ := fun e =>
  if e 1 % 2 = 1 then (downUpCompositionCount (e 0) (e 1) (e 2) : ℚ) else 0

/-- **The auxiliary series $\alpha$ for down/up compositions.** In $\mathbb{Q}[[x, y, z]]$ write
$(a; x)_m = \prod_{j=0}^{m-1} (1 - a x^j)$. For a power series $w$ in $\mathbb{Q}[[x, y, z]]$, the
series $\alpha(x, y, w)$ is the coefficientwise convergent sum
$\alpha(x, y, w) = \sum_{n \ge 0} \frac{(-1)^n x^{n^2+n} y^{2n} w^n}{(xw; x)_{2n}}$.

The paper uses it with $w = z$ and with $w = x$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 12, equation (5). -/
noncomputable def arndtPalAlpha (w : MvPowerSeries (Fin 3) ℚ) : MvPowerSeries (Fin 3) ℚ :=
  ∑' n : ℕ, (-1 : MvPowerSeries (Fin 3) ℚ) ^ n * MvPowerSeries.X 0 ^ (n ^ 2 + n) *
    MvPowerSeries.X 1 ^ (2 * n) * w ^ n *
      (∏ k ∈ Finset.range (2 * n), (1 - MvPowerSeries.X 0 ^ (k + 1) * w))⁻¹

/-- **The auxiliary series $\beta$ for down/up compositions.** In $\mathbb{Q}[[x, y, z]]$ write
$(a; x)_m = \prod_{j=0}^{m-1} (1 - a x^j)$. For a power series $w$ in $\mathbb{Q}[[x, y, z]]$, the
series $\beta(x, y, w)$ is the coefficientwise convergent sum
$\beta(x, y, w) = \sum_{n \ge 1} \frac{(-1)^{n+1} x^{n^2+n} y^{2n} w^n}{(1 - x)(xw; x)_{2n-1}}$.

The paper uses it with $w = z$ and with $w = x$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 12, equation (5). -/
noncomputable def arndtPalBeta (w : MvPowerSeries (Fin 3) ℚ) : MvPowerSeries (Fin 3) ℚ :=
  ∑' n : ℕ, (-1 : MvPowerSeries (Fin 3) ℚ) ^ (n + 2) * MvPowerSeries.X 0 ^ ((n + 1) ^ 2 + (n + 1)) *
    MvPowerSeries.X 1 ^ (2 * (n + 1)) * w ^ (n + 1) *
      ((1 - MvPowerSeries.X 0) *
        ∏ k ∈ Finset.range (2 * n + 1), (1 - MvPowerSeries.X 0 ^ (k + 1) * w))⁻¹

/-- **Formula for the generating function of even-length down/up compositions.** Let
$F(x, y, z) \in \mathbb{Q}[[x, y, z]]$ be the generating function of down/up compositions with an
even number of parts (including the empty composition, with last part $0$) by weight ($x$),
number of parts ($y$) and last part ($z$). For a power series $w$, write
$(xw; x)_m = \prod_{i=1}^{m} (1 - x^i w)$ and let
$$\alpha(x, y, w) = \sum_{n \ge 0} \frac{(-1)^n x^{n^2+n} y^{2n} w^n}{(xw; x)_{2n}}$$
and
$$\beta(x, y, w) = \sum_{n \ge 1} \frac{(-1)^{n+1} x^{n^2+n} y^{2n} w^n}{(1 - x)(xw; x)_{2n-1}},$$
with the sums taken coefficientwise. Then
$$F(x, y, z) = \alpha(x, y, z) + \frac{\alpha(x, y, x)\, \beta(x, y, z)}{1 - \beta(x, y, x)}.$$

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 12 (`jis-2025-25.3.6-thm-12`). -/
public theorem_wanted downUpEvenGF_eq :
    downUpEvenGF = arndtPalAlpha (MvPowerSeries.X 2) +
      arndtPalAlpha (MvPowerSeries.X 0) * (1 - arndtPalBeta (MvPowerSeries.X 0))⁻¹ *
        arndtPalBeta (MvPowerSeries.X 2)

/-- **Odd-length down/up compositions from even-length ones.** Let $F(x, y, z)$ and $G(x, y, z)$
in $\mathbb{Q}[[x, y, z]]$ be the generating functions of down/up compositions with an even,
respectively odd, number of parts by weight ($x$), number of parts ($y$) and last part ($z$).
Then
$$G(x, y, z) = \frac{xyz}{1 - xz}\, F(x, y, xz).$$

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 13 (`jis-2025-25.3.6-thm-13`). -/
public theorem_wanted downUpOddGF_eq :
    downUpOddGF = MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2 *
      (1 - MvPowerSeries.X 0 * MvPowerSeries.X 2)⁻¹ *
        MvPowerSeries.subst
          ![MvPowerSeries.X 0, MvPowerSeries.X 1, MvPowerSeries.X 0 * MvPowerSeries.X 2]
          downUpEvenGF

/-- **Palindromic Arndt compositions.** An Arndt composition of $n$ with $k$ parts is a sequence
$(\sigma_1, \dots, \sigma_k)$ of positive integers with sum $n$ such that
$\sigma_{2i-1} > \sigma_{2i}$ whenever $2i \le k$; it is palindromic when
$\sigma_i = \sigma_{k+1-i}$ for all $i$. For $n, k, m \ge 0$, $p(n, k, m)$ is the number of
palindromic Arndt compositions of $n$ with $k \ge 1$ parts whose middle summand
$\sigma_{\lfloor k/2 \rfloor + 1}$ equals $m$; in particular $p(n, 0, m) = 0$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 3 (the set `PA`). -/
def palindromicArndtCount (n k m : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple k n).filter fun c =>
    (∀ i, 0 < c i) ∧
      (∀ i j : Fin k, (i : ℕ) % 2 = 0 → (j : ℕ) = i + 1 → c j < c i) ∧
      (∀ i j : Fin k, (i : ℕ) + j + 1 = k → c i = c j) ∧
      (if h : 0 < k then c ⟨k / 2, by omega⟩ = m else False)).card

/-- **Palindromic Arndt compositions of 5.** There is exactly one palindromic Arndt composition of
$5$ with one part and middle summand $5$, exactly one with three parts and middle summand $1$,
and none with three parts and middle summand $2$.

The compositions counted are $(5)$ and $(2, 1, 2)$; the paper reads them off the coefficient of
$x^5$ in the series expansion of the generating function of palindromic Arndt compositions.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 3.2 (series expansion of `PA(x, y, 1)`). -/
theorem palindromicArndtCount_five : palindromicArndtCount 5 1 5 = 1 ∧
    palindromicArndtCount 5 3 1 = 1 ∧ palindromicArndtCount 5 3 2 = 0 := by
  decide

/-- **Palindromic Arndt generating function.** A palindromic Arndt composition of $n$ with
$k \ge 1$ parts is a tuple $(\sigma_1, \dots, \sigma_k)$ of positive integers with sum $n$ such
that $\sigma_{2i-1} > \sigma_{2i}$ whenever $2i \le k$, and $\sigma_i = \sigma_{k+1-i}$ for all
$i$; its middle summand is $\sigma_{\lfloor k/2 \rfloor + 1}$. The generating function
$PA(x, y, z)$ is the formal power series in $x, y, z$ with rational coefficients whose coefficient
of $x^n y^k z^m$ is the number of palindromic Arndt compositions of $n$ with $k$ parts and middle
summand $m$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 3.2 (definition of `PA`). -/
noncomputable def palindromicArndtGF : MvPowerSeries (Fin 3) ℚ := fun e =>
  (palindromicArndtCount (e 0) (e 1) (e 2) : ℚ)

/-- **Generating function of palindromic Arndt compositions.** Let $PA(x, y, z)$ be the
generating function of nonempty palindromic Arndt compositions by weight ($x$), number of parts
($y$) and middle summand ($z$), and let $F(x, y, z)$ be the generating function of down/up
compositions $\sigma_1 > \sigma_2 < \sigma_3 > \cdots$ with an even number of parts by weight
($x$), number of parts ($y$) and last part ($z$). Then, as formal power series over $\mathbb{Q}$,
$$
PA(x, y, z) = \frac{xyz}{1 - xz} F(x^2, y^2, xz) +
\frac{x^3 y^3 z}{(1 - x^2)(1 - xz)} F(x^2, y^2, x^2) -
\frac{x^3 y^3 z}{(1 - xz)(1 - x^3 z)} F(x^2, y^2, x^3 z).
$$

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 14 (`jis-2025-25.3.6-thm-14`). -/
public theorem_wanted palindromicArndtGF_eq :
    palindromicArndtGF =
      MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2 *
          (1 - MvPowerSeries.X 0 * MvPowerSeries.X 2)⁻¹ *
          MvPowerSeries.subst ![MvPowerSeries.X 0 ^ 2, MvPowerSeries.X 1 ^ 2,
            MvPowerSeries.X 0 * MvPowerSeries.X 2] downUpEvenGF +
        MvPowerSeries.X 0 ^ 3 * MvPowerSeries.X 1 ^ 3 * MvPowerSeries.X 2 *
          ((1 - MvPowerSeries.X 0 ^ 2) * (1 - MvPowerSeries.X 0 * MvPowerSeries.X 2))⁻¹ *
          MvPowerSeries.subst ![MvPowerSeries.X 0 ^ 2, MvPowerSeries.X 1 ^ 2,
            MvPowerSeries.X 0 ^ 2] downUpEvenGF -
        MvPowerSeries.X 0 ^ 3 * MvPowerSeries.X 1 ^ 3 * MvPowerSeries.X 2 *
          ((1 - MvPowerSeries.X 0 * MvPowerSeries.X 2) *
            (1 - MvPowerSeries.X 0 ^ 3 * MvPowerSeries.X 2))⁻¹ *
          MvPowerSeries.subst ![MvPowerSeries.X 0 ^ 2, MvPowerSeries.X 1 ^ 2,
            MvPowerSeries.X 0 ^ 3 * MvPowerSeries.X 2] downUpEvenGF

/-! ### Colored Arndt compositions (Section 4) -/

/-- **Colored Arndt compositions.** An Arndt composition of $n$ with $k$ parts is a sequence
$(\sigma_1, \dots, \sigma_k)$ of positive integers with sum $n$ such that
$\sigma_{2i-1} > \sigma_{2i}$ for every $i$ with $2i \le k$. In a colored Arndt composition, each
part of size $m$ carries one of $m$ colors. The number $c(n, k)$ of colored Arndt compositions of
$n$ with $k$ parts is therefore the sum of $\sigma_1 \sigma_2 \cdots \sigma_k$ over all Arndt
compositions $(\sigma_1, \dots, \sigma_k)$ of $n$ with $k$ parts.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 4 (definition of colored Arndt compositions). -/
def coloredArndtCount (n k : ℕ) : ℕ :=
  ∑ c ∈ (Finset.Nat.antidiagonalTuple k n).filter (fun c =>
      (∀ i, 0 < c i) ∧ ∀ i j : Fin k, (i : ℕ) % 2 = 0 → (j : ℕ) = i + 1 → c j < c i),
    ∏ i, c i

/-- **Colored Arndt compositions of 4.** Write $m_a$ for a part of size $m$ with color
$a \in \{1, \dots, m\}$. The colored Arndt compositions of $4$ are $(4_1)$, $(4_2)$, $(4_3)$,
$(4_4)$, $(3_a, 1_1)$ for $a \le 3$, and $(2_a, 1_1, 1_1)$ for $a \le 2$. Hence the numbers of
colored Arndt compositions of $4$ with $1$, $2$ and $3$ parts are $c(4, 1) = 4$, $c(4, 2) = 3$
and $c(4, 3) = 2$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 4, list (6). -/
theorem coloredArndtCount_four : coloredArndtCount 4 1 = 4 ∧ coloredArndtCount 4 2 = 3 ∧
    coloredArndtCount 4 3 = 2 := by
  decide

/-- **Generating function of colored Arndt compositions.** The bivariate generating function of
colored Arndt compositions, by weight ($x$) and number of parts ($y$), is the power series
$C(x, y) = \sum_{n \ge 0} \left(\sum_{k=0}^{n} c(n, k)\, y^k\right) x^n$ in $\mathbb{Z}[y][[x]]$,
where $c(n, k)$ is the number of colored Arndt compositions of $n$ with $k$ parts.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 4 (definition of `C(x, y)`). -/
noncomputable def coloredArndtGF : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), (coloredArndtCount n k : Polynomial ℤ) * Polynomial.X ^ k

/-- **Closed form of the generating function of colored Arndt compositions.** Let
$C(x, y) = \sum_{n, k} c(n, k)\, x^n y^k$ in $\mathbb{Z}[y][[x]]$, where $c(n, k)$ is the number
of colored Arndt compositions of $n$ with $k$ parts. Then
$C(x, y) \cdot (1 - x - 3x^2 - x^3(2y^2 - 3) - x^4(y^2 - 3) - x^5(3 + y^2) - x^6 + x^7) =
(1 - x)^2 (1 + x)^3 (1 + x^2 + x(y - 2))$.

Since the second factor on the left has constant term $1$, this says that
$C(x, y) = \frac{(1 - x)^2 (1 + x)^3 (1 + x^2 + x(y - 2))}{1 - x - 3x^2 - x^3(2y^2 - 3) -
x^4(y^2 - 3) - x^5(3 + y^2) - x^6 + x^7}$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 17 (`jis-2025-25.3.6-thm-17`). -/
public theorem_wanted coloredArndtGF_mul :
    coloredArndtGF *
        (1 - PowerSeries.X - 3 * PowerSeries.X ^ 2 -
          PowerSeries.X ^ 3 * (2 * PowerSeries.C (Polynomial.X ^ 2) - 3) -
          PowerSeries.X ^ 4 * (PowerSeries.C (Polynomial.X ^ 2) - 3) -
          PowerSeries.X ^ 5 * (3 + PowerSeries.C (Polynomial.X ^ 2)) -
          PowerSeries.X ^ 6 + PowerSeries.X ^ 7) =
      (1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 3 *
        (1 + PowerSeries.X ^ 2 + PowerSeries.X * (PowerSeries.C Polynomial.X - 2))

/-- **Generating function for the total number of colored Arndt compositions.** For $n \ge 0$ let
$c(n, k)$ be the number of colored Arndt compositions of $n$ with $k$ parts, and let
$c(n) = \sum_{k=0}^{n} c(n, k)$ be the total number of colored Arndt compositions of $n$ (so
$c(0) = 1$, counting the empty composition). Then, in the ring $\mathbb{Z}[[x]]$ of formal power
series,
$$\Big(\sum_{n \ge 0} c(n) x^n\Big) (1 - x - 3x^2 + x^3 + 2x^4 - 4x^5 - x^6 + x^7) =
(1 - x)^2 (1 + x)^3 (1 - x + x^2).$$

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Corollary 18 (`jis-2025-25.3.6-cor-18`). -/
public theorem_wanted coloredArndt_total_mul :
    (PowerSeries.mk fun n => ∑ k ∈ Finset.range (n + 1), (coloredArndtCount n k : ℤ)) *
        (1 - PowerSeries.X - 3 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4 -
          4 * PowerSeries.X ^ 5 - PowerSeries.X ^ 6 + PowerSeries.X ^ 7) =
      (1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 3 *
        (1 - PowerSeries.X + PowerSeries.X ^ 2)

/-- **Generating function of colored Arndt compositions with $k$ parts.** For every $k \ge 0$,
let $C_k(x) = \sum_{n \ge 0} c(n, k)\, x^n$ in $\mathbb{Z}[[x]]$, where $c(n, k)$ is the number of
colored Arndt compositions of $n$ with $k$ parts. Then
$C_k(x)\, (1 - x)^{2k} (1 + x)^{3\lfloor k/2 \rfloor} =
x^{k + \lfloor k/2 \rfloor} (x^2 + x + 2)^{\lfloor k/2 \rfloor}$.

Equivalently, since $(1 - x)^{2k} (1 + x)^{3\lfloor k/2 \rfloor}$ has constant term $1$,
$C_k(x) = \frac{x^{k + \lfloor k/2 \rfloor} (x^2 + x + 2)^{\lfloor k/2 \rfloor}}
{(1 - x)^{2k} (1 + x)^{3\lfloor k/2 \rfloor}}$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 19 (`jis-2025-25.3.6-thm-19`). -/
public theorem_wanted coloredArndt_parts_mul (k : ℕ) :
    (PowerSeries.mk fun n => (coloredArndtCount n k : ℤ)) *
        ((1 - PowerSeries.X) ^ (2 * k) * (1 + PowerSeries.X) ^ (3 * (k / 2))) =
      PowerSeries.X ^ (k + k / 2) * (PowerSeries.X ^ 2 + PowerSeries.X + 2) ^ (k / 2)

/-- **Asymptotics of colored Arndt compositions with $k$ parts.** For every fixed $k \ge 1$, the
number $c(n, k)$ of colored Arndt compositions of $n$ with $k$ parts satisfies
$c(n, k) \sim \frac{n^{2k-1}}{2^{\lfloor k/2 \rfloor} (2k - 1)!}$ as $n \to \infty$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Corollary 20 (`jis-2025-25.3.6-cor-20`). -/
public theorem_wanted coloredArndtCount_isEquivalent (k : ℕ) (hk : 0 < k) :
    Asymptotics.IsEquivalent Filter.atTop (fun n => (coloredArndtCount n k : ℝ))
      fun n => (n : ℝ) ^ (2 * k - 1) / (2 ^ (k / 2) * (Nat.factorial (2 * k - 1) : ℝ))

end

end MetaMathlibExt
