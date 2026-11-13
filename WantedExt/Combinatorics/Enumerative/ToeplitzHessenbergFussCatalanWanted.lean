/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Toeplitz-Hessenberg determinants with Fuss-Catalan entries

Statements from Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2.

`toeplitzHessenbergDet a n` is the determinant of the `n × n` Toeplitz-Hessenberg matrix with
`a 0` on the superdiagonal and `a 1, …, a n` down the first column. The paper's
`D_±(a_1, …, a_n)` is `toeplitzHessenbergDet (fun i => if i = 0 then ±1 else a i) n`.
The Fuss-Catalan (Raney) number `A_n(p, r)` is `(generalizedFussCatalanNumber p n r : ℚ)`
(MathlibExt), so `C_n = A_n(2, 1)`,
`K_n = A_n(2, 3) = C_{n+2} - C_{n+1}`, `H_n = A_n(3, 1)`, `J_n = A_n(3, 2)`. The Catalan generating
function `C(x)` is `PowerSeries.mk fun n => (catalan n : ℚ)`. Generating-function statements are
written multiplicatively.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.DyckPeakDescents
public import MathlibExt.Combinatorics.NoncrossingPartition.Basic
public import MathlibExt.LinearAlgebra.Matrix.TrudiBrioschiDeterminant
public import MathlibExt.NumberTheory.GeneralizedFussCatalanNumbersFMNK

namespace MetaMathlibExt

@[expose] public section

/-- **Small generalized Fuss–Catalan numbers.** For the generalized Fuss–Catalan numbers
$A_n(p, r) = \frac{r}{pn + r} \binom{pn + r}{n}$, one has $A_3(2, 1) = 5$, $A_2(2, 3) = 9$,
$A_3(3, 1) = 12$ and $A_2(3, 2) = 7$.

With $C_n$ the $n$-th Catalan number, $A_3(2, 1) = C_3$ and $A_2(2, 3) = C_4 - C_3$.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Sections 1-2
(`C_n = A_n(2, 1)`, `K_n = A_n(2, 3)`, `H_n = A_n(3, 1)`, `J_n = A_n(3, 2)`). -/
theorem toeplitzHessenberg_fussCatalan_examples :
    generalizedFussCatalanNumber 2 3 1 = 5 ∧ generalizedFussCatalanNumber 2 2 3 = 9 ∧
      generalizedFussCatalanNumber 3 3 1 = 12 ∧ generalizedFussCatalanNumber 3 2 2 = 7 := by
  decide

/-- **Generating function of Toeplitz–Hessenberg determinants.** Let $R$ be a commutative ring and
$a_0, a_1, a_2, \dots$ a sequence in $R$. Write $\det(a_0; a_1, \dots, a_n)$ for the determinant
of the $n \times n$ Toeplitz–Hessenberg matrix whose entry in row $i$ and column $j$ is
$a_{i+1-j}$ for $j \le i + 1$ and $0$ above the superdiagonal. In the ring of formal power series
over $R$ let $f(x) = \sum_{n \ge 1} \det(a_0; a_1, \dots, a_n)\, x^n$ and
$H(x) = \sum_{i \ge 1} a_i (-a_0)^{i-1} x^i$. Then $f = H + H f$.

When $a_0$ is invertible, $H(x) = -g(-a_0 x)/a_0$ with $g(x) = \sum_{i \ge 1} a_i x^i$, and the
identity is the paper's $f(x) = (-g(-a_0 x)/a_0)/(1 + g(-a_0 x)/a_0)$. The form $f = H + H f$
needs no hypothesis on $a_0$; for $a_0 = 0$ it gives $\det(0; a_1, \dots, a_n) = a_1^n$.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Lemma 2
(`jis-2026-26.1.2-lem-2`). -/
public theorem_wanted toeplitzHessenbergDet_genFun {R : Type*} [CommRing R] (a : ℕ → R) :
    PowerSeries.mk (fun n => if n = 0 then 0 else toeplitzHessenbergDet a n) =
      PowerSeries.mk (fun i => if i = 0 then 0 else a i * (-a 0) ^ (i - 1)) +
        PowerSeries.mk (fun i => if i = 0 then 0 else a i * (-a 0) ^ (i - 1)) *
          PowerSeries.mk (fun n => if n = 0 then 0 else toeplitzHessenbergDet a n)

/-- **Toeplitz–Hessenberg determinants of Fuss–Catalan numbers.** Write
$\det(a_0; a_1, \dots, a_n)$ for the determinant of the $n \times n$ Toeplitz–Hessenberg matrix
whose entry in row $i$ and column $j$ is $a_{i+1-j}$ for $j \le i + 1$ and $0$ above the
superdiagonal. For natural numbers $p, r, n$ let $A_n(p, r) = \frac{r}{pn + r} \binom{pn + r}{n}$
be the generalized Fuss–Catalan number, taken to be $0$ when $pn + r = 0$. Then for all natural
numbers $p, r$ and every $n \ge 1$,
$$\det(1; A_1(p, r), \dots, A_n(p, r)) = (-1)^{n-1} \frac{r}{n} \binom{pn - r - 1}{n - 1}$$
in $\mathbb{Q}$, where the binomial coefficient has an integer, possibly negative, upper index:
$\binom{x}{k} = x (x - 1) \cdots (x - k + 1)/k!$.

This includes $p = r = 0$, which the paper's standing assumption excludes; there every entry
$A_i(0, 0)$ is $0$ and both sides vanish.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Theorem 3
(`jis-2026-26.1.2-thm-3`). -/
public theorem_wanted toeplitzHessenbergDet_fussCatalan (p r n : ℕ) (hn : 1 ≤ n) :
    toeplitzHessenbergDet
        (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber p i r : ℚ)) n =
      (-1) ^ (n - 1) * (r : ℚ) / n * (Ring.choose ((p * n : ℤ) - r - 1) (n - 1) : ℚ)

/-- **Special Toeplitz–Hessenberg determinants of Fuss–Catalan numbers.** Write
$\det(a_0; a_1, \dots, a_n)$ for the determinant of the $n \times n$ Toeplitz–Hessenberg matrix
whose entry in row $i$ and column $j$ is $a_{i+1-j}$ for $j \le i + 1$ and $0$ above the
superdiagonal. For natural numbers $p, r \ge 1$ let $A_n(p, r) = \frac{r}{pn + r} \binom{pn + r}{n}$
be the generalized Fuss–Catalan number, put
$D_n(p, r) = (-1)^{n-1} \det(1; A_1(p, r), \dots, A_n(p, r))$, and let $C_n$ be the $n$-th
Catalan number. Then, in $\mathbb{Q}$: $D_n(2, 3) = C_{n-1} - C_{n-2}$ for every $n \ge 2$;
$D_n(2, 4) = C_{n-1} - 2 C_{n-2}$ for every $n \ge 3$;
$D_n(3, 1) = \frac{1}{n} \binom{3n - 2}{n - 1}$ for every $n \ge 1$; and
$D_n(3, 2) = \frac{2}{n} \binom{3n - 3}{n - 1}$ for every $n \ge 1$.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Corollary 4
(`jis-2026-26.1.2-cor-4`). -/
public theorem_wanted toeplitzHessenbergDet_fussCatalan_special :
    (∀ n : ℕ, 2 ≤ n →
      (-1) ^ (n - 1) * toeplitzHessenbergDet
          (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 2 i 3 : ℚ)) n =
        (catalan (n - 1) : ℚ) - catalan (n - 2)) ∧
    (∀ n : ℕ, 3 ≤ n →
      (-1) ^ (n - 1) * toeplitzHessenbergDet
          (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 2 i 4 : ℚ)) n =
        (catalan (n - 1) : ℚ) - 2 * catalan (n - 2)) ∧
    (∀ n : ℕ, 1 ≤ n →
      (-1) ^ (n - 1) * toeplitzHessenbergDet
          (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 3 i 1 : ℚ)) n =
        1 / (n : ℚ) * ((3 * n - 2).choose (n - 1) : ℚ)) ∧
    ∀ n : ℕ, 1 ≤ n →
      (-1) ^ (n - 1) * toeplitzHessenbergDet
          (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 3 i 2 : ℚ)) n =
        2 / (n : ℚ) * ((3 * n - 3).choose (n - 1) : ℚ)

/-- **Toeplitz–Hessenberg determinants with Catalan entries.** Write $\det(a_0; a_1, \dots, a_n)$
for the determinant of the $n \times n$ Toeplitz–Hessenberg matrix whose entry in row $i$ and
column $j$ is $a_{i+1-j}$ for $j \le i + 1$ and $0$ above the superdiagonal (so $a_0$ fills the
superdiagonal and $a_1, \dots, a_n$ the first column); for $n = 0$ it is $1$. Let $C_n$ be the
$n$-th Catalan number, $C(x) = \sum_{n \ge 0} C_n x^n \in \mathbb{Q}[[x]]$, and
$K_m = C_{m+2} - C_{m+1}$ for $m \ge -1$, so that $K_{-1} = 0$. Then the following hold.
(1) $\sum_{n \ge 1} \det(-1; C_1, C_3, \dots, C_{2n-1})\, x^{2n} = x^2 C(x)^2 C(-x)^2$.
(2) $\bigl(\sum_{n \ge 0} \det(-1; C_2, \dots, C_{n+1})\, x^n\bigr) \bigl(2 - C(x)^2\bigr) = 1$.
(3) For every $n \ge 1$,
$\det(1; K_{-1}, K_0, \dots, K_{n-2}) = (-1)^{n-1} \sum_{i=1}^{n-1} C_i$.
(4) For every $n \ge 1$, $\det(1; K_0, K_1, \dots, K_{n-1}) = (-1)^{n-1} \sum_{i=0}^{n-1} C_i$.
(5) $\bigl(\sum_{n \ge 1} \det(-1; K_0, K_1, \dots, K_{n-1})\, x^n\bigr) \bigl(1 - x C(x)^3\bigr) =
x C(x)^3$.

Thus the determinants in (2) have generating function $1/(2 - C(x)^2)$ and those in (5) have
generating function $x C(x)^3/(1 - x C(x)^3)$, the generating function of OEIS A026674; the
determinants in (1) form OEIS A066357.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Theorem 6
(`jis-2026-26.1.2-thm-6`). -/
public theorem_wanted toeplitzHessenbergDet_catalan :
    let C : PowerSeries ℚ := PowerSeries.mk fun n => (catalan n : ℚ)
    (PowerSeries.mk (fun m => if m % 2 = 0 ∧ 2 ≤ m then
        toeplitzHessenbergDet (fun i => if i = 0 then -1 else (catalan (2 * i - 1) : ℚ)) (m / 2)
      else 0) =
      PowerSeries.X ^ 2 * C ^ 2 * (PowerSeries.rescale (-1 : ℚ) C) ^ 2) ∧
    (PowerSeries.mk (fun n =>
        toeplitzHessenbergDet (fun i => if i = 0 then -1 else (catalan (i + 1) : ℚ)) n) *
      (2 - C ^ 2) = 1) ∧
    (∀ n : ℕ, 1 ≤ n →
      toeplitzHessenbergDet
          (fun i => if i = 0 then 1 else (catalan i : ℚ) - catalan (i - 1)) n =
        (-1) ^ (n - 1) * ∑ i ∈ Finset.Icc 1 (n - 1), (catalan i : ℚ)) ∧
    (∀ n : ℕ, 1 ≤ n →
      toeplitzHessenbergDet
          (fun i => if i = 0 then 1 else (catalan (i + 1) : ℚ) - catalan i) n =
        (-1) ^ (n - 1) * ∑ i ∈ Finset.range n, (catalan i : ℚ)) ∧
    PowerSeries.mk (fun n => if n = 0 then 0 else
        toeplitzHessenbergDet
          (fun i => if i = 0 then -1 else (catalan (i + 1) : ℚ) - catalan i) n) *
      (1 - PowerSeries.X * C ^ 3) = PowerSeries.X * C ^ 3

/-- **Toeplitz–Hessenberg determinants of ternary Fuss–Catalan numbers.** Write
$\det(a_0; a_1, \dots, a_n)$ for the determinant of the $n \times n$ Toeplitz–Hessenberg matrix
whose entry in row $i$ and column $j$ is $a_{i+1-j}$ for $j \le i + 1$ and $0$ above the
superdiagonal, and let $H_n = \frac{1}{3n + 1} \binom{3n + 1}{n}$ and
$J_n = \frac{2}{3n + 2} \binom{3n + 2}{n}$. Then, in $\mathbb{Q}$,
$\det(1; H_2, H_3, \dots, H_{n+1}) = \frac{2 (-1)^{n-1}}{n} \binom{3n - 3}{n - 1}$ for every
$n \ge 2$, and $\det(-1; J_0, J_1, \dots, J_{n-1}) = H_n$ for every $n \ge 1$.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Theorem 8, formulas
(4) and (6) (`jis-2026-26.1.2-thm-8`). -/
public theorem_wanted toeplitzHessenbergDet_ternary :
    (∀ n : ℕ, 2 ≤ n →
      toeplitzHessenbergDet
          (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 3 (i + 1) 1 : ℚ)) n =
        2 * (-1) ^ (n - 1) / (n : ℚ) * ((3 * n - 3).choose (n - 1) : ℚ)) ∧
    ∀ n : ℕ, 1 ≤ n →
      toeplitzHessenbergDet
          (fun i => if i = 0 then -1 else (generalizedFussCatalanNumber 3 (i - 1) 2 : ℚ)) n =
        (generalizedFussCatalanNumber 3 n 1 : ℚ)

/-- **Trudi multi-sums of Fuss–Catalan numbers.** For $s \in \mathbb{Q}$ and rational numbers
$a_1, \dots, a_n$ let $T_s(a_1, \dots, a_n)$ be the sum of
$s^{|\alpha|} \binom{|\alpha|}{\alpha_1, \dots, \alpha_n} a_1^{\alpha_1} \cdots a_n^{\alpha_n}$
over all $(\alpha_1, \dots, \alpha_n) \in \mathbb{N}^n$ with
$\alpha_1 + 2 \alpha_2 + \dots + n \alpha_n = n$, where $|\alpha| = \alpha_1 + \dots + \alpha_n$.
Let $A_n(p, r) = \frac{r}{pn + r} \binom{pn + r}{n}$ be the generalized Fuss–Catalan number,
taken to be $0$ when $pn + r = 0$; let $C_n$ be the $n$-th Catalan number,
$K_m = C_{m+2} - C_{m+1}$ for $m \ge -1$ (so $K_{-1} = 0$), $H_n = A_n(3, 1)$ and
$J_n = A_n(3, 2)$. Then the following hold.
(1) For all natural numbers $p, r$ and every $n \ge 1$,
$-T_{-1}(A_1(p, r), \dots, A_n(p, r)) = \frac{r}{n} \binom{pn - r - 1}{n - 1}$, where the
binomial coefficient has an integer, possibly negative, upper index:
$\binom{x}{k} = x (x - 1) \cdots (x - k + 1)/k!$.
(2) For every $n \ge 1$, $-T_{-1}(K_{-1}, K_0, \dots, K_{n-2}) = \sum_{i=1}^{n-1} C_i$.
(3) For every $n \ge 1$, $-T_{-1}(K_0, K_1, \dots, K_{n-1}) = \sum_{i=0}^{n-1} C_i$.
(4) For every $n \ge 2$, $-T_{-1}(H_2, H_3, \dots, H_{n+1}) = \frac{2}{n} \binom{3n - 3}{n - 1}$.
(5) For every $n \ge 1$, $T_1(J_0, J_1, \dots, J_{n-1}) = H_n$.

Identity (1) includes $p = r = 0$, which the paper's standing assumption excludes; there both
sides are $0$.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Corollary 9
(`jis-2026-26.1.2-cor-9`). -/
public theorem_wanted trudiPartitionSum_fussCatalan :
    (∀ p r n : ℕ, 1 ≤ n →
      -trudiPartitionSum (-1) (fun i => (generalizedFussCatalanNumber p i r : ℚ)) n =
        (r : ℚ) / n * (Ring.choose ((p * n : ℤ) - r - 1) (n - 1) : ℚ)) ∧
    (∀ n : ℕ, 1 ≤ n →
      -trudiPartitionSum (-1) (fun i => (catalan i : ℚ) - catalan (i - 1)) n =
        ∑ i ∈ Finset.Icc 1 (n - 1), (catalan i : ℚ)) ∧
    (∀ n : ℕ, 1 ≤ n →
      -trudiPartitionSum (-1) (fun i => (catalan (i + 1) : ℚ) - catalan i) n =
        ∑ i ∈ Finset.range n, (catalan i : ℚ)) ∧
    (∀ n : ℕ, 2 ≤ n →
      -trudiPartitionSum (-1) (fun i => (generalizedFussCatalanNumber 3 (i + 1) 1 : ℚ)) n =
        2 / (n : ℚ) * ((3 * n - 3).choose (n - 1) : ℚ)) ∧
    ∀ n : ℕ, 1 ≤ n →
      trudiPartitionSum 1 (fun i => (generalizedFussCatalanNumber 3 (i - 1) 2 : ℚ)) n =
        (generalizedFussCatalanNumber 3 n 1 : ℚ)

/-- **Even noncrossing partitions and Dyck paths with even descents.** For every natural number
$n$, there is a bijection between the noncrossing partitions of $\{0, \dots, 2n - 1\}$ all of
whose blocks have even size and the Dyck paths of semilength $2n$ all of whose descents have even
length. Here the descents of a Dyck path are the lengths of its maximal runs of down steps, one
for each peak $UD$: the run of down steps starting at the $D$ of that peak.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Lemma 10
(`jis-2026-26.1.2-lem-10`). -/
public theorem_wanted nonempty_equiv_evenNoncrossing_evenDescentDyck (n : ℕ) :
    Nonempty
      ({P : _root_.NoncrossingPartition (2 * n) // ∀ B ∈ P.val.parts, Even B.card} ≃
        {p : DyckWord // p.semilength = 2 * n ∧ ∀ j ∈ dyckPeakDescents p.toList, Even j})

end

end MetaMathlibExt
