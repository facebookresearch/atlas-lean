/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import MathlibExt.NumberTheory.LucasSequence

/-!
# Subwords in non-decreasing Dyck paths

Statements from Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in
Non-Decreasing Dyck Paths*, Journal of Integer Sequences 28 (2025), Article
25.1.6. Dyck paths are Mathlib's `DyckWord`s. A Dyck path is non-decreasing when
the heights of its valley vertices (the low points of the factors `DU`), read
from left to right, form a non-decreasing sequence; this is the `0`-Dyck case
of Flórez and Ramírez, *Restricted Dyck paths on valleys sequence*,
arXiv:2108.08299, Section 1. A subword is a contiguous factor, and
`nondecreasingDyckSubwordTotal w n` is the total number of occurrences of `w`
(overlapping occurrences counted separately) summed over the non-decreasing
Dyck paths of semilength `n`. The bivariate generating function
`F_w(x, y) = ∑_{n ≥ 1} ∑_{P} x^n y^{#w(P)}` is a power series in `x` with
coefficients in `ℤ[y]`, and the univariate `D_w(x) = ∑ d_w(n) x^n`. Generating
function identities are stated with the denominator cleared, and the closed
forms with the rational factor cleared, over `ℤ`.
-/

namespace MetaMathlibExt

@[expose] public section

open DyckStep

/-- **Valley heights.** For a finite sequence $l$ of up steps $U$ and down steps $D$, the valley
heights of $l$ form the list with one entry for each factor $DU$ of $l$, from left to right:
the number of $U$ steps minus the number of $D$ steps in $l$ up to and including the $D$ of
that factor, taken to be $0$ when negative.

Source: Flórez and Ramírez, *Restricted Dyck paths on valleys sequence*,
arXiv:2108.08299, Section 1, the definition of non-decreasing Dyck paths used by
Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing Dyck
Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6. -/
public def dyckValleyHeights (l : List DyckStep) : List ℕ :=
  ((List.range l.length).filter fun i => decide (l[i]? = some D ∧ l[i + 1]? = some U)).map
    fun i => (l.take (i + 1)).count U - (l.take (i + 1)).count D

/-- **Valley heights of UUDUDDUD.** The Dyck path $UUDUDDUD$ has exactly two valleys, of heights
$1$ and $0$ from left to right.

In particular this path is not non-decreasing.

Source: Flórez and Ramírez, *Restricted Dyck paths on valleys sequence*,
arXiv:2108.08299, Section 1. -/
public theorem dyckValleyHeights_UUDUDDUD :
    dyckValleyHeights [U, U, D, U, D, D, U, D] = [1, 0] := by decide

/-- **Valley heights of UDUUDUDD.** The Dyck path $UDUUDUDD$ has exactly two valleys, of heights
$0$ and $1$ from left to right.

Source: Flórez and Ramírez, *Restricted Dyck paths on valleys sequence*,
arXiv:2108.08299, Section 1. -/
public theorem dyckValleyHeights_UDUUDUDD :
    dyckValleyHeights [U, D, U, U, D, U, D, D] = [0, 1] := by decide

/-- **Non-decreasing Dyck paths.** A Dyck path is non-decreasing when its valley heights (the
heights reached after the $D$ of each factor $DU$), read from left to right, form a
non-decreasing sequence.

Source: Flórez and Ramírez, *Restricted Dyck paths on valleys sequence*,
arXiv:2108.08299, Section 1 (the `0`-Dyck paths), as used by Flórez, Junes,
Montoya, and Ramírez, *Counting Subwords in Non-Decreasing Dyck Paths*, Journal of
Integer Sequences 28 (2025), Article 25.1.6. -/
public def IsNondecreasingDyckPath (p : DyckWord) : Prop :=
  (dyckValleyHeights p.toList).Pairwise (· ≤ ·)

/-- Non-decreasing is decidable.

Source: Flórez and Ramírez, *Restricted Dyck paths on valleys sequence*,
arXiv:2108.08299, Section 1. -/
public instance : DecidablePred IsNondecreasingDyckPath := fun p => by
  unfold IsNondecreasingDyckPath
  infer_instance

/-- **Non-decreasing Dyck paths of semilength $n$.** For a natural number $n$, $D_n$ is the finite
set of Dyck paths of semilength $n$ that are non-decreasing: the heights of their valleys (the
height reached after the $D$ of each factor $DU$), read from left to right, form a non-decreasing
sequence.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public def nondecreasingDyckWords (n : ℕ) : Finset {p : DyckWord // p.semilength = n} :=
  Finset.univ.filter fun p => IsNondecreasingDyckPath p.1

/-- **Five non-decreasing Dyck paths of semilength 3.** There are exactly $5$ non-decreasing
Dyck paths of semilength $3$.

These are all five Dyck paths of semilength $3$.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public theorem card_nondecreasingDyckWords_three : (nondecreasingDyckWords 3).card = 5 := by
  decide +kernel

/-- **Thirteen non-decreasing Dyck paths of semilength 4.** There are exactly $13$
non-decreasing Dyck paths of semilength $4$.

They are all $14$ Dyck paths of semilength $4$ except $UUDUDDUD$.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public theorem card_nondecreasingDyckWords_four : (nondecreasingDyckWords 4).card = 13 := by
  decide +kernel

/-- **Number of occurrences of a subword.** For finite words $w$ and $l$ in the up step $U$ and
the down step $D$, the number of occurrences of $w$ in $l$ is the number of suffixes of $l$,
including $l$ itself and the empty suffix, that begin with $w$. Thus every occurrence of $w$ as a
contiguous subword of $l$ is counted, overlapping occurrences separately.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public def dyckSubwordCount (w l : List DyckStep) : ℕ :=
  l.tails.countP fun t => w.isPrefixOf t

/-- **Occurrences of UU in UUUDDD.** The contiguous subword $UU$ occurs exactly $2$ times in
$UUUDDD$; the two occurrences overlap.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public theorem dyckSubwordCount_UU_UUUDDD :
    dyckSubwordCount [U, U] [U, U, U, D, D, D] = 2 := by decide

/-- **Occurrences of UDU in UDUDUD.** The contiguous subword $UDU$ occurs exactly $2$ times in
$UDUDUD$; the two occurrences overlap.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public theorem dyckSubwordCount_UDU_UDUDUD :
    dyckSubwordCount [U, D, U] [U, D, U, D, U, D] = 2 := by decide

/-- **Total occurrences of a subword in non-decreasing Dyck paths.** For a word $w$ in the steps
$U$ and $D$ and for $n \ge 0$, $d_w(n)$ is the total number of occurrences of $w$ as a contiguous
subword (overlapping occurrences counted separately), summed over all non-decreasing Dyck paths
of semilength $n$.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public def nondecreasingDyckSubwordTotal (w : List DyckStep) (n : ℕ) : ℕ :=
  ∑ p ∈ nondecreasingDyckWords n, dyckSubwordCount w p.1.toList

/-- **Peaks in the non-decreasing Dyck paths of semilength three.** Let $d_w(n)$ be the total
number of occurrences of the subword $w$ over all non-decreasing Dyck paths of semilength $n$.
Then $d_{UD}(3) = 10$; that is, the non-decreasing Dyck paths of semilength $3$ have $10$ peaks
$UD$ in total.

All five Dyck paths of semilength $3$ are non-decreasing.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public theorem nondecreasingDyckSubwordTotal_UD_three :
    nondecreasingDyckSubwordTotal [U, D] 3 = 10 := by
  decide +kernel

/-- **Bivariate generating function of a subword in non-decreasing Dyck paths.** For a word $w$
in the steps $U$ and $D$, let $D_n$ be the set of non-decreasing Dyck paths of semilength $n$,
and let $\#w(P)$ be the number of occurrences of $w$ as a contiguous subword of a path $P$,
overlapping occurrences counted separately. The bivariate generating function $F_w(x, y)$ is
the power series in $x$ with coefficients in $\mathbb{Z}[y]$ given by
$$F_w(x, y) = \sum_{n \ge 1} \sum_{P \in D_n} y^{\#w(P)} x^n,$$
so its constant coefficient is $0$: the empty path is not counted.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public noncomputable def nondecreasingDyckSubwordBivariateGF (w : List DyckStep) :
    PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun n =>
    if n = 0 then 0
    else ∑ p ∈ nondecreasingDyckWords n, Polynomial.X ^ dyckSubwordCount w p.1.toList

/-- **Generating function of the total subword count in non-decreasing Dyck paths.** For a word
$w$ in the steps $U$ and $D$, let $d_w(n)$ be the total number of occurrences of $w$ as a
contiguous subword (overlapping occurrences counted separately) over all non-decreasing Dyck
paths of semilength $n$. The univariate generating function of $w$ is the integer power series
$$D_w(x) = \sum_{n \ge 0} d_w(n) x^n.$$

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public noncomputable def nondecreasingDyckSubwordTotalGF (w : List DyckStep) :
    PowerSeries ℤ :=
  PowerSeries.mk fun n => (nondecreasingDyckSubwordTotal w n : ℤ)

/-- **Height of the last peak.** For a finite sequence $l$ of up steps $U$ and down steps $D$,
the last peak height of $l$ is undefined when $l$ has no factor $UD$. Otherwise it is the
height of the peak of the rightmost factor $UD$: the number of $U$ steps minus the number of
$D$ steps in $l$ up to and including the $U$ of that factor, taken to be $0$ when negative.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 16. -/
public def dyckLastPeakHeight (l : List DyckStep) : Option ℕ :=
  ((List.range l.length).filter fun i =>
      decide (l[i]? = some U ∧ l[i + 1]? = some D)).getLast?.map
    fun i => (l.take (i + 1)).count U - (l.take (i + 1)).count D

/-- **Last peak height of UDUUDD.** The last peak of the Dyck path $UDUUDD$ has height $2$.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 16. -/
public theorem dyckLastPeakHeight_UDUUDD :
    dyckLastPeakHeight [U, D, U, U, D, D] = some 2 := by decide

/-- **Non-decreasing Dyck paths by height of the last peak.** For natural numbers $n$ and $k$,
$l_{n,k}$ is the number of non-decreasing Dyck paths of semilength $n$ whose last peak (the last
factor $UD$) has height $k$.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 16. -/
public def nondecreasingDyckLastPeakCount (n k : ℕ) : ℕ :=
  ((nondecreasingDyckWords n).filter fun p => dyckLastPeakHeight p.1.toList = some k).card

/-- **Non-decreasing Dyck paths of semilength four with last peak at height one.** Exactly four
non-decreasing Dyck paths of semilength $4$ have their last peak at height $1$; that is,
$l_{4,1} = 4$, where $l_{n,k}$ is the number of non-decreasing Dyck paths of semilength $n$
whose last peak has height $k$.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 16. -/
public theorem nondecreasingDyckLastPeakCount_four_one :
    nondecreasingDyckLastPeakCount 4 1 = 4 := by
  decide +kernel

/-- The variable `x` of the bivariate generating functions. -/
local notation "𝒙" => (PowerSeries.X : PowerSeries (Polynomial ℤ))
/-- The variable `y` of the bivariate generating functions, a constant in `ℤ[y]`. -/
local notation "𝒚" => PowerSeries.C (Polynomial.X : Polynomial ℤ)
/-- The variable `x` of the univariate generating functions. -/
local notation "𝒛" => (PowerSeries.X : PowerSeries ℤ)

/-- **Generating functions and closed form for the subword $UD$ in non-decreasing Dyck paths.**
For $n \ge 0$ let $\mathcal{D}_n$ be the set of non-decreasing Dyck paths of semilength $n$, let
$\#_{UD}(P)$ be the number of occurrences of the subword $UD$ in a path $P$, and let
$d_{UD}(n) = \sum_{P \in \mathcal{D}_n} \#_{UD}(P)$. Let
$F_{UD}(x, y) = \sum_{n \ge 1} \sum_{P \in \mathcal{D}_n} y^{\#_{UD}(P)} x^n$, a power series in
$x$ with coefficients in $\mathbb{Z}[y]$, and $D_{UD}(x) = \sum_{n \ge 0} d_{UD}(n) x^n$ in
$\mathbb{Z}[[x]]$. Then $(1 - 2x + x^2 - xy) F_{UD}(x, y) = (1 - x) x y$ and
$(1 - 3x + x^2)^2 D_{UD}(x) = x (1 - x)^3$, and for every $n \ge 1$,
$$10\, d_{UD}(n) = (5n - 7) F_{2n} - (n - 5) L_{2n},$$
where $F_k$ and $L_k$ are the Fibonacci and Lucas numbers ($F_0 = 0$, $F_1 = 1$, $L_0 = 2$,
$L_1 = 1$).

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 1
(`jis-2025-25.1.6-thm-1`). -/
public theorem_wanted nondecreasingDyck_subword_UD :
    (1 - 2 * 𝒙 + 𝒙 ^ 2 - 𝒙 * 𝒚) * nondecreasingDyckSubwordBivariateGF [U, D] = (1 - 𝒙) * 𝒙 * 𝒚 ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [U, D] = 𝒛 * (1 - 𝒛) ^ 3 ∧
    ∀ n : ℕ, 1 ≤ n →
      10 * (nondecreasingDyckSubwordTotal [U, D] n : ℤ) =
        (5 * (n : ℤ) - 7) * (Nat.fib (2 * n) : ℤ) - ((n : ℤ) - 5) * (lucasNumber (2 * n) : ℤ)

/-- **The subword $DU$ in non-decreasing Dyck paths.** Let $F_{DU}(x, y)$ and $D_{DU}(x)$ be the
bivariate and univariate generating functions of the subword $DU$ in non-decreasing Dyck paths,
let $d_{DU}(n)$ be the total number of occurrences of $DU$ over all non-decreasing Dyck paths of
semilength $n$, and let $F_n$ and $L_n$ denote the Fibonacci and Lucas numbers. Then
$$(1 - 2x + x^2 - xy) F_{DU}(x, y) = (1 - x) x$$
in $\mathbb{Z}[y][[x]]$,
$$(1 - 3x + x^2)^2 D_{DU}(x) = (1 - x) x^2$$
in $\mathbb{Z}[[x]]$, and for every $n \ge 1$,
$$10 d_{DU}(n) = (5n - 2) F_{2n} - n L_{2n}.$$

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 2
(`jis-2025-25.1.6-thm-2`). -/
public theorem_wanted nondecreasingDyck_subword_DU :
    (1 - 2 * 𝒙 + 𝒙 ^ 2 - 𝒙 * 𝒚) * nondecreasingDyckSubwordBivariateGF [D, U] = (1 - 𝒙) * 𝒙 ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [D, U] = (1 - 𝒛) * 𝒛 ^ 2 ∧
    ∀ n : ℕ, 1 ≤ n →
      10 * (nondecreasingDyckSubwordTotal [D, U] n : ℤ) =
        (5 * (n : ℤ) - 2) * (Nat.fib (2 * n) : ℤ) - (n : ℤ) * (lucasNumber (2 * n) : ℤ)

/-- **Generating functions and closed form for the subwords $UU$ and $DD$ in non-decreasing Dyck
paths.** Let $w$ be $UU$ or $DD$. For $n \ge 0$ let $\mathcal{D}_n$ be the set of non-decreasing
Dyck paths of semilength $n$, let $\#_w(P)$ be the number of occurrences of the subword $w$ in a
path $P$, and let $d_w(n) = \sum_{P \in \mathcal{D}_n} \#_w(P)$. Let
$F_w(x, y) = \sum_{n \ge 1} \sum_{P \in \mathcal{D}_n} y^{\#_w(P)} x^n$, a power series in $x$
with coefficients in $\mathbb{Z}[y]$, and $D_w(x) = \sum_{n \ge 0} d_w(n) x^n$ in
$\mathbb{Z}[[x]]$. Then $(1 - x - 2xy + x^2 y^2) F_w(x, y) = x (1 - xy)$ and
$(1 - 3x + x^2)^2 D_w(x) = x^2 (1 - x + x^2)$, and for every $n \ge 1$,
$$10\, d_w(n) = (7 - 10n) F_{2n} + (6n - 5) L_{2n},$$
where $F_k$ and $L_k$ are the Fibonacci and Lucas numbers ($F_0 = 0$, $F_1 = 1$, $L_0 = 2$,
$L_1 = 1$).

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 3
(`jis-2025-25.1.6-thm-3`). -/
public theorem_wanted nondecreasingDyck_subword_UU_DD (w : List DyckStep)
    (hw : w = [U, U] ∨ w = [D, D]) :
    (1 - 𝒙 - 2 * 𝒙 * 𝒚 + 𝒙 ^ 2 * 𝒚 ^ 2) * nondecreasingDyckSubwordBivariateGF w =
      𝒙 * (1 - 𝒙 * 𝒚) ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF w = 𝒛 ^ 2 * (1 - 𝒛 + 𝒛 ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n →
      10 * (nondecreasingDyckSubwordTotal w n : ℤ) =
        (7 - 10 * (n : ℤ)) * (Nat.fib (2 * n) : ℤ) + (6 * (n : ℤ) - 5) * (lucasNumber (2 * n) : ℤ)

/-- **Subword $UUU$ in non-decreasing Dyck paths.** Let $F_{UUU}(x, y) \in \mathbb{Z}[y][[x]]$ be
the bivariate generating function with constant term $0$ in which, for $n \ge 1$, the coefficient
of $x^n$ is the sum of $y^{k(P)}$ over the non-decreasing Dyck paths $P$ of semilength $n$, where
$k(P)$ is the number of occurrences of the subword $UUU$ in $P$ (overlapping occurrences counted
separately). Let $d_{UUU}(n)$ be the total number of occurrences of $UUU$ over all non-decreasing
Dyck paths of semilength $n$, let $D_{UUU}(x) = \sum_{n \ge 0} d_{UUU}(n) x^n \in \mathbb{Z}[[x]]$,
and let $F_n$ and $L_n$ denote the Fibonacci and Lucas numbers. Then
$(1 - x(2 + y) + x^2 y) F_{UUU}(x, y) = (1 - xy) x$, $(1 - 3x + x^2)^2 D_{UUU}(x) = x^3$, and
for every $n \ge 1$, $10\, d_{UUU}(n) = -(5n + 4) F_{2n} + 3n L_{2n}$.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 4
(`jis-2025-25.1.6-thm-4`). -/
public theorem_wanted nondecreasingDyck_subword_UUU :
    (1 - 𝒙 * (2 + 𝒚) + 𝒙 ^ 2 * 𝒚) * nondecreasingDyckSubwordBivariateGF [U, U, U]
        = (1 - 𝒙 * 𝒚) * 𝒙 ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [U, U, U] = 𝒛 ^ 3 ∧
    ∀ n : ℕ, 1 ≤ n →
      10 * (nondecreasingDyckSubwordTotal [U, U, U] n : ℤ) =
        -(5 * (n : ℤ) + 4) * (Nat.fib (2 * n) : ℤ) + 3 * (n : ℤ) * (lucasNumber (2 * n) : ℤ)

/-- **Generating functions and closed form for the subword $UDU$ in non-decreasing Dyck paths.**
For $n \ge 0$ let $\mathcal{D}_n$ be the set of non-decreasing Dyck paths of semilength $n$, let
$\#_{UDU}(P)$ be the number of occurrences of the subword $UDU$ in a path $P$, and let
$d_{UDU}(n) = \sum_{P \in \mathcal{D}_n} \#_{UDU}(P)$. Let
$F_{UDU}(x, y) = \sum_{n \ge 1} \sum_{P \in \mathcal{D}_n} y^{\#_{UDU}(P)} x^n$, a power series
in $x$ with coefficients in $\mathbb{Z}[y]$, and $D_{UDU}(x) = \sum_{n \ge 0} d_{UDU}(n) x^n$ in
$\mathbb{Z}[[x]]$. Then $(1 - x(2 + y) + x^2 y) F_{UDU}(x, y) = (1 - x) x$ and
$(1 - 3x + x^2)^2 D_{UDU}(x) = x^2 (1 - x)^2$, and for every $n \ge 1$,
$$10\, d_{UDU}(n) = (11 - 5n) F_{2n} + (3n - 5) L_{2n},$$
where $F_k$ and $L_k$ are the Fibonacci and Lucas numbers ($F_0 = 0$, $F_1 = 1$, $L_0 = 2$,
$L_1 = 1$).

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 5
(`jis-2025-25.1.6-thm-5`). -/
public theorem_wanted nondecreasingDyck_subword_UDU :
    (1 - 𝒙 * (2 + 𝒚) + 𝒙 ^ 2 * 𝒚) * nondecreasingDyckSubwordBivariateGF [U, D, U] = (1 - 𝒙) * 𝒙 ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [U, D, U] = 𝒛 ^ 2 * (1 - 𝒛) ^ 2 ∧
    ∀ n : ℕ, 1 ≤ n →
      10 * (nondecreasingDyckSubwordTotal [U, D, U] n : ℤ) =
        (-5 * (n : ℤ) + 11) * (Nat.fib (2 * n) : ℤ) + (3 * (n : ℤ) - 5) * (lucasNumber (2 * n) : ℤ)

/-- **Generating functions and closed form for the subword $UDD$ in non-decreasing Dyck paths.**
For $n \ge 0$ let $\mathcal{D}_n$ be the set of non-decreasing Dyck paths of semilength $n$, let
$\#_{UDD}(P)$ be the number of occurrences of the subword $UDD$ in a path $P$, and let
$d_{UDD}(n) = \sum_{P \in \mathcal{D}_n} \#_{UDD}(P)$. Let
$F_{UDD}(x, y) = \sum_{n \ge 1} \sum_{P \in \mathcal{D}_n} y^{\#_{UDD}(P)} x^n$, a power series
in $x$ with coefficients in $\mathbb{Z}[y]$, and $D_{UDD}(x) = \sum_{n \ge 0} d_{UDD}(n) x^n$ in
$\mathbb{Z}[[x]]$. Then
$$(1 - 3x + x^2 (2 - y)) (1 - 2x + x^2 (1 - y)) F_{UDD}(x, y) = (1 - x)(1 - 2x)(1 - x(1 - y)) x$$
and
$$(1 - 2x)(1 - 3x + x^2)^2 D_{UDD}(x) = (1 - x)(1 - 3x + 2x^2 - x^3) x^2,$$
and for every $n \ge 2$,
$$5\, d_{UDD}(n) = (5n - 9) F_{2n} + (5 - 2n) L_{2n} - 5 \cdot 2^{n-2},$$
where $F_k$ and $L_k$ are the Fibonacci and Lucas numbers ($F_0 = 0$, $F_1 = 1$, $L_0 = 2$,
$L_1 = 1$).

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 6
(`jis-2025-25.1.6-thm-6`). -/
public theorem_wanted nondecreasingDyck_subword_UDD :
    ((1 - 3 * 𝒙 + 𝒙 ^ 2 * (2 - 𝒚)) * (1 - 2 * 𝒙 + 𝒙 ^ 2 * (1 - 𝒚)))
        * nondecreasingDyckSubwordBivariateGF [U, D, D]
        = (1 - 𝒙) * (1 - 2 * 𝒙) * (1 - 𝒙 * (1 - 𝒚)) * 𝒙 ∧
    ((1 - 2 * 𝒛) * (1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [U, D, D]
        = (1 - 𝒛) * (1 - 3 * 𝒛 + 2 * 𝒛 ^ 2 - 𝒛 ^ 3) * 𝒛 ^ 2 ∧
    ∀ n : ℕ, 2 ≤ n →
      5 * (nondecreasingDyckSubwordTotal [U, D, D] n : ℤ) =
        (5 * (n : ℤ) - 9) * (Nat.fib (2 * n) : ℤ) + (-2 * (n : ℤ) + 5) * (lucasNumber (2 * n) : ℤ)
            - 5 * 2 ^ (n - 2)

/-- **The subword $DUU$ in non-decreasing Dyck paths.** Let $F_{DUU}(x, y)$ and $D_{DUU}(x)$ be
the bivariate and univariate generating functions of the subword $DUU$ in non-decreasing Dyck
paths, let $d_{DUU}(n)$ be the total number of occurrences of $DUU$ over all non-decreasing Dyck
paths of semilength $n$, and let $F_n$ and $L_n$ denote the Fibonacci and Lucas numbers. Then
$$(1 - 3x + x^2(3 - 2y) - x^3(1 - y)) F_{DUU}(x, y) = x - x^2 + x^3(1 - y)$$
in $\mathbb{Z}[y][[x]]$,
$$(1 - 3x + x^2)^2 D_{DUU}(x) = x^3$$
in $\mathbb{Z}[[x]]$, and for every $n \ge 3$,
$$10 d_{DUU}(n) = -(5n + 4) F_{2n} + 3n L_{2n}.$$

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 7
(`jis-2025-25.1.6-thm-7`). -/
public theorem_wanted nondecreasingDyck_subword_DUU :
    (1 - 3 * 𝒙 + 𝒙 ^ 2 * (3 - 2 * 𝒚) - 𝒙 ^ 3 * (1 - 𝒚))
        * nondecreasingDyckSubwordBivariateGF [D, U, U] = 𝒙 - 𝒙 ^ 2 + 𝒙 ^ 3 * (1 - 𝒚) ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [D, U, U] = 𝒛 ^ 3 ∧
    ∀ n : ℕ, 3 ≤ n →
      10 * (nondecreasingDyckSubwordTotal [D, U, U] n : ℤ) =
        -(5 * (n : ℤ) + 4) * (Nat.fib (2 * n) : ℤ) + 3 * (n : ℤ) * (lucasNumber (2 * n) : ℤ)

/-- **The subword $DUD$ in non-decreasing Dyck paths.** Let $F_{DUD}(x, y)$ and $D_{DUD}(x)$ be
the bivariate and univariate generating functions of the subword $DUD$ in non-decreasing Dyck
paths, let $d_{DUD}(n)$ be the total number of occurrences of $DUD$ over all non-decreasing Dyck
paths of semilength $n$, and let $F_n$ and $L_n$ denote the Fibonacci and Lucas numbers. Then
$$(1 - x^2(1 - 2y) + x^3(1 - y) - x(2 + y)) F_{DUD}(x, y) = x (1 - x - x^2(1 - y))$$
in $\mathbb{Z}[y][[x]]$,
$$(1 - 3x + x^2)^2 D_{DUD}(x) = x^2 - 2x^3$$
in $\mathbb{Z}[[x]]$, and for every $n \ge 3$,
$$5 d_{DUD}(n) = (5n + 1) F_{2n} - 2n L_{2n}.$$

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 8
(`jis-2025-25.1.6-thm-8`). -/
public theorem_wanted nondecreasingDyck_subword_DUD :
    (1 - 𝒙 ^ 2 * (1 - 2 * 𝒚) + 𝒙 ^ 3 * (1 - 𝒚) - 𝒙 * (2 + 𝒚))
        * nondecreasingDyckSubwordBivariateGF [D, U, D] = 𝒙 * (1 - 𝒙 - 𝒙 ^ 2 * (1 - 𝒚)) ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [D, U, D] = 𝒛 ^ 2 - 2 * 𝒛 ^ 3 ∧
    ∀ n : ℕ, 3 ≤ n →
      5 * (nondecreasingDyckSubwordTotal [D, U, D] n : ℤ) =
        (5 * (n : ℤ) + 1) * (Nat.fib (2 * n) : ℤ) - 2 * (n : ℤ) * (lucasNumber (2 * n) : ℤ)

/-- **The subword $DDU$ in non-decreasing Dyck paths.** Let $F_{DDU}(x, y)$ and $D_{DDU}(x)$ be
the bivariate and univariate generating functions of the subword $DDU$ in non-decreasing Dyck
paths, let $d_{DDU}(n)$ be the total number of occurrences of $DDU$ over all non-decreasing Dyck
paths of semilength $n$, and let $F_n$ and $L_n$ denote the Fibonacci and Lucas numbers. Then
$$(1 - 3x + x^2(2 - y)) F_{DDU}(x, y) = (1 - x) x$$
in $\mathbb{Z}[y][[x]]$,
$$(1 - 3x + x^2)^2 D_{DDU}(x) = (1 - x) x^3$$
in $\mathbb{Z}[[x]]$, and for every $n \ge 3$,
$$10 d_{DDU}(n) = (10n - 13) F_{2n} + (-4n + 5) L_{2n}.$$

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 9
(`jis-2025-25.1.6-thm-9`). -/
public theorem_wanted nondecreasingDyck_subword_DDU :
    (1 - 3 * 𝒙 + 𝒙 ^ 2 * (2 - 𝒚)) * nondecreasingDyckSubwordBivariateGF [D, D, U] = (1 - 𝒙) * 𝒙 ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [D, D, U] = (1 - 𝒛) * 𝒛 ^ 3 ∧
    ∀ n : ℕ, 3 ≤ n →
      10 * (nondecreasingDyckSubwordTotal [D, D, U] n : ℤ) =
        (10 * (n : ℤ) - 13) * (Nat.fib (2 * n) : ℤ) + (-4 * (n : ℤ) + 5) * (lucasNumber (2 * n) : ℤ)

/-- **The subword $DDD$ in non-decreasing Dyck paths.** Let $F_{DDD}(x, y)$ and $D_{DDD}(x)$ be
the bivariate and univariate generating functions of the subword $DDD$ in non-decreasing Dyck
paths, let $d_{DDD}(n)$ be the total number of occurrences of $DDD$ over all non-decreasing Dyck
paths of semilength $n$, and let $F_n$ and $L_n$ denote the Fibonacci and Lucas numbers. Then
$$(1 - x(1 + y) - x^2(1 - y)) (1 - x(1 + 2y) - x^2(1 - y - y^2)) F_{DDD}(x, y) =
x (1 - xy) (1 - 2xy - x^2(1 - y^2))$$
in $\mathbb{Z}[y][[x]]$,
$$(1 - 2x) (1 - 3x + x^2)^2 D_{DDD}(x) = x^3 (1 - 2x + x^2 - x^3)$$
in $\mathbb{Z}[[x]]$, and for every $n \ge 3$,
$$4 d_{DDD}(n) = (-8n + 10) F_{2n} + (4n - 6) L_{2n} + 2^n.$$

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 10
(`jis-2025-25.1.6-thm-10`). -/
public theorem_wanted nondecreasingDyck_subword_DDD :
    ((1 - 𝒙 * (1 + 𝒚) - 𝒙 ^ 2 * (1 - 𝒚)) * (1 - 𝒙 * (1 + 2 * 𝒚) - 𝒙 ^ 2 * (1 - 𝒚 - 𝒚 ^ 2)))
        * nondecreasingDyckSubwordBivariateGF [D, D, D]
        = 𝒙 * (1 - 𝒙 * 𝒚) * (1 - 2 * 𝒙 * 𝒚 - 𝒙 ^ 2 * (1 - 𝒚 ^ 2)) ∧
    ((1 - 2 * 𝒛) * (1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [D, D, D]
        = 𝒛 ^ 3 * (1 - 2 * 𝒛 + 𝒛 ^ 2 - 𝒛 ^ 3) ∧
    ∀ n : ℕ, 3 ≤ n →
      4 * (nondecreasingDyckSubwordTotal [D, D, D] n : ℤ) =
        (-8 * (n : ℤ) + 10) * (Nat.fib (2 * n) : ℤ) + (4 * (n : ℤ) - 6) * (lucasNumber (2 * n) : ℤ)
            + 2 ^ n

/-- **Generating functions and closed form for the subword $UUD$ in non-decreasing Dyck paths.**
For $n \ge 0$ let $\mathcal{D}_n$ be the set of non-decreasing Dyck paths of semilength $n$, let
$\#_{UUD}(P)$ be the number of occurrences of the subword $UUD$ in a path $P$, and let
$d_{UUD}(n) = \sum_{P \in \mathcal{D}_n} \#_{UUD}(P)$. Let
$F_{UUD}(x, y) = \sum_{n \ge 1} \sum_{P \in \mathcal{D}_n} y^{\#_{UUD}(P)} x^n$, a power series
in $x$ with coefficients in $\mathbb{Z}[y]$, and $D_{UUD}(x) = \sum_{n \ge 0} d_{UUD}(n) x^n$ in
$\mathbb{Z}[[x]]$. Then
$$(1 - 3x + x^2 (3 - 2y) - x^3 (1 - y)) F_{UUD}(x, y) = (1 - x) x (1 - x(1 - y))$$
and $(1 - 3x + x^2)^2 D_{UUD}(x) = (1 - x)^2 x^2$, and for every $n \ge 3$,
$$10\, d_{UUD}(n) = (11 - 5n) F_{2n} + (3n - 5) L_{2n},$$
where $F_k$ and $L_k$ are the Fibonacci and Lucas numbers ($F_0 = 0$, $F_1 = 1$, $L_0 = 2$,
$L_1 = 1$).

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 11
(`jis-2025-25.1.6-thm-11`). -/
public theorem_wanted nondecreasingDyck_subword_UUD :
    (1 - 3 * 𝒙 + 𝒙 ^ 2 * (3 - 2 * 𝒚) - 𝒙 ^ 3 * (1 - 𝒚))
        * nondecreasingDyckSubwordBivariateGF [U, U, D] = (1 - 𝒙) * 𝒙 * (1 - 𝒙 * (1 - 𝒚)) ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [U, U, D] = (1 - 𝒛) ^ 2 * 𝒛 ^ 2 ∧
    ∀ n : ℕ, 3 ≤ n →
      10 * (nondecreasingDyckSubwordTotal [U, U, D] n : ℤ) =
        (-5 * (n : ℤ) + 11) * (Nat.fib (2 * n) : ℤ) + (3 * (n : ℤ) - 5) * (lucasNumber (2 * n) : ℤ)

/-- **Subword $UUUD$ in non-decreasing Dyck paths.** Let $F_{UUUD}(x, y) \in \mathbb{Z}[y][[x]]$ be
the bivariate generating function with constant term $0$ in which, for $n \ge 1$, the coefficient
of $x^n$ is the sum of $y^{k(P)}$ over the non-decreasing Dyck paths $P$ of semilength $n$, where
$k(P)$ is the number of occurrences of the subword $UUUD$ in $P$. Let $d_{UUUD}(n)$ be the total
number of occurrences of $UUUD$ over all non-decreasing Dyck paths of semilength $n$, let
$D_{UUUD}(x) = \sum_{n \ge 0} d_{UUUD}(n) x^n \in \mathbb{Z}[[x]]$, and let $F_n$ and $L_n$ denote
the Fibonacci and Lucas numbers. Then
$(1 - 3x + x^2 + (3 - 3y) x^3 - 2(1 - y) x^4) F_{UUUD}(x, y) = (1 - x)(x + x^3 (y - 1))$,
$(1 + x(x - 3))^2 D_{UUUD}(x) = (x - 1)^2 x^3 (x + 1)$, and for every $n \ge 3$,
$d_{UUUD}(n) = n F_{2n-5} - L_{2n-6}$.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 12
(`jis-2025-25.1.6-thm-12`). -/
public theorem_wanted nondecreasingDyck_subword_UUUD :
    (1 - 3 * 𝒙 + 𝒙 ^ 2 + (3 - 3 * 𝒚) * 𝒙 ^ 3 - 2 * (1 - 𝒚) * 𝒙 ^ 4)
        * nondecreasingDyckSubwordBivariateGF [U, U, U, D] = (1 - 𝒙) * (𝒙 + 𝒙 ^ 3 * (𝒚 - 1)) ∧
    ((1 + 𝒛 * (𝒛 - 3)) ^ 2) * nondecreasingDyckSubwordTotalGF [U, U, U, D]
        = (𝒛 - 1) ^ 2 * 𝒛 ^ 3 * (𝒛 + 1) ∧
    ∀ n : ℕ, 3 ≤ n →
      (nondecreasingDyckSubwordTotal [U, U, U, D] n : ℤ) =
        (n : ℤ) * (Nat.fib (2 * n - 5) : ℤ) - (lucasNumber (2 * n - 6) : ℤ)

/-- **Recurrence for the subword $U^m$ in non-decreasing Dyck paths.** Let $m \ge 1$. Let
$d_w(n)$ be the total number of occurrences of the subword $w$ over all non-decreasing Dyck paths
of semilength $n$, and let $F_k$ be the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$). Then for every
$n > m$,
$$d_{U^m}(n) = 3\,d_{U^m}(n-1) - d_{U^m}(n-2) + F_{2(n-m)} + F_{2(n-2)} -
\sum_{k=1}^{m-2} k\,F_{2(n-k-2)}$$
(the sum is empty when $m \le 2$); moreover $d_{U^m}(n) = 0$ for every $n < m$, and
$d_{U^m}(m) = 1$.

The source writes $n \le m$ for the vanishing case, which contradicts $d_{U^m}(m) = 1$; the
vanishing case is stated for $n < m$.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 13
(`jis-2025-25.1.6-thm-13`). -/
public theorem_wanted nondecreasingDyck_subword_U_pow (m : ℕ) (hm : 1 ≤ m) :
    (∀ n : ℕ, m < n →
      (nondecreasingDyckSubwordTotal (List.replicate m U) n : ℤ) =
        3 * (nondecreasingDyckSubwordTotal (List.replicate m U) (n - 1) : ℤ)
          - (nondecreasingDyckSubwordTotal (List.replicate m U) (n - 2) : ℤ)
          + (Nat.fib (2 * (n - m)) : ℤ) + (Nat.fib (2 * (n - 2)) : ℤ)
          - ∑ k ∈ Finset.Icc 1 (m - 2), (k : ℤ) * (Nat.fib (2 * (n - k - 2)) : ℤ)) ∧
    (∀ n : ℕ, n < m → nondecreasingDyckSubwordTotal (List.replicate m U) n = 0) ∧
    nondecreasingDyckSubwordTotal (List.replicate m U) m = 1

/-- **Recurrence for the subword $U^mD$ in non-decreasing Dyck paths.** Let $m \ge 1$. Let
$d_w(n)$ be the total number of occurrences of the subword $w$ over all non-decreasing Dyck paths
of semilength $n$, and let $F_k$ be the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$). Then for every
$n \ge m + 2$,
$$d_{U^mD}(n) = 3\,d_{U^mD}(n-1) - d_{U^mD}(n-2) + F_{2(n-m)-3} + m\,F_{2(n-m-1)};$$
moreover $d_{U^mD}(n) = 0$ for every $n < m$, $d_{U^mD}(m) = 1$, and $d_{U^mD}(m+1) = m + 2$.

The source states the recurrence for $n \ge m$, where $n = m$ and $n = m + 1$ give negative
Fibonacci indices; those two values are the separately stated initial values, and the recurrence
is stated for $n \ge m + 2$.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 15
(`jis-2025-25.1.6-thm-15`). -/
public theorem_wanted nondecreasingDyck_subword_U_pow_D (m : ℕ) (hm : 1 ≤ m) :
    (∀ n : ℕ, m + 2 ≤ n →
      (nondecreasingDyckSubwordTotal (List.replicate m U ++ [D]) n : ℤ) =
        3 * (nondecreasingDyckSubwordTotal (List.replicate m U ++ [D]) (n - 1) : ℤ)
          - (nondecreasingDyckSubwordTotal (List.replicate m U ++ [D]) (n - 2) : ℤ)
          + (Nat.fib (2 * (n - m) - 3) : ℤ) + (m : ℤ) * (Nat.fib (2 * (n - m - 1)) : ℤ)) ∧
    (∀ n : ℕ, n < m → nondecreasingDyckSubwordTotal (List.replicate m U ++ [D]) n = 0) ∧
    nondecreasingDyckSubwordTotal (List.replicate m U ++ [D]) m = 1 ∧
    nondecreasingDyckSubwordTotal (List.replicate m U ++ [D]) (m + 1) = m + 2

/-- **Recurrence for the subword $UD^m$ in non-decreasing Dyck paths.** Let $m \ge 1$. Let
$d_w(n)$ be the total number of occurrences of the subword $w$ over all non-decreasing Dyck paths
of semilength $n$, let $l_{n,k}$ be the number of non-decreasing Dyck paths of semilength $n$
whose last peak has height $k$, and let $F_k$ be the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$).
Then for every $n$ with $n > m$ and $n \ge 3$,
$$d_{UD^m}(n) = 3\,d_{UD^m}(n-1) - d_{UD^m}(n-2) + F_{2(n-m)-1} + l_{n-1,m-1} - l_{n-2,m-1};$$
moreover $d_{UD^m}(n) = 0$ for every $n < m$, and $d_{UD^m}(m) = 1$.

The source states the recurrence for $n \ge m$; $n = m$ is the separately stated initial value,
and the added condition $n \ge 3$ excludes only $(m, n) = (1, 2)$, where $d_{UD}(2) = 3$ but the
right side is $3 \cdot 1 - 0 + F_1 + l_{1,0} - l_{0,0} = 4$ (the empty path has no peak).

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 16
(`jis-2025-25.1.6-thm-16`). -/
public theorem_wanted nondecreasingDyck_subword_U_D_pow (m : ℕ) (hm : 1 ≤ m) :
    (∀ n : ℕ, m < n → 3 ≤ n →
      (nondecreasingDyckSubwordTotal (U :: List.replicate m D) n : ℤ) =
        3 * (nondecreasingDyckSubwordTotal (U :: List.replicate m D) (n - 1) : ℤ)
          - (nondecreasingDyckSubwordTotal (U :: List.replicate m D) (n - 2) : ℤ)
          + (Nat.fib (2 * (n - m) - 1) : ℤ)
          + (nondecreasingDyckLastPeakCount (n - 1) (m - 1) : ℤ)
          - (nondecreasingDyckLastPeakCount (n - 2) (m - 1) : ℤ)) ∧
    (∀ n : ℕ, n < m → nondecreasingDyckSubwordTotal (U :: List.replicate m D) n = 0) ∧
    nondecreasingDyckSubwordTotal (U :: List.replicate m D) m = 1

end

end MetaMathlibExt
