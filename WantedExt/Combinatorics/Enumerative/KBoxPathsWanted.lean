/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Rat.Defs
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# `k`-box paths: a subfamily of skew Dyck paths related to `k`-ary trees

Statements from Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to
`k`-ary Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4
(arXiv:2306.15778). Skew Dyck paths are words over `{U, D, L}` that avoid the
factors `UL` and `LU`, have as many `U`s as `D`s and `L`s together, and have no
prefix with more `D`s and `L`s than `U`s; the semilength is the number of `U`s.
A `k`-box path of size `n` (`k ≥ 1`) is a skew Dyck path of semilength
`(k+2)n - 1` with exactly `n` factors `U D^k L`. A `k`-Dyck path is a word over
`Bool` (`true` for `U = (1,1)`, `false` for `D^{(k)} = (k,-k)`), and an
augmented `k`-Dyck path replaces each `D^{(k)}` by `U D^{k-1} L D`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Skew Dyck steps.** A skew Dyck path is built from three kinds of step: the up step
$U = (1,1)$, the down step $D = (1,-1)$ and the left step $L = (-1,-1)$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 1. -/
public inductive SkewDyckStep
  | U
  | D
  | L
  deriving DecidableEq

open SkewDyckStep

/-- The three steps form a finite type.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 1. -/
public instance : Fintype SkewDyckStep where
  elems := {U, D, L}
  complete := by intro x; cases x <;> simp

/-- **Skew Dyck words.** A word $w$ in the steps $U$, $D$, $L$ is a skew Dyck word when neither
$UL$ nor $LU$ occurs in $w$ as two consecutive letters, the number of $U$s in $w$ equals the
number of $D$s and $L$s together, and no prefix of $w$ has more $D$s and $L$s together than
$U$s.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 1. -/
public def IsSkewDyckWord (w : List SkewDyckStep) : Prop :=
  ¬ [U, L] <:+: w ∧ ¬ [L, U] <:+: w ∧ w.count U = w.count D + w.count L ∧
    ∀ i ≤ w.length, (w.take i).count D + (w.take i).count L ≤ (w.take i).count U

/-- Being a skew Dyck word is decidable.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 1. -/
public instance : DecidablePred IsSkewDyckWord := fun w => by
  unfold IsSkewDyckWord
  infer_instance

/-- **Skew Dyck paths of semilength $m$.** For $m \in \mathbb{N}$, the skew Dyck paths of
semilength $m$ are the words of length $2m$ over $\{U, D, L\}$ that avoid the factors $UL$ and
$LU$, have as many $U$s as $D$s and $L$s together, and have no prefix with more $D$s and $L$s
together than $U$s.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 1. -/
public def skewDyckWords (m : ℕ) : Finset (List SkewDyckStep) :=
  ((Finset.univ : Finset (Fin (2 * m) → SkewDyckStep)).image List.ofFn).filter IsSkewDyckWord

/-- **Three skew Dyck paths of semilength $2$.** The number of skew Dyck paths of semilength
$2$ is $3$.

They are $UUDD$, $UDUD$ and $UUDL$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 1. -/
public theorem card_skewDyckWords_two : (skewDyckWords 2).card = 3 := by
  decide +kernel

/-- **Occurrences of a factor in a skew Dyck word.** For words $f$ and $w$ over the skew Dyck
steps $U$, $D$, $L$, the factor count of $f$ in $w$ is the number of suffixes of $w$, including
$w$ itself and the empty suffix, that begin with $f$. Equivalently, it is the number of positions
of $w$ at which an occurrence of $f$ as a contiguous block starts, overlapping occurrences all
being counted; in particular the empty word has factor count $|w| + 1$ in $w$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 1. -/
public def skewFactorCount (f w : List SkewDyckStep) : ℕ :=
  w.tails.countP fun t => f.isPrefixOf t

/-- **The $k$-box factor.** For $k \ge 0$, the $k$-box factor is the word $U D^k L$ in the skew
Dyck steps: one step $U$, then $k$ steps $D$, then one step $L$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 3. -/
public def boxFactor (k : ℕ) : List SkewDyckStep :=
  U :: List.replicate k D ++ [L]

/-- **$k$-box paths.** For natural numbers $k$ and $n$, the set $B_n^{(k)}$ of $k$-box paths of
size $n$ consists of the skew Dyck paths of semilength $(k+2)n - 1$ that contain exactly $n$
occurrences of the factor $U D^k L$. The subtraction is truncated at $0$, so $B_0^{(k)}$
consists of the empty path alone.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 3. -/
public def kBoxPaths (k n : ℕ) : Finset (List SkewDyckStep) :=
  (skewDyckWords ((k + 2) * n - 1)).filter fun w => skewFactorCount (boxFactor k) w = n

/-- **The $1$-box path of size $1$.** The only $1$-box path of size $1$ is $UUDL$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 3. -/
public theorem kBoxPaths_one_one : kBoxPaths 1 1 = {[U, U, D, L]} := by
  decide +kernel

/-- **Box words.** Let $k \ge 0$ and let $a = (a_1, \dots, a_n)$ be a list of natural numbers
with $n \ge 1$. The box word of $k$ and $a$ is the word in the skew Dyck steps
$$
U^{a_1} D^k L D \; U^{a_2} D^k L D \; \cdots \; U^{a_{n-1}} D^k L D \; U^{a_n} D^k L,
$$
that is, the blocks $U^{a_i} D^k L D$ for $i < n$ followed by $U^{a_n} D^k L$. For the empty
list it is $D^k L$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Lemma 2. -/
public def boxWord (k : ℕ) (a : List ℕ) : List SkewDyckStep :=
  (a.dropLast.flatMap fun x => List.replicate x U ++ List.replicate k D ++ [L, D]) ++
    List.replicate (a.getLastD 0) U ++ List.replicate k D ++ [L]

/-- **The box word for $k = 1$ and $a = (3, 2)$.** For $k = 1$ and $a = (3, 2)$, the box word
$U^{a_1} D^k L D \, U^{a_2} D^k L$ equals $UUUDLDUUDL$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Lemma 2. -/
public theorem boxWord_one_three_two :
    boxWord 1 [3, 2] = [U, U, U, D, L, D, U, U, D, L] := by
  decide

/-- **$k$-Dyck words.** A word $w$ over the Booleans is a $k$-Dyck word when the number of
letters $\mathrm{true}$ in $w$ is $k$ times the number of letters $\mathrm{false}$, and every
prefix of $w$ contains at least $k$ times as many letters $\mathrm{true}$ as letters
$\mathrm{false}$.

Reading $\mathrm{true}$ as the step $U = (1,1)$ and $\mathrm{false}$ as the step
$D^{(k)} = (k,-k)$, this says that the path ends on the $x$-axis and never goes below it.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 2. -/
public def IsKDyckWord (k : ℕ) (w : List Bool) : Prop :=
  w.count true = k * w.count false ∧
    ∀ i ≤ w.length, k * (w.take i).count false ≤ (w.take i).count true

/-- Being a `k`-Dyck word is decidable.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 2. -/
public instance (k : ℕ) : DecidablePred (IsKDyckWord k) := fun w => by
  unfold IsKDyckWord
  infer_instance

/-- **$k$-Dyck paths of size $n$.** Write $U = (1,1)$ and $D^{(k)} = (k,-k)$. The $k$-Dyck paths
of size $n$ are the words of length $(k+1)n$ over $\{U, D^{(k)}\}$ with exactly $n$ steps
$D^{(k)}$ that have $k$ times as many $U$s as $D^{(k)}$s and in which every prefix has at least
$k$ times as many $U$s as $D^{(k)}$s.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 2. -/
public def kDyckWords (k n : ℕ) : Finset (List Bool) :=
  ((Finset.univ : Finset (Fin ((k + 1) * n) → Bool)).image List.ofFn).filter fun w =>
    IsKDyckWord k w ∧ w.count false = n

/-- **Three $2$-Dyck paths of size $2$.** The number of $2$-Dyck paths of size $2$ is $3$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 2. -/
public theorem card_kDyckWords_two_two : (kDyckWords 2 2).card = 3 := by
  decide +kernel

/-- **Augmentation of a $k$-Dyck word.** Let $k \ge 0$ and let $w$ be a word in the letters
$U = (1,1)$ and $D^{(k)} = (k,-k)$, for example a $k$-Dyck path. The augmented path of $w$ is the
word in the skew Dyck steps $U$, $D$, $L$ obtained from $w$ by keeping each letter $U$ and
replacing each letter $D^{(k)}$ by $U D^{k-1} L D$, where $D^{k-1}$ means $k - 1$ copies of $D$
(none when $k \le 1$).

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 2. -/
public def augmentKDyckWord (k : ℕ) (w : List Bool) : List SkewDyckStep :=
  w.flatMap fun b => if b then [U] else U :: List.replicate (k - 1) D ++ [L, D]

/-- **Augmented $k$-Dyck paths.** For natural numbers $k$ and $n$, write $U = (1,1)$ and
$D^{(k)} = (k,-k)$. A $k$-Dyck path of size $n$ is a word of length $(k+1)n$ in the letters $U$
and $D^{(k)}$ that has exactly $n$ letters $D^{(k)}$ and $k$ times as many letters $U$ as letters
$D^{(k)}$, and in which every prefix has at least $k$ times as many letters $U$ as letters
$D^{(k)}$. The augmented path of such a word is the word in the skew Dyck steps $U$, $D$, $L$
obtained by keeping each letter $U$ and replacing each letter $D^{(k)}$ by $U D^{k-1} L D$, where
$D^{k-1}$ means $k - 1$ copies of $D$ (none when $k \le 1$). The set $\hat{D}_n^{(k)}$ of
augmented $k$-Dyck paths of size $n$ is the set of the augmented paths of the $k$-Dyck paths of
size $n$.

The definition is used for $k \ge 2$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 2. -/
public def augmentedKDyckPaths (k n : ℕ) : Finset (List SkewDyckStep) :=
  (kDyckWords k n).image (augmentKDyckWord k)

/-- **Returns of a skew Dyck word.** Read a word $w$ over the skew Dyck steps $U = (1,1)$,
$D = (1,-1)$ and $L = (-1,-1)$ as a lattice path starting at the origin. The number of returns of
$w$ is the number of steps of $w$ that end on the $x$-axis, that is, the number of nonempty
prefixes of $w$ that contain as many $U$ steps as $D$ and $L$ steps together.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 3. -/
public def skewReturns (w : List SkewDyckStep) : ℕ :=
  ((List.range w.length).filter fun i =>
    decide ((w.take (i + 1)).count U = (w.take (i + 1)).count D + (w.take (i + 1)).count L)).length

/-- **Long ascents of a skew Dyck word.** A long ascent of a word $w$ over the skew Dyck steps
$U$, $D$, $L$ is a maximal run of consecutive $U$ steps of length at least $2$. The long ascent
count of $w$ is the number of long ascents of $w$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 7. -/
public def skewLongAscents (w : List SkewDyckStep) : ℕ :=
  ((List.range w.length).filter fun i =>
    decide (w[i]? = some U ∧ w[i + 1]? = some U ∧ (i = 0 ∨ w[i - 1]? ≠ some U))).length

/-- **Returns and long ascents of an example skew Dyck path.** The word $U D U^5 D L^2 D U D L$
over the skew Dyck steps has exactly two returns and exactly one long ascent.

This is the source's example of a skew Dyck path.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Figure 1. -/
public theorem skewReturns_skewLongAscents_example :
    skewReturns [U, D, U, U, U, U, U, D, L, L, D, U, D, L] = 2 ∧
      skewLongAscents [U, D, U, U, U, U, U, D, L, L, D, U, D, L] = 1 := by
  decide

/-- **Generating function of augmented $k$-Dyck paths.** Let $k \ge 0$ and let $\hat D_n^{(k)}$
be the set of augmented $k$-Dyck paths of size $n$. Then $G_k(x)$ is the formal power series with
integer coefficients
$$
G_k(x) = \sum_{n \ge 0} |\hat D_n^{(k)}| \, x^n \in \mathbb{Z}[[x]].
$$

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 6. -/
public noncomputable def augmentedKDyckGF (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => ((augmentedKDyckPaths k n).card : ℤ)

/-- **Generating function of $k$-box paths by returns.** For $k \in \mathbb{N}$, $F_k(t, x)$ is
the power series in $\mathbb{Z}[t][[x]]$ with constant term $0$ whose coefficient of $x^n$ for
$n \ge 1$ is the sum of $t^{\operatorname{ret}(\mu)}$ over the set $B_n^{(k)}$ of $k$-box paths
$\mu$ of size $n$, where $\operatorname{ret}(\mu)$ is the number of returns of $\mu$; that is,
$F_k(t, x) = \sum_{n \ge 1} \sum_{\mu \in B_n^{(k)}} t^{\operatorname{ret}(\mu)} x^n$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 6. -/
public noncomputable def kBoxReturnGF (k : ℕ) : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun n =>
    if n = 0 then 0 else ∑ w ∈ kBoxPaths k n, Polynomial.X ^ skewReturns w

/-- **Long-ascent generating function of $k$-box paths.** Let $B_n^{(k)}$ be the set of $k$-box
paths of size $n$, and let $\mathrm{la}(\mu)$ be the number of long ascents of a path $\mu$. The
long-ascent generating function of $k$-box paths is the power series
$$
\acute F_k(t, x) = \sum_{n \ge 1} \sum_{\mu \in B_n^{(k)}} t^{\mathrm{la}(\mu)} x^n
$$
in $\mathbb{Z}[t][[x]]$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 7. -/
public noncomputable def kBoxLongAscentGF (k : ℕ) : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun n =>
    if n = 0 then 0 else ∑ w ∈ kBoxPaths k n, Polynomial.X ^ skewLongAscents w

/-- **Long-ascent generating function of augmented $k$-Dyck paths.** Let $k \ge 0$, let
$\hat D_n^{(k)}$ be the set of augmented $k$-Dyck paths of size $n$, and for a path $\mu$ let
$\operatorname{asc}(\mu)$ be its number of long ascents. Then $\acute{G}_k(t, x)$ is the formal
power series
$$
\acute{G}_k(t, x) = \sum_{n \ge 0} \sum_{\mu \in \hat D_n^{(k)}} t^{\operatorname{asc}(\mu)} x^n
$$
in $\mathbb{Z}[t][[x]]$. Its constant term is $1$, coming from the empty path.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 7. -/
public noncomputable def augmentedKDyckLongAscentGF (k : ℕ) : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun n => ∑ w ∈ augmentedKDyckPaths k n, Polynomial.X ^ skewLongAscents w

/-- The variable `x` of the bivariate generating functions. -/
local notation "𝒙" => (PowerSeries.X : PowerSeries (Polynomial ℤ))
/-- The variable `t` of the bivariate generating functions, a constant in `ℤ[t]`. -/
local notation "𝒕" => PowerSeries.C (Polynomial.X : Polynomial ℤ)

/-- **Minimal semilength of skew Dyck paths with $n$ box factors.** Let $k \ge 1$ and $n \ge 1$.
Some skew Dyck path with exactly $n$ occurrences of the factor $U D^k L$ has semilength
(number of $U$ steps) $(k+2)n - 1$, and every skew Dyck path with exactly $n$ occurrences of
$U D^k L$ has semilength at least $(k+2)n - 1$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Proposition 1
(`jis-2024-24.2.4-prop-1`). -/
public theorem_wanted min_semilength_boxFactor {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    (∃ w, IsSkewDyckWord w ∧ skewFactorCount (boxFactor k) w = n ∧
      w.count U = (k + 2) * n - 1) ∧
    ∀ w, IsSkewDyckWord w → skewFactorCount (boxFactor k) w = n → (k + 2) * n - 1 ≤ w.count U

/-- **Structure of $k$-box paths.** Let $k \ge 1$ and $n \ge 1$. For a list
$a = (a_1, \dots, a_n)$ of natural numbers write
$w_k(a) = U^{a_1} D^k L D \cdots U^{a_{n-1}} D^k L D\, U^{a_n} D^k L$. Every $k$-box path of
size $n$ equals $w_k(a)$ for some list $a$ of $n$ positive integers. Conversely, if $a$ is a
list of $n$ positive integers with $a_1 + \cdots + a_n = (k+2)n - 1$ and no prefix of $w_k(a)$
has more $D$s and $L$s together than $U$s, then $w_k(a)$ is a $k$-box path of size $n$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Lemma 2
(`jis-2024-24.2.4-lem-2`). -/
public theorem_wanted kBoxPaths_structure {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    (∀ w ∈ kBoxPaths k n, ∃ a : List ℕ, a.length = n ∧ (∀ x ∈ a, 0 < x) ∧ w = boxWord k a) ∧
    ∀ a : List ℕ, a.length = n → (∀ x ∈ a, 0 < x) → a.sum = (k + 2) * n - 1 →
      (∀ i ≤ (boxWord k a).length, ((boxWord k a).take i).count D +
        ((boxWord k a).take i).count L ≤ ((boxWord k a).take i).count U) →
      boxWord k a ∈ kBoxPaths k n

/-- **Decomposition of $k$-box paths.** Let $k \ge 1$. A word $w$ in the steps $U$, $D$, $L$ is a
$k$-box path of some size $n \ge 1$ if and only if $w = \mu_1 U \mu_2 U \cdots \mu_{k+1} U D^k L$
for some augmented $(k+1)$-Dyck paths $\mu_1, \ldots, \mu_{k+1}$, each of some size.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Lemma 4
(`jis-2024-24.2.4-lem-4`). -/
public theorem_wanted kBoxPaths_decomposition {k : ℕ} (hk : 1 ≤ k) (w : List SkewDyckStep) :
    (∃ n, 1 ≤ n ∧ w ∈ kBoxPaths k n) ↔
      ∃ μ : Fin (k + 1) → List SkewDyckStep, (∀ i, ∃ m, μ i ∈ augmentedKDyckPaths (k + 1) m) ∧
        w = (List.ofFn fun i => μ i ++ [U]).flatten ++ List.replicate k D ++ [L]

/-- **Number of $k$-box paths of size $n$.** Let $k \ge 1$ and $n \ge 1$, and let $f_{k,n}$ be
the number of $k$-box paths of size $n$. Then
$$
((k+2)n - 1) \, f_{k,n} = \binom{(k+2)n - 1}{n},
$$
and if moreover $n \ge 2$, then
$$
(n - 1) \, f_{k,n} = (k+1) \binom{(k+2)n - 2}{n - 2}.
$$

The source also identifies $f_{k,n}$ with the number of $(k+1)$-tuples of $(k+2)$-ary trees
with $n - 1$ nodes; that identification is not part of this statement.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Theorem 5
(`jis-2024-24.2.4-thm-5`). -/
public theorem_wanted card_kBoxPaths {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    ((k + 2) * n - 1) * (kBoxPaths k n).card = ((k + 2) * n - 1).choose n ∧
      (2 ≤ n → (n - 1) * (kBoxPaths k n).card = (k + 1) * ((k + 2) * n - 2).choose (n - 2))

/-- **Counting tailed $k$-box paths.** Let $k \ge 1$ and $n \ge 1$, and let $T$ be the number of
$k$-box paths of size $n$ that end with $U^{k+1} D^k L$. Then
$((k+2)(n-1)+1) \cdot T = \binom{(k+2)(n-1)+1}{n-1}$, and if $n \ge 2$ then also
$(n-1) \cdot T = \binom{(k+2)(n-1)}{n-2}$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Proposition 7
(`jis-2024-24.2.4-prop-7`). -/
public theorem_wanted card_tailed_kBoxPaths {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    ((k + 2) * (n - 1) + 1) *
        ((kBoxPaths k n).filter fun w =>
          List.replicate (k + 1) U ++ List.replicate k D ++ [L] <:+ w).card =
      ((k + 2) * (n - 1) + 1).choose (n - 1) ∧
    (2 ≤ n → (n - 1) * ((kBoxPaths k n).filter fun w =>
          List.replicate (k + 1) U ++ List.replicate k D ++ [L] <:+ w).card =
      ((k + 2) * (n - 1)).choose (n - 2))

/-- **Functional equation for the returns generating function.** Let $k \ge 1$, let
$F_k(t, x) \in \mathbb{Z}[t][[x]]$ be the generating function of $k$-box paths of size at least
$1$ by number of returns (exponent of $t$) and size (exponent of $x$), and let $G_{k+1}(x)$ be
the generating function of augmented $(k+1)$-Dyck paths by size, viewed in $\mathbb{Z}[t][[x]]$.
Then
$$\bigl(1 - t x G_{k+1}^{k+1}\bigr) F_k = t x G_{k+1}^k.$$

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Lemma 8
(`jis-2024-24.2.4-lem-8`). -/
public theorem_wanted kBoxReturnGF_eq {k : ℕ} (hk : 1 ≤ k) :
    (1 - 𝒕 * 𝒙 * PowerSeries.map Polynomial.C (augmentedKDyckGF (k + 1)) ^ (k + 1)) *
        kBoxReturnGF k =
      𝒕 * 𝒙 * PowerSeries.map Polynomial.C (augmentedKDyckGF (k + 1)) ^ k

/-- **Number of $k$-box paths with $j$ returns.** Let $k \ge 1$ and $1 \le j \le n$, and let
$r_{k,n,j}$ be the number of $k$-box paths of size $n$ with exactly $j$ returns. Then
$$
((k+2)n - j - 1) \, r_{k,n,j} = (j(k+1) - 1) \binom{(k+2)n - j - 1}{n - j},
$$
and if moreover $j < n$, then
$$
(n - j) \, r_{k,n,j} = (j(k+1) - 1) \binom{(k+2)n - j - 2}{n - j - 1}.
$$

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Theorem 9
(`jis-2024-24.2.4-thm-9`). -/
public theorem_wanted card_kBoxPaths_returns {k n j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j)
    (hjn : j ≤ n) :
    ((k + 2) * n - j - 1) * ((kBoxPaths k n).filter fun w => skewReturns w = j).card =
        (j * (k + 1) - 1) * ((k + 2) * n - j - 1).choose (n - j) ∧
      (j < n → (n - j) * ((kBoxPaths k n).filter fun w => skewReturns w = j).card =
        (j * (k + 1) - 1) * ((k + 2) * n - j - 2).choose (n - j - 1))

/-- **Mean and variance of the number of returns of $k$-box paths.** Let $k \ge 1$ and $n \ge 1$,
and let $R(\mu)$ be the number of returns (steps ending on the $x$-axis) of a path $\mu$. The
average of $R$ over the $k$-box paths of size $n$ is
$$\frac{(k+2)((k+2)n-1)}{(k+1)((k+1)n+1)},$$
and the average of $R^2$ over these paths minus the square of the average of $R$ is
$$\frac{(k+2)((k+2)n-1)((2k+1)(k+1)n-2)(n-1)}{(k+1)^2((k+1)n+1)^2((k+1)n+2)}.$$

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Corollary 11
(`jis-2024-24.2.4-cor-11`). -/
public theorem_wanted kBoxPaths_returns_mean_variance {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    (∑ w ∈ kBoxPaths k n, (skewReturns w : ℚ)) / (kBoxPaths k n).card =
        ((k + 2) * ((k + 2) * n - 1) : ℚ) / ((k + 1) * ((k + 1) * n + 1)) ∧
      (∑ w ∈ kBoxPaths k n, (skewReturns w : ℚ) ^ 2) / (kBoxPaths k n).card -
          ((∑ w ∈ kBoxPaths k n, (skewReturns w : ℚ)) / (kBoxPaths k n).card) ^ 2 =
        ((k + 2) * ((k + 2) * n - 1) * ((2 * k + 1) * (k + 1) * n - 2) * (n - 1) : ℚ) /
          ((k + 1) ^ 2 * ((k + 1) * n + 1) ^ 2 * ((k + 1) * n + 2))

/-- **Long-ascent functional equations for $k$-box paths.** Let $\acute F_k(t, x)$ be the
long-ascent generating function of $k$-box paths and $\acute G_k(t, x)$ that of augmented
$k$-Dyck paths, including the empty path, both in $\mathbb{Z}[t][[x]]$. Then for every $k \ge 1$
$$
\acute F_k = x \, \acute G_{k+1}^{k} \, (\acute G_{k+1} - 1 + t),
$$
and for every $k \ge 2$
$$
\acute G_k = 1 + x \, \acute G_k^{k} \, (\acute G_k - 1 + t).
$$

The source's displayed sum for $\acute G_k$ omits the empty path; here $\acute G_k$ includes it
(constant term $1$), as both equations require.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Lemma 12
(`jis-2024-24.2.4-lem-12`). -/
public theorem_wanted kBoxLongAscentGF_functional_equations :
    (∀ k : ℕ, 1 ≤ k → kBoxLongAscentGF k =
      𝒙 * augmentedKDyckLongAscentGF (k + 1) ^ k *
        (augmentedKDyckLongAscentGF (k + 1) - 1 + 𝒕)) ∧
    ∀ k : ℕ, 2 ≤ k → augmentedKDyckLongAscentGF k =
      1 + 𝒙 * augmentedKDyckLongAscentGF k ^ k * (augmentedKDyckLongAscentGF k - 1 + 𝒕)

/-- **Number of $k$-box paths with $j$ long ascents.** Let $k \ge 1$, $n \ge 1$ and $j \ge 1$,
and let $a_{k,n,j}$ be the number of $k$-box paths of size $n$ with exactly $j$ long ascents.
Then
$$
j \, a_{k,n,j} = \binom{(k+1)n - 2}{j - 1} \binom{n - 1}{j - 1}.
$$
For $j > n$ both sides vanish.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Theorem 13
(`jis-2024-24.2.4-thm-13`). -/
public theorem_wanted card_kBoxPaths_longAscents {k n j : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hj : 1 ≤ j) :
    j * ((kBoxPaths k n).filter fun w => skewLongAscents w = j).card =
      ((k + 1) * n - 2).choose (j - 1) * (n - 1).choose (j - 1)

/-- **Second polygonal numbers count box paths with two long ascents.** Let $K \ge 4$ and
$n \ge 1$. Then $n\bigl((K-2)n + (K-4)\bigr)$ is twice the number of $(K-3)$-box paths of size
$n + 1$ with exactly two long ascents (maximal runs of at least two $U$ steps). Equivalently,
the $n$th second $K$-gonal number $n\bigl((K-2)n + (K-4)\bigr)/2$, the $K$-gonal formula
$m\bigl((K-2)m - (K-4)\bigr)/2$ at $m = -n$, equals this number of paths.

The source states this for $K \ge 3$, where the case $K = 3$ uses its convention for $0$-box
paths.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Theorem 15
(`jis-2024-24.2.4-thm-15`). -/
public theorem_wanted second_polygonal_eq_card_kBoxPaths_two_longAscents {K n : ℕ}
    (hK : 4 ≤ K) (hn : 1 ≤ n) :
    n * ((K - 2) * n + (K - 4)) =
      2 * ((kBoxPaths (K - 3) (n + 1)).filter fun w => skewLongAscents w = 2).card

/-- **Long ascents of box paths: sum and sum of squares.** Let $k \ge 1$ and $n \ge 1$, let
$B_n^{(k)}$ be the set of $k$-box paths of size $n$, and for a path $w$ let $\mathrm{la}(w)$ be
its number of long ascents. Then
$$\sum_{w \in B_n^{(k)}} \mathrm{la}(w) = \binom{(k+2)n-3}{n-1}$$
and
$$\bigl((k+2)n-3\bigr) \sum_{w \in B_n^{(k)}} \mathrm{la}(w)^2 =
\bigl((k+1)n^2-n-1\bigr) \binom{(k+2)n-3}{n-1}.$$

The source states the second identity divided by $(k+2)n-3$, that is, with the sum of
$\mathrm{la}(w)^2$ equal to $\frac{(k+1)n^2-n-1}{(k+2)n-3}\binom{(k+2)n-3}{n-1}$; at $k = n = 1$
the cleared form reads $0 = 0$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Lemma 17
(`jis-2024-24.2.4-lem-17`). -/
public theorem_wanted sum_kBoxPaths_longAscents {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    ∑ w ∈ kBoxPaths k n, skewLongAscents w = ((k + 2) * n - 3).choose (n - 1) ∧
      ((k + 2) * n - 3) * ∑ w ∈ kBoxPaths k n, skewLongAscents w ^ 2 =
        ((k + 1) * n ^ 2 - n - 1) * ((k + 2) * n - 3).choose (n - 1)

/-- **Mean and variance of long ascents in $k$-box paths.** Let $k \ge 1$ and $n \ge 1$. Over the
$k$-box paths of size $n$, taken with equal weight, the mean number of long ascents is
$$
\frac{n((k+1)n-1)}{(k+2)n-2}
$$
and the variance (the mean of the square minus the square of the mean) is
$$
\frac{((k+1)n-1)((k+1)n-2)\,n(n-1)}{((k+2)n-2)^2\,((k+2)n-3)}.
$$

When $k = n = 1$ the variance is $0$, and the last fraction reads $0/0$, which is taken to be $0$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Proposition 18
(`jis-2024-24.2.4-prop-18`). -/
public theorem_wanted kBoxPaths_longAscents_mean_variance {k n : ℕ} (hk : 1 ≤ k)
    (hn : 1 ≤ n) :
    (∑ w ∈ kBoxPaths k n, (skewLongAscents w : ℚ)) / (kBoxPaths k n).card =
        (n * ((k + 1) * n - 1) : ℚ) / ((k + 2) * n - 2) ∧
      (∑ w ∈ kBoxPaths k n, (skewLongAscents w : ℚ) ^ 2) / (kBoxPaths k n).card -
          ((∑ w ∈ kBoxPaths k n, (skewLongAscents w : ℚ)) / (kBoxPaths k n).card) ^ 2 =
        (((k + 1) * n - 1) * ((k + 1) * n - 2) * n * (n - 1) : ℚ) /
          (((k + 2) * n - 2) ^ 2 * ((k + 2) * n - 3))

end

end MetaMathlibExt
