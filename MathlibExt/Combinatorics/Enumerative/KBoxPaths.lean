/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.List.Infix
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
The theorem `min_semilength_boxFactor` gives the sharp lower bound for paths with `n` box factors.
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

namespace min_semilength_boxFactor

private theorem factorCount_cons (k : ℕ) (a : SkewDyckStep) (w : List SkewDyckStep) :
    skewFactorCount (boxFactor k) (a :: w) = skewFactorCount (boxFactor k) w +
      if boxFactor k <+: a :: w then 1 else 0 := by
  simp [skewFactorCount, List.countP_cons, List.isPrefixOf_iff_prefix]

private theorem factorCount_cons_of_ne (k : ℕ) {a : SkewDyckStep} (ha : a ≠ U)
    (w : List SkewDyckStep) :
    skewFactorCount (boxFactor k) (a :: w) = skewFactorCount (boxFactor k) w := by
  rw [factorCount_cons]
  simp [boxFactor, List.cons_prefix_cons, Ne.symm ha]

private theorem factorCount_replicate_down (k j : ℕ) (w : List SkewDyckStep) :
    skewFactorCount (boxFactor k) (List.replicate j D ++ w) =
      skewFactorCount (boxFactor k) w := by
  induction j with
  | zero => simp
  | succ j ih => simpa [List.replicate_succ, factorCount_cons_of_ne k (by decide : D ≠ U)]

private theorem factorCount_box_append (k : ℕ) (w : List SkewDyckStep) :
    skewFactorCount (boxFactor k) (boxFactor k ++ w) = skewFactorCount (boxFactor k) w + 1 := by
  rw [show boxFactor k ++ w = U :: ((List.replicate k D ++ [L]) ++ w) by rfl,
    factorCount_cons, ite_eq_left (by exact List.prefix_append (boxFactor k) w), List.append_assoc]
  simp [factorCount_replicate_down, factorCount_cons_of_ne k (by decide : L ≠ U)]

/-- Each box uses `k + 1` descending steps. Its next step, if present, also descends. -/
private theorem descending_bound (k : ℕ) (w : List SkewDyckStep) (h : ¬ [L, U] <:+: w) :
    (k + 2) * skewFactorCount (boxFactor k) w ≤ w.count D + w.count L + 1 := by
  cases w with
  | nil => simp [skewFactorCount, boxFactor]
  | cons a t =>
    by_cases hp : boxFactor k <+: a :: t
    · obtain ⟨r, hr⟩ := hp
      rw [← hr] at h ⊢
      rw [factorCount_box_append, Nat.mul_add, Nat.mul_one]
      cases r with
      | nil => simp [skewFactorCount, boxFactor, List.count_replicate]
      | cons b s =>
        have hb : b ≠ U := by
          rintro rfl
          exact h ⟨U :: List.replicate k D, s, by simp [boxFactor]⟩
        have hs : ¬ [L, U] <:+: s := fun hi =>
          h (hi.trans ((List.suffix_cons b s).trans (List.suffix_append _ _)).isInfix)
        have ih := descending_bound k s hs
        rw [factorCount_cons_of_ne k hb]
        cases b with
        | U => contradiction
        | D | L =>
          simp [boxFactor, List.count_replicate] at ih ⊢
          omega
    · have ih := descending_bound k t fun hi => h (List.infix_cons_iff.mpr (.inr hi))
      simp only [factorCount_cons k a t, hp, ↓reduceIte, Nat.add_zero]
      exact ih.trans (Nat.add_le_add_right
        (Nat.add_le_add List.count_le_count_cons List.count_le_count_cons) 1)
termination_by w.length
decreasing_by
  · rw [‹w = a :: t›, ← hr]
    simp only [List.length_append, List.length_cons]
    omega
  · rw [‹w = a :: t›]
    simp

private def Avoids (w : List SkewDyckStep) : Prop :=
  ¬ [U, L] <:+: w ∧ ¬ [L, U] <:+: w

private theorem avoids_cons {a : SkewDyckStep} {w : List SkewDyckStep}
    (hw : Avoids w) (hul : ¬ [U, L] <+: a :: w) (hlu : ¬ [L, U] <+: a :: w) :
    Avoids (a :: w) := by
  simpa [Avoids, List.infix_cons_iff, hul, hlu] using hw

private theorem avoids_run {a : SkewDyckStep} {w : List SkewDyckStep}
    (n : ℕ) (hw : Avoids (a :: w)) : Avoids (List.replicate (n + 1) a ++ w) := by
  induction n with
  | zero => simpa using hw
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append]
    apply avoids_cons ih <;> cases a <;> simp [List.replicate_succ, List.cons_prefix_cons]

private theorem descending_le_length (w : List SkewDyckStep) :
    w.count D + w.count L ≤ w.length := by
  induction w with
  | nil => simp
  | cons a w ih => cases a <;> simp <;> omega

/-- Prepending equal runs of up and descending steps preserves the prefix height bound. -/
private theorem mountain_append (d w : List SkewDyckStep) (hu : d.count U = 0)
    (hd : d.count D + d.count L = d.length) (hw : IsSkewDyckWord w)
    (ha : Avoids (List.replicate d.length U ++ (d ++ w))) :
    IsSkewDyckWord (List.replicate d.length U ++ (d ++ w)) := by
  obtain ⟨_, _, hbal, hpref⟩ := hw
  refine ⟨ha.1, ha.2, ?_, fun i hi => ?_⟩
  · simp [List.count_replicate, hu]
    omega
  · by_cases h₁ : i ≤ d.length
    · rw [List.take_append_of_le_length (by simpa using h₁)]
      simp [List.take_replicate, List.count_replicate]
    · simp only [List.take_append, List.length_replicate, List.take_replicate,
        Nat.min_eq_right (by omega : d.length ≤ i), List.count_append]
      by_cases h₂ : i - d.length ≤ d.length
      · have bound := descending_le_length (d.take (i - d.length))
        simp [Nat.sub_eq_zero_of_le h₂, List.count_replicate] at *
        omega
      · have bound := hpref (i - d.length - d.length) (by simp at hi; omega)
        simp [List.take_of_length_le (by omega : d.length ≤ i - d.length),
          List.count_replicate, hu]
        omega

/-- Multiple consecutive up steps give just one possible start for the box. -/
private theorem factorCount_peak (k j : ℕ) (hk : 1 ≤ k) (r : List SkewDyckStep) :
    skewFactorCount (boxFactor k) (List.replicate (j + 1) U ++ (List.replicate k D ++ L :: r)) =
      skewFactorCount (boxFactor k) r + 1 := by
  induction j with
  | zero => simpa [boxFactor, List.append_assoc] using factorCount_box_append k r
  | succ j ih =>
    rw [List.replicate_succ, List.cons_append, factorCount_cons]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hn : ¬ boxFactor (k + 1) <+:
        U :: (List.replicate (j + 1) U ++ (List.replicate (k + 1) D ++ L :: r)) := by
      simp [boxFactor, List.replicate_succ, List.cons_prefix_cons]
    simpa only [hn, ↓reduceIte, Nat.add_zero] using ih

/-- Prepend a balanced peak with one box. Its optional final down step separates it
from the next peak. -/
private theorem prepend_peak {k : ℕ} (hk : 1 ≤ k) (sep : Bool) (w : List SkewDyckStep)
    (hw : IsSkewDyckWord w) (hlast : sep = false → w = []) :
    ∃ v, IsSkewDyckWord v ∧ skewFactorCount (boxFactor k) v = skewFactorCount (boxFactor k) w + 1 ∧
      v.count U = w.count U + (k + 1 + sep.toNat) := by
  let tail := if sep then [D] else []
  let d := List.replicate k D ++ L :: tail
  have hlen : d.length = k + 1 + sep.toNat := by cases sep <;> simp [d, tail]
  refine ⟨List.replicate d.length U ++ (d ++ w), ?_, ?_, ?_⟩
  · refine mountain_append d w ?_ ?_ hw ?_
    · cases sep <;> simp [d, tail, List.count_replicate]
    · cases sep <;> simp [d, tail, List.count_replicate]
    · have htail : Avoids (L :: (tail ++ w)) := by
        cases sep with
        | false => simp [hlast rfl, Avoids, tail, List.infix_cons_iff, List.cons_prefix_cons]
        | true =>
          have hw' : Avoids w := ⟨hw.1, hw.2.1⟩
          have hD : Avoids (D :: w) := by
            apply avoids_cons hw' <;> simp [List.cons_prefix_cons]
          apply avoids_cons hD <;> simp [List.cons_prefix_cons]
      have hD : Avoids (D :: L :: (tail ++ w)) := by
        apply avoids_cons htail <;> simp [List.cons_prefix_cons]
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hrun := avoids_run j hD
      rw [show d.length = (j + 1 + sep.toNat) + 1 by omega]
      apply avoids_run
      simp only [d, List.append_assoc, List.cons_append]
      apply avoids_cons hrun <;> simp [List.replicate_succ, List.cons_prefix_cons]
  · rw [show d.length = (k + sep.toNat) + 1 by omega]
    simp only [d, List.append_assoc, List.cons_append]
    rw [factorCount_peak k _ hk]
    cases sep <;> simp [tail, factorCount_cons_of_ne k (by decide : D ≠ U)]
  · cases sep <;> simp [d, tail, List.count_replicate] <;> omega

private theorem exists_minimizer (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    ∃ w, IsSkewDyckWord w ∧ skewFactorCount (boxFactor k) w = m + 1 ∧
      w.count U = (k + 2) * (m + 1) - 1 := by
  induction m with
  | zero =>
    obtain ⟨v, hv, hc, hu⟩ := prepend_peak hk false [] (by simp [IsSkewDyckWord]) (by simp)
    exact ⟨v, hv, by simpa [skewFactorCount, boxFactor] using hc, by simpa using hu⟩
  | succ m ih =>
    obtain ⟨w, hw, hc, hu⟩ := ih
    obtain ⟨v, hv, hc', hu'⟩ := prepend_peak hk true w hw (by simp)
    refine ⟨v, hv, by omega, ?_⟩
    simp only [Bool.toNat_true] at hu'
    rw [Nat.mul_succ]
    have := Nat.mul_pos (by omega : 0 < k + 2) (by omega : 0 < m + 1)
    omega

end min_semilength_boxFactor

/-- **Minimal semilength of skew Dyck paths with $n$ box factors.** Let $k \ge 1$ and $n \ge 1$.
Some skew Dyck path with exactly $n$ occurrences of the factor $U D^k L$ has semilength
(number of $U$ steps) $(k+2)n - 1$, and every skew Dyck path with exactly $n$ occurrences of
$U D^k L$ has semilength at least $(k+2)n - 1$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Proposition 1
(`jis-2024-24.2.4-prop-1`). -/
public theorem min_semilength_boxFactor {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    (∃ w, IsSkewDyckWord w ∧ skewFactorCount (boxFactor k) w = n ∧
      w.count U = (k + 2) * n - 1) ∧
    ∀ w, IsSkewDyckWord w → skewFactorCount (boxFactor k) w = n → (k + 2) * n - 1 ≤ w.count U := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  refine ⟨min_semilength_boxFactor.exists_minimizer k hk m, fun w hw hc => ?_⟩
  have h := min_semilength_boxFactor.descending_bound k w hw.2.1
  rw [hc, ← hw.2.2.1] at h
  omega

end

end MetaMathlibExt
