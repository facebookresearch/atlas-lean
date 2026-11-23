/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Young.SemistandardTableau
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Multiset.Powerset
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.Enumerative.ParkingFunction
public import MathlibExt.Combinatorics.FineNumber

/-!
# Discrete statistics of parking functions: wishlist

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6 (arXiv:2312.16786).

Parking functions are `MetaMathlibExt.IsParkingFunction n f` with `f : Fin n → Fin n`;
the value `f i` stands for the paper's preference `a_{i+1} = f i + 1`. Positions in
descent and ascent sets are the paper's 1-based indices `i ∈ [n-1]`. A descent at `i`
means `a_i > a_{i+1}`, an ascent `a_i < a_{i+1}`, a tie `a_i = a_{i+1}`, a peak
`a_{i-1} < a_i > a_{i+1}`, a valley `a_{i-1} > a_i < a_{i+1}`. A word over the multiset
`M(β)` of entries of `β` is an `f` with the same multiset of values. The statistic
encoding uses `Ordering`: `A = .lt`, `D = .gt`, `T = .eq`. These are written inline via
local notation; the new definitions are the bijection `peaklessTielessOfNondecreasing`
(the paper's `φ`) and the rearrangement `ascentToDescentRearrangement` (the paper's `ν`,
computed by the fuelled recursion `ascentToDescentRearrangementAux`).
-/

namespace MetaMathlibExt

@[expose] public section

open Classical

set_option quotPrecheck false in
/-- The parking functions of length `n`. -/
local notation "pfSet" n:max =>
  Finset.filter (fun f : Fin n → Fin n => IsParkingFunction n f) Finset.univ

set_option quotPrecheck false in
/-- The nondecreasing parking functions of length `n`. -/
local notation "ndpfSet" n:max =>
  Finset.filter (fun f : Fin n → Fin n => IsParkingFunction n f ∧ Monotone f) Finset.univ

set_option quotPrecheck false in
/-- Descent set (1-based positions) of a word `w : Fin m → Fin n`. -/
local notation "desSet" w:max =>
  Finset.image (fun i => i.val + 1)
    (Finset.filter (fun i => ∃ j, j.val = i.val + 1 ∧ w j < w i) Finset.univ)

set_option quotPrecheck false in
/-- Ascent set (1-based positions) of a word `w : Fin m → Fin n`. -/
local notation "ascSet" w:max =>
  Finset.image (fun i => i.val + 1)
    (Finset.filter (fun i => ∃ j, j.val = i.val + 1 ∧ w i < w j) Finset.univ)

set_option quotPrecheck false in
/-- `w` has no ties. -/
local notation "NoTies" w:max => ∀ i j, j.val = i.val + 1 → w i ≠ w j

set_option quotPrecheck false in
/-- `w` has no peaks. -/
local notation "NoPeaks" w:max =>
  ∀ i j k, j.val = i.val + 1 → k.val = j.val + 1 → ¬ (w i < w j ∧ w k < w j)

set_option quotPrecheck false in
/-- `w` has no valleys. -/
local notation "NoValleys" w:max =>
  ∀ i j k, j.val = i.val + 1 → k.val = j.val + 1 → ¬ (w j < w i ∧ w j < w k)

set_option quotPrecheck false in
/-- The peakless-tieless parking functions `PTPF_n`. -/
local notation "ptpfSet" n:max =>
  Finset.filter (fun f : Fin n → Fin n => IsParkingFunction n f ∧ (NoTies f) ∧ NoPeaks f)
    Finset.univ

set_option quotPrecheck false in
/-- The valleyless-tieless parking functions `VTPF_n`. -/
local notation "vtpfSet" n:max =>
  Finset.filter (fun f : Fin n → Fin n => IsParkingFunction n f ∧ (NoTies f) ∧ NoValleys f)
    Finset.univ

set_option quotPrecheck false in
/-- Statistic encoding of `f : Fin n → Fin n`: `compare a_i a_{i+1}` for `i ∈ [n-1]`. -/
local notation "statEnc" n:max f:max => fun i : Fin (n - 1) =>
  compare (f ⟨i.val, by have := i.isLt; omega⟩) (f ⟨i.val + 1, by have := i.isLt; omega⟩)

set_option quotPrecheck false in
/-- `w` has the form `A*T*`. -/
local notation "IsAstarTstar" w:max =>
  ∃ k : ℕ, ∀ i, (i.val < k → w i = Ordering.lt) ∧ (k ≤ i.val → w i = Ordering.eq)

set_option quotPrecheck false in
/-- `w` has the form `T*D*`. -/
local notation "IsTstarDstar" w:max =>
  ∃ k : ℕ, ∀ i, (i.val < k → w i = Ordering.eq) ∧ (k ≤ i.val → w i = Ordering.gt)

/-- **Descent generating function of parking functions.** Write a sequence of length $n$ as
$(a_1, \dots, a_n)$; its descents are the $j \in \{1, \dots, n-1\}$ with $a_j > a_{j+1}$, and
$\operatorname{des}$ is their number. A parking function $f$ of length $n$ is read as the sequence
$a_j = f(j-1) + 1$. Let $PF_n$ be the set of parking functions of length $n$, $PF^{\uparrow}_n$
the set of nondecreasing ones, and $d(n, j)$ the number of $\alpha \in PF_n$ with
$\operatorname{des}(\alpha) = j$. For every $n \ge 1$, in the polynomial ring $\mathbb{N}[y]$,

$$\sum_{\alpha \in PF_n} y^{\operatorname{des}(\alpha)} = \sum_{j=0}^{n-1} d(n, j)\, y^j =
\sum_{\beta \in PF^{\uparrow}_n} \sum_{\pi} y^{\operatorname{des}(\pi)},$$

where, for each $\beta$, $\pi$ runs over the rearrangements of $\beta$: the sequences of length
$n$ with the same multiset of entries as $\beta$.

The paper prints the middle sum from $j = 1$; it is read from $j = 0$ (at $n = 1$ the printed
middle sum is $0$ while the other two sides are $1$). At $n = 0$ the left side is $1$ and the
middle sum is empty, so $n \ge 1$ is assumed, as in the paper.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorems 1 and 2
(`jis-2024-24.8.6-thm-1`, `jis-2024-24.8.6-thm-2`). -/
public theorem_wanted parkingFunction_descent_genFun (n : ℕ) (hn : 1 ≤ n) :
    ∑ f ∈ pfSet n, (Polynomial.X : Polynomial ℕ) ^ (desSet f).card =
      ∑ j ∈ Finset.range n,
        Polynomial.C ((pfSet n).filter (fun f => (desSet f).card = j)).card *
          Polynomial.X ^ j ∧
    ∑ j ∈ Finset.range n,
        Polynomial.C ((pfSet n).filter (fun f => (desSet f).card = j)).card *
          Polynomial.X ^ j =
      ∑ β ∈ ndpfSet n, ∑ w ∈ Finset.univ.filter
        (fun w : Fin n → Fin n => Finset.univ.val.map w = Finset.univ.val.map β),
          (Polynomial.X : Polynomial ℕ) ^ (desSet w).card

/-- **Descent sets versus reflected ascent sets of parking functions.** Write a parking function
$f$ of length $n$ as the sequence $(a_1, \dots, a_n)$ with $a_j = f(j-1) + 1$. Its descent set is
the set of $j \in \{1, \dots, n-1\}$ with $a_j > a_{j+1}$, and its ascent set the set of such $j$
with $a_j < a_{j+1}$. For every $n$ and every $I \subseteq \{1, \dots, n-1\}$, let
$J = \{n - i : i \in I\}$. Then the number of parking functions of length $n$ with descent set
$I$ equals the number of parking functions of length $n$ with ascent set $J$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Proposition 6
(`jis-2024-24.8.6-prop-6`). -/
public theorem_wanted parkingFunction_descentSet_card_eq_ascentSet_reflect (n : ℕ)
    (I : Finset ℕ) (hI : I ⊆ Finset.Ico 1 n) :
    ((pfSet n).filter (fun f => desSet f = I)).card =
      ((pfSet n).filter (fun f => ascSet f = I.image (fun i => n - i))).card

/-- **Descent sets and ascent sets of parking functions are equidistributed.** Write a parking
function $f$ of length $n$ as the sequence $(a_1, \dots, a_n)$ with $a_j = f(j-1) + 1$. Its
descent set is the set of $j \in \{1, \dots, n-1\}$ with $a_j > a_{j+1}$, and its ascent set the
set of such $j$ with $a_j < a_{j+1}$. For every $n$ and every $I \subseteq \{1, \dots, n-1\}$, the
number of parking functions of length $n$ with descent set $I$ equals the number of parking
functions of length $n$ with ascent set $I$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Corollary 15
(`jis-2024-24.8.6-cor-15`). -/
public theorem_wanted parkingFunction_descentSet_card_eq_ascentSet (n : ℕ) (I : Finset ℕ)
    (hI : I ⊆ Finset.Ico 1 n) :
    ((pfSet n).filter (fun f => desSet f = I)).card =
      ((pfSet n).filter (fun f => ascSet f = I)).card

/-- **Reflection symmetry of descent sets of parking functions.** Write a parking function $f$ of
length $n$ as the sequence $(a_1, \dots, a_n)$ with $a_j = f(j-1) + 1$. Its descent set is the set
of $j \in \{1, \dots, n-1\}$ with $a_j > a_{j+1}$. For every $n$ and every
$I \subseteq \{1, \dots, n-1\}$, let $J = \{n - i : i \in I\}$. Then the number of parking
functions of length $n$ with descent set $I$ equals the number with descent set $J$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorem 16
(`jis-2024-24.8.6-thm-16`). -/
public theorem_wanted parkingFunction_descentSet_card_reflect (n : ℕ) (I : Finset ℕ)
    (hI : I ⊆ Finset.Ico 1 n) :
    ((pfSet n).filter (fun f => desSet f = I)).card =
      ((pfSet n).filter (fun f => desSet f = I.image (fun i => n - i))).card

/-- **Counting parking functions with a given descent set by their content.** The descent set
of a word $w = (w_1, \dots, w_n)$ is $\{i : 1 \le i \le n - 1,\ w_i > w_{i+1}\}$. Let
$n \in \mathbb{N}$ and $I \subseteq \{1, \dots, n - 1\}$. Then the number of parking functions of
length $n$ with descent set $I$ equals the sum, over the nondecreasing parking functions $\beta$
of length $n$, of the number of words of length $n$ with descent set $I$ whose multiset of
letters is the multiset of entries of $\beta$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 17
(`jis-2024-24.8.6-lem-17`). -/
public theorem_wanted sum_ndpf_multisetDescent_eq (n : ℕ) (I : Finset ℕ)
    (hI : I ⊆ Finset.Ico 1 n) :
    ∑ β ∈ ndpfSet n, (Finset.univ.filter (fun w : Fin n → Fin n =>
        Finset.univ.val.map w = Finset.univ.val.map β ∧ desSet w = I)).card =
      ((pfSet n).filter (fun f => desSet f = I)).card

/-- **Recursion for parking functions with a given descent set.** The descent set of a word
$w = (w_1, \dots, w_\ell)$ is $\{i : 1 \le i \le \ell - 1,\ w_i > w_{i+1}\}$, and $d(J; n)$ denotes
the number of parking functions of length $n$ with descent set $J$. Let $n \in \mathbb{N}$, let
$I \subseteq \{1, \dots, n - 1\}$ be nonempty with largest element $m$, and let
$I^- = I \setminus \{m\}$. Then
$$d(I; n) = \sum_{\beta} \sum_{X} d_X(I^-) - d(I^-; n),$$
where $\beta$ runs over the nondecreasing parking functions of length $n$, $X$ runs over the
distinct sub-multisets of size $m$ of the multiset of entries of $\beta$, and $d_X(I^-)$ is the
number of words of length $m$ whose multiset of letters is $X$ and whose descent set is $I^-$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorem 18
(`jis-2024-24.8.6-thm-18`). -/
public theorem_wanted parkingFunction_descentSet_recursion (n : ℕ) (I : Finset ℕ)
    (hI : I ⊆ Finset.Ico 1 n) (hne : I.Nonempty) :
    (((pfSet n).filter (fun f => desSet f = I)).card : ℤ) =
      ∑ β ∈ ndpfSet n, ∑ X ∈ ((Finset.univ.val.map β).powersetCard (I.max' hne)).toFinset,
        ((Finset.univ.filter (fun w : Fin (I.max' hne) → Fin n =>
          Finset.univ.val.map w = X ∧ desSet w = I.erase (I.max' hne))).card : ℤ) -
      ((pfSet n).filter (fun f => desSet f = I.erase (I.max' hne))).card

/-- **Parking functions with descent set $\{1, \dots, k\}$.** Let $n \ge 1$ and
$0 \le k \le n - 1$. The number of parking functions $(a_1, \dots, a_n)$ of length $n$ whose descent
set $\{i : 1 \le i \le n - 1,\ a_i > a_{i+1}\}$ is exactly $\{1, \dots, k\}$ (empty when $k = 0$)
equals $\frac{1}{n}\binom{n}{k}\binom{2n-k}{n-k-1}$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Proposition 24
(`jis-2024-24.8.6-prop-24`). -/
public theorem_wanted parkingFunction_descentSet_initial_card (n k : ℕ) (hn : 1 ≤ n)
    (hk : k ≤ n - 1) :
    ((((pfSet n).filter (fun f => desSet f = Finset.Icc 1 k)).card : ℕ) : ℚ) =
      1 / n * (n.choose k : ℚ) * ((2 * n - k).choose (n - k - 1) : ℚ)

/-- **Peakless-tieless parking functions are counted by the Catalan numbers.** Write a parking
function $f$ of length $n$ as the sequence $(a_1, \dots, a_n)$ with $a_j = f(j-1) + 1$. It is
peakless-tieless if there is no $j$ with $a_{j-1} < a_j > a_{j+1}$ (a peak) and no $j$ with
$a_j = a_{j+1}$ (a tie). For every $n \ge 1$, the number of peakless-tieless parking functions of
length $n$ is the Catalan number $C_n$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Corollary 31
(`jis-2024-24.8.6-cor-31`). -/
public theorem_wanted card_peakless_tieless_parkingFunction (n : ℕ) (hn : 1 ≤ n) :
    (ptpfSet n).card = catalan n

/-- **Peakless-tieless parking functions by last entry.** Write a parking function $f$ of length
$n$ as the sequence $(a_1, \dots, a_n)$ with $a_j = f(j-1) + 1 \in \{1, \dots, n\}$. It is
peakless-tieless if there is no $j$ with $a_{j-1} < a_j > a_{j+1}$ (a peak) and no $j$ with
$a_j = a_{j+1}$ (a tie). For natural numbers $i$ and $n$ with $1 \le i \le n$, the number of
peakless-tieless parking functions of length $n$ with last entry $a_n = i$ is
$$\binom{n+i-2}{i-1} \cdot \frac{n-i+1}{n}.$$

This is the Catalan-triangle entry $T(n-1, i-1)$ of OEIS A009766.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Corollary 32
(`jis-2024-24.8.6-cor-32`). -/
public theorem_wanted card_peakless_tieless_parkingFunction_last (n i : ℕ) (hi : 1 ≤ i)
    (hin : i ≤ n) :
    ((((ptpfSet n).filter (fun f => ∀ j : Fin n, j.val + 1 = n → (f j : ℕ) + 1 = i)).card :
      ℕ) : ℚ) = ((n + i - 2).choose (i - 1) : ℚ) * ((n - i + 1 : ℕ) : ℚ) / n

/-- **Valleyless-tieless parking functions are counted by the Fine numbers.** Write a parking
function $f$ of length $n$ as the sequence $(a_1, \dots, a_n)$ with $a_j = f(j-1) + 1$. It is
valleyless-tieless if there is no $j$ with $a_{j-1} > a_j < a_{j+1}$ (a valley) and no $j$ with
$a_j = a_{j+1}$ (a tie). For every $n \ge 1$, the number of valleyless-tieless parking functions
of length $n$ is the Fine number $F(n+1)$, where the Fine numbers are indexed from $0$ with
$F(0) = 1$; for $n = 1, \dots, 5$ these counts are $1, 2, 6, 18, 57$.

In the offset-0 indexing of OEIS A000957 ($0, 1, 0, 1, 2, 6, 18, \dots$), $F(n+1)$ is the term
of index $n + 2$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorem 33
(`jis-2024-24.8.6-thm-33`). -/
public theorem_wanted card_valleyless_tieless_parkingFunction (n : ℕ) (hn : 1 ≤ n) :
    (((vtpfSet n).card : ℕ) : ℚ) = fineNumber (n + 1)

/-- **Prepending $1$ to valleyless-tieless parking functions.** Identify a parking function $f$
of length $m$ with the word $(f(0) + 1, \dots, f(m-1) + 1)$. A word $(a_1, \dots, a_m)$ has a
tie if $a_k = a_{k+1}$ for some $k$, and a valley if $a_{k-1} > a_k < a_{k+1}$ for some $k$;
write $\mathrm{VTPF}_m$ for the set of parking functions of length $m$ with no ties and no
valleys. For $n \ge 1$, the map $(a_1, \dots, a_n) \mapsto (1, a_1 + 1, \dots, a_n + 1)$ is a
bijection from $\mathrm{VTPF}_n$ onto the set of $(b_1, \dots, b_{n+1}) \in \mathrm{VTPF}_{n+1}$
with $b_1 = 1$ and $b_{n+1} > 1$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 34
(`jis-2024-24.8.6-lem-34`). -/
public theorem_wanted valleyless_tieless_prepend_one_bijOn (n : ℕ) (hn : 1 ≤ n) :
    Set.BijOn (fun f : Fin n → Fin n => (Fin.cons (0 : Fin (n + 1)) (fun i => (f i).succ) :
        Fin (n + 1) → Fin (n + 1)))
      (vtpfSet n : Set (Fin n → Fin n))
      {g | g ∈ vtpfSet (n + 1) ∧ g 0 = 0 ∧ g (Fin.last n) ≠ 0}

set_option quotPrecheck false in
/-- Number of `α ∈ PTPF_m` whose first and last entries satisfy `r`. -/
local notation "ptpfEnds" m:max r:max =>
  ((ptpfSet m).filter (fun f => ∃ i j : Fin m, i.val = 0 ∧ j.val + 1 = m ∧ r (f i) (f j))).card

/-- **First and last entries of peakless-tieless parking functions.** A parking function
$(a_1, \dots, a_m)$ is peakless-tieless if $a_i \ne a_{i+1}$ for all $1 \le i \le m - 1$ and there
is no $i$ with $a_{i-1} < a_i > a_{i+1}$. Let $G_m$, $E_m$ and $L_m$ be the sets of
peakless-tieless parking functions of length $m$ with $a_1 > a_m$, $a_1 = a_m$ and $a_1 < a_m$,
respectively. Then $|E_{n+1}| = |L_n|$ for every $n \ge 1$, and $|G_{n+1}| = |L_{n+1}|$ for every
$n \ge 0$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 40
(`jis-2024-24.8.6-lem-40`). -/
public theorem_wanted peakless_tieless_ends_card (n : ℕ) :
    (1 ≤ n → ptpfEnds (n + 1) (fun a b : Fin (n + 1) => a = b) =
      ptpfEnds n (fun a b : Fin n => a < b)) ∧
    ptpfEnds (n + 1) (fun a b : Fin (n + 1) => b < a) =
      ptpfEnds (n + 1) (fun a b : Fin (n + 1) => a < b)

/-- **Peakless-tieless parking functions with first entry below the last.** For every
$n \in \mathbb{N}$, the number of parking functions $(a_1, \dots, a_{n+1})$ of length $n + 1$
with no ties (no $i$ with $a_i = a_{i+1}$), no peaks (no $i$ with $a_{i-1} < a_i$ and
$a_i > a_{i+1}$) and $a_1 < a_{n+1}$ is the Fine number $F(n + 1)$, indexed from $0$ so that
$F(0) = 1$.

In the indexing of OEIS A000957, $F(n + 1)$ is the term of index $n + 2$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorem 41
(`jis-2024-24.8.6-thm-41`). -/
public theorem_wanted card_peakless_tieless_first_lt_last (n : ℕ) :
    ((ptpfEnds (n + 1) (fun a b : Fin (n + 1) => a < b) : ℕ) : ℚ) = fineNumber (n + 1)

/-- **Peakless parking functions with $n - 1$ ties.** For every $n \ge 1$, exactly one parking
function $(a_1, \dots, a_n)$ of length $n$ has no peaks (no $i$ with $a_{i-1} < a_i$ and
$a_i > a_{i+1}$) and exactly $n - 1$ ties (indices $i \in \{1, \dots, n - 1\}$ with
$a_i = a_{i+1}$).

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 42
(`jis-2024-24.8.6-lem-42`). -/
public theorem_wanted card_peakless_parkingFunction_max_ties (n : ℕ) (hn : 1 ≤ n) :
    ((pfSet n).filter (fun f => (NoPeaks f) ∧
      (Finset.univ.filter (fun i : Fin n => ∃ j : Fin n, j.val = i.val + 1 ∧ f i = f j)).card =
        n - 1)).card = 1

/-- **Every statistic encoding comes from a parking function.** Write a parking function $f$ of
length $n$ as the sequence $(a_1, \dots, a_n)$ with $a_j = f(j-1) + 1$. Its statistic encoding is
the word $w_1 \cdots w_{n-1}$ over the letters $A$, $D$, $T$ with $w_j = A$ if $a_j < a_{j+1}$
(an ascent), $w_j = D$ if $a_j > a_{j+1}$ (a descent) and $w_j = T$ if $a_j = a_{j+1}$ (a tie).
For every natural number $n$, every word of length $n - 1$ over $A$, $D$, $T$ (the empty word
when $n = 0$) is the statistic encoding of some parking function of length $n$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorem 48
(`jis-2024-24.8.6-thm-48`). -/
public theorem_wanted exists_parkingFunction_statEnc (n : ℕ) (w : Fin (n - 1) → Ordering) :
    ∃ f : Fin n → Fin n, IsParkingFunction n f ∧ statEnc n f = w

/-- **Uniquely encoded parking functions have steps of at most one and no gaps.** The statistic
encoding of $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ is the word over $\{A, D, T\}$ whose
letter at each position $0 \le i \le n - 2$ is $A$, $D$ or $T$ according as $f(i) < f(i+1)$,
$f(i) > f(i+1)$ or $f(i) = f(i+1)$. Let $f$ be a parking function of length $n$ such that every
parking function of length $n$ with the same statistic encoding equals $f$. Then
$|f(i+1) - f(i)| \le 1$ for all $0 \le i \le n - 2$, and for all $q < p$ in $\{0, \dots, n-1\}$,
if $p$ is a value of $f$ then so is $q$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 49
(`jis-2024-24.8.6-lem-49`). -/
public theorem_wanted unique_statEnc_adjacent_and_downward_closed (n : ℕ)
    (f : Fin n → Fin n) (hf : IsParkingFunction n f)
    (huniq : ∀ g : Fin n → Fin n, IsParkingFunction n g → statEnc n g = statEnc n f → g = f) :
    (∀ i j : Fin n, j.val = i.val + 1 → (f j : ℕ) ≤ f i + 1 ∧ (f i : ℕ) ≤ f j + 1) ∧
    ∀ p q : Fin n, q < p → (∃ i, f i = p) → ∃ i, f i = q

/-- **The sorted rearrangement of a uniquely encoded parking function.** The statistic encoding
of $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ is the word over $\{A, D, T\}$ whose letter at
each position $0 \le i \le n - 2$ is $A$, $D$ or $T$ according as $f(i) < f(i+1)$,
$f(i) > f(i+1)$ or $f(i) = f(i+1)$. Let $f$ be a parking function of length $n$ such that every
parking function of length $n$ with the same statistic encoding equals $f$, and let
$\beta : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ be nondecreasing and take each value as often
as $f$ does. Then the statistic encoding of $\beta$ consists of $A$'s followed by $T$'s (either
block may be empty).

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 50
(`jis-2024-24.8.6-lem-50`). -/
public theorem_wanted unique_statEnc_sorted_form (n : ℕ) (f : Fin n → Fin n)
    (hf : IsParkingFunction n f)
    (huniq : ∀ g : Fin n → Fin n, IsParkingFunction n g → statEnc n g = statEnc n f → g = f)
    (β : Fin n → Fin n) (hβ : Monotone β)
    (hβf : Finset.univ.val.map β = Finset.univ.val.map f) :
    IsAstarTstar (statEnc n β)

/-- **Valley plateaus of a uniquely encoded parking function equal $1$.** For a map
$g : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$, its statistic encoding is the word of length
$n - 1$ whose $k$-th letter, for $1 \le k \le n - 1$, is $<$, $=$ or $>$ according as
$g(k-1) < g(k)$, $g(k-1) = g(k)$ or $g(k-1) > g(k)$. Let $f$ be a parking function of length $n$
such that every parking function of length $n$ with the same statistic encoding as $f$ equals
$f$, and write $\alpha_k = f(k-1) + 1$ for $1 \le k \le n$. If $2 \le i \le j \le n - 1$,
$\alpha_{i-1} > \alpha_i$, $\alpha_k = \alpha_i$ for every $k$ with $i \le k \le j$, and
$\alpha_j < \alpha_{j+1}$, then $\alpha_k = 1$ for every $k$ with $i \le k \le j$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 51
(`jis-2024-24.8.6-lem-51`). -/
public theorem_wanted unique_statEnc_valley_plateau_eq_one (n : ℕ) (f : Fin n → Fin n)
    (hf : IsParkingFunction n f)
    (huniq : ∀ g : Fin n → Fin n, IsParkingFunction n g → statEnc n g = statEnc n f → g = f)
    (a b c d : Fin n) (hab : a.val + 1 = b.val) (hbc : b ≤ c) (hcd : c.val + 1 = d.val)
    (hfa : f b < f a) (hconst : ∀ k : Fin n, b ≤ k → k ≤ c → f k = f b) (hfd : f c < f d) :
    ∀ k : Fin n, b ≤ k → k ≤ c → (f k : ℕ) = 0

/-- **Statistic encodings with a unique parking function.** The statistic encoding of a parking
function $(a_1, \dots, a_n)$ is the word $w_1 \cdots w_{n-1}$ over $\{A, D, T\}$ with $w_i = A$ if
$a_i < a_{i+1}$, $w_i = D$ if $a_i > a_{i+1}$ and $w_i = T$ if $a_i = a_{i+1}$. For every
$n \in \mathbb{N}$, a word over $\{A, D, T\}$ with one letter for each $1 \le i \le n - 1$ is the
statistic encoding of exactly one parking function of length $n$ if and only if it consists of
$A$'s followed by $T$'s or of $T$'s followed by $D$'s (either block may be empty).

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorem 52
(`jis-2024-24.8.6-thm-52`). -/
public theorem_wanted unique_parkingFunction_statEnc_iff (n : ℕ)
    (w : Fin (n - 1) → Ordering) :
    (∃! f : Fin n → Fin n, IsParkingFunction n f ∧ statEnc n f = w) ↔
      (IsAstarTstar w) ∨ IsTstarDstar w

/-- **Tie-and-value map.** Let $n \in \mathbb{N}$ and $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$.
The ties of $f$ are the positions $i \in \{1, \dots, n-1\}$ with $f(i-1) = f(i)$, and its values
are the elements of the image of $f$. Form the list of the ties in decreasing order followed by
the values in increasing order. Then $\varphi_n(f) : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ is the
map whose value at $k$ is the entry of this list at position $k$ (counting from $0$), or $k$
itself if the list has at most $k$ entries.

For nondecreasing $f$ the list has exactly $n$ entries. In the paper's one-based notation,
$\varphi$ sends $\alpha = (a_1, \dots, a_n)$ to its tie set $\{j + 1 : a_j = a_{j+1}\}$ in
decreasing order followed by its value set in increasing order.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, the function `φ` of
Theorem 30 (`jis-2024-24.8.6-thm-30`), defined as in arXiv:2312.16786v1, Definition 4.2. -/
public def peaklessTielessOfNondecreasing (n : ℕ) (f : Fin n → Fin n) : Fin n → Fin n :=
  fun k =>
    ((List.finRange n).reverse.filter (fun i => (List.finRange n).any fun j =>
        Nat.beq (j.val + 1) i.val && Nat.beq (f j).val (f i).val) ++
      (List.finRange n).filter (fun v => (List.finRange n).any fun i =>
        Nat.beq (f i).val v.val)).getD k.val k

/-- **Example of the tie-and-value map.** For $n = 6$, the tie-and-value map $\varphi$ sends
$(0, 0, 1, 2, 3, 3)$ to $(5, 1, 0, 1, 2, 3)$; in the paper's one-based values this reads
$\varphi(1, 1, 2, 3, 4, 4) = (6, 2, 1, 2, 3, 4)$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, the function `φ` of
Theorem 30, Example (arXiv:2312.16786v1, Example 4.3). -/
public theorem peaklessTielessOfNondecreasing_example :
    peaklessTielessOfNondecreasing 6 ![0, 0, 1, 2, 3, 3] = ![5, 1, 0, 1, 2, 3] := by
  funext k
  fin_cases k <;> rfl

/-- **Nondecreasing and peakless-tieless parking functions are in bijection.** For every
$n \in \mathbb{N}$, the tie-and-value map $\varphi$ is a bijection from the nondecreasing parking
functions of length $n$ onto the peakless-tieless parking functions of length $n$, that is, the
parking functions $(a_1, \dots, a_n)$ with $a_i \ne a_{i+1}$ for all $1 \le i \le n - 1$ and no $i$
with $a_{i-1} < a_i > a_{i+1}$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorem 30
(`jis-2024-24.8.6-thm-30`; arXiv:2312.16786v1, Theorem 4.4). -/
public theorem_wanted peaklessTielessOfNondecreasing_bijOn (n : ℕ) :
    Set.BijOn (peaklessTielessOfNondecreasing n) ↑(ndpfSet n) ↑(ptpfSet n)

/-- **Fuel-bounded ascent-to-descent rearrangement.** For a fuel $N \in \mathbb{N}$ and a word
$x = x_1 \cdots x_m$ over $\mathbb{N}$, the word $\nu_N(x)$ is defined by recursion on $N$:
$\nu_0(x) = x$, and $\nu_{N+1}(x) = x$ when $m \le 1$. For $m \ge 2$, let $A$ be the set of
positions of the least letter of $x$ and $B$ the set of positions of its greatest letter. If
$b \le a$ for all $a \in A$ and $b \in B$ (Case 1), put $i = \max A$ and $j = \min B$; then
$\nu_{N+1}(x) = \nu_N(x_1 \cdots x_{j-1})\, x_i\, \nu_N(x_{j+1} \cdots x_{i-1})\, x_j\,
\nu_N(x_{i+1} \cdots x_m)$. Otherwise (Case 2), let $i$ be the greatest $a \in A$ such that
$a < b$ for some $b \in B$, and $j$ the least $b \in B$ with $b > i$; then
$\nu_{N+1}(x) = \nu_N(x_1 \cdots x_{i-1})\, x_j\, \nu_N(x_{i+1} \cdots x_{j-1})\, x_i\,
\nu_N(x_{j+1} \cdots x_m)$.

Every recursive call is on a strictly shorter word, so fuel $N = m$ never runs out.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Definition `nu` (Section 2). -/
public def ascentToDescentRearrangementAux : ℕ → List ℕ → List ℕ
  | 0, l => l
  | fuel + 1, l =>
    if l.length ≤ 1 then l else
      let mn := l.foldr min (l.headD 0)
      let mx := l.foldr max (l.headD 0)
      let amin := (List.range l.length).filter fun k => l.getD k 0 == mn
      let amax := (List.range l.length).filter fun k => l.getD k 0 == mx
      if amin.all fun a => amax.all fun b => b ≤ a then
        let i := amin.foldr max 0
        let j := amax.foldr min l.length
        ascentToDescentRearrangementAux fuel (l.take j) ++ [l.getD i 0] ++
          ascentToDescentRearrangementAux fuel ((l.drop (j + 1)).take (i - j - 1)) ++
          [l.getD j 0] ++ ascentToDescentRearrangementAux fuel (l.drop (i + 1))
      else
        let i := (amin.filter fun a => amax.any fun b => a < b).foldr max 0
        let j := (amax.filter fun b => i < b).foldr min l.length
        ascentToDescentRearrangementAux fuel (l.take i) ++ [l.getD j 0] ++
          ascentToDescentRearrangementAux fuel ((l.drop (i + 1)).take (j - i - 1)) ++
          [l.getD i 0] ++ ascentToDescentRearrangementAux fuel (l.drop (j + 1))

/-- **Ascent-to-descent rearrangement.** For a word $x = x_1 \cdots x_m$ over $\mathbb{N}$, the
ascent-to-descent rearrangement of $x$ is $\nu(x) = \nu_m(x)$, the fuel-bounded
ascent-to-descent rearrangement $\nu_N(x)$ with fuel $N = m$, the length of $x$.

Every recursive call of $\nu_N$ is on a strictly shorter word, so the fuel $m$ never runs out.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Definition `nu` (Section 2). -/
public def ascentToDescentRearrangement (x : List ℕ) : List ℕ :=
  ascentToDescentRearrangementAux x.length x

/-- **Words of length at most one are fixed by the ascent-to-descent rearrangement.** Every word
$x$ over $\mathbb{N}$ of length at most $1$ satisfies $\nu(x) = x$, where $\nu$ is the
ascent-to-descent rearrangement.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Definition `nu`, Case 0. -/
public theorem ascentToDescentRearrangement_of_length_le_one {x : List ℕ} (hx : x.length ≤ 1) :
    ascentToDescentRearrangement x = x := by
  unfold ascentToDescentRearrangement
  cases h : x.length with
  | zero => rfl
  | succ k => simp only [ascentToDescentRearrangementAux, hx, ↓reduceIte]

/-- **Example of the ascent-to-descent rearrangement.** The ascent-to-descent rearrangement $\nu$
satisfies $\nu(1\,4\,1\,3\,4\,3\,1\,2\,1) = 4\,1\,4\,3\,1\,1\,2\,1\,3$, $\nu(1\,4) = 4\,1$ and
$\nu(3\,1\,2\,1) = 1\,2\,1\,3$.

The last two are the sub-steps of the first: $\nu(1\,4)$ falls under Case 2 of the definition
and $\nu(3\,1\,2\,1)$ under Case 1.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Example following Definition `nu`. -/
public theorem ascentToDescentRearrangement_example :
    ascentToDescentRearrangement [1, 4, 1, 3, 4, 3, 1, 2, 1] = [4, 1, 4, 3, 1, 1, 2, 1, 3] ∧
      ascentToDescentRearrangement [1, 4] = [4, 1] ∧
      ascentToDescentRearrangement [3, 1, 2, 1] = [1, 2, 1, 3] := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

set_option quotPrecheck false in
/-- Ascent set (1-based positions) of a word `x : List ℕ`. -/
local notation "ascList" x:max =>
  Finset.image (· + 1)
    ((Finset.range (List.length x - 1)).filter fun i => List.getD x i 0 < List.getD x (i + 1) 0)

set_option quotPrecheck false in
/-- Descent set (1-based positions) of a word `x : List ℕ`. -/
local notation "desList" x:max =>
  Finset.image (· + 1)
    ((Finset.range (List.length x - 1)).filter fun i => List.getD x (i + 1) 0 < List.getD x i 0)

/-- **Ascents of a word are the descents of its rearrangement.** For a word
$x = x_1 \cdots x_m$ over $\mathbb{N}$, let the ascent set $\mathrm{Asc}(x)$ be the set of
$i \in \{1, \dots, m - 1\}$ with $x_i < x_{i+1}$, and the descent set $\mathrm{Des}(x)$ the set
of $i \in \{1, \dots, m - 1\}$ with $x_i > x_{i+1}$. Then every word $x$ over $\mathbb{N}$
satisfies $\mathrm{Asc}(x) = \mathrm{Des}(\nu(x))$, where $\nu$ is the ascent-to-descent
rearrangement.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Lemma 11 (`jis-2024-24.8.6-lem-11`). -/
public theorem_wanted ascList_eq_desList_ascentToDescentRearrangement (x : List ℕ) :
    ascList x = desList (ascentToDescentRearrangement x)

/-- **The ascent-to-descent rearrangement is injective.** The ascent-to-descent rearrangement
$\nu$ is injective on finite words over $\mathbb{N}$: if $\nu(x) = \nu(x')$, then $x = x'$.

Since $\nu$ rearranges letters, this is the same as injectivity of $\nu$ on the rearrangements of
each fixed word.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Lemma 13 (`jis-2024-24.8.6-lem-13`). -/
public theorem_wanted ascentToDescentRearrangement_injective :
    Function.Injective ascentToDescentRearrangement

/-- **The ascent-to-descent rearrangement matches ascent and descent sets.** Let $y$ be a finite
word over $\mathbb{N}$ and $I$ a finite set of natural numbers. For a word $x = x_1 \cdots x_m$,
let the ascent set $\mathrm{Asc}(x)$ be the set of $i \in \{1, \dots, m - 1\}$ with
$x_i < x_{i+1}$, and the descent set $\mathrm{Des}(x)$ the set of those $i$ with $x_i > x_{i+1}$.
Then the ascent-to-descent rearrangement $\nu$ maps the set of rearrangements $x$ of $y$ with
$\mathrm{Asc}(x) = I$ bijectively onto the set of rearrangements $x$ of $y$ with
$\mathrm{Des}(x) = I$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Proposition 10 (`jis-2024-24.8.6-prop-10`). -/
public theorem_wanted ascentToDescentRearrangement_bijOn (y : List ℕ) (I : Finset ℕ) :
    Set.BijOn ascentToDescentRearrangement {x | x.Perm y ∧ ascList x = I}
      {x | x.Perm y ∧ desList x = I}

/-- **Flicking valleyless-tieless parking functions.** Identify a parking function $f$ of length
$m$ with the word $(f(0) + 1, \dots, f(m-1) + 1)$. A word $(a_1, \dots, a_m)$ has a tie if
$a_k = a_{k+1}$ for some $k$, a peak if $a_{k-1} < a_k > a_{k+1}$ for some $k$, and a valley if
$a_{k-1} > a_k < a_{k+1}$ for some $k$. For $1 \le i \le m$, let
$\mathrm{flick}_i(x_1, \dots, x_m) = (x_i, x_{i-1}, \dots, x_1, x_m, x_{m-1}, \dots, x_{i+1})$,
the block $x_m, \dots, x_{i+1}$ being empty when $i = m$. Let $D$ be the set of parking
functions $(a_1, \dots, a_{n+1})$ with no valleys and no ties such that $a_1 = 1$ and
$a_{n+1} > 1$, and let $\varphi$ send $v \in D$ to $\mathrm{flick}_i(v)$, where $i$ is the
position of the strictly largest entry of $v$. Then $\varphi$ is a bijection from $D$ onto the
set of parking functions $(b_1, \dots, b_{n+1})$ with no peaks and no ties such that
$b_1 > b_{n+1}$.

The paper's domain condition $a_{i+1} > 1$ is a typo for $a_{n+1} > 1$, its domain in the same
display.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Proposition 37 (`jis-2024-24.8.6-prop-37`). -/
public theorem_wanted valleyless_tieless_flick_bijOn (n : ℕ) :
    ∃ φ : (Fin (n + 1) → Fin (n + 1)) → Fin (n + 1) → Fin (n + 1),
      (∀ v ∈ vtpfSet (n + 1), v 0 = 0 → v (Fin.last n) ≠ 0 → ∀ p : Fin (n + 1),
        (∀ j, j ≠ p → v j < v p) →
        φ v = fun q => if h : q.val ≤ p.val then v ⟨p.val - q.val, by have := p.isLt; omega⟩
          else v ⟨n + 1 + p.val - q.val, by have := q.isLt; omega⟩) ∧
      Set.BijOn φ {v | v ∈ vtpfSet (n + 1) ∧ v 0 = 0 ∧ v (Fin.last n) ≠ 0}
        {g | g ∈ ptpfSet (n + 1) ∧ g (Fin.last n) < g 0}

set_option quotPrecheck false in
/-- The two-row Young diagram of shape `(n, n)`. -/
local notation "twoRowShape" n:max =>
  YoungDiagram.ofRowLens [n, n] (by simp [List.sortedGE_cons, List.sortedGE_nil])

/-- **Gudmundsson's bijection between Dyck words and standard Young tableaux.** For every $n$
there is a map $f$ from Dyck words to semistandard Young tableaux of the two-row shape $(n, n)$
with the following two properties. First, for every Dyck word $w$ of semilength $n$ and every
$i \ge 1$, if the $i$th letter of $w$ is an up step $U$ then $i$ is an entry of the first row of
$f(w)$, and if it is a down step $D$ then $i$ is an entry of the second row. Second, $f$
restricts to a bijection from the Dyck words of semilength $n$ onto the standard tableaux of
shape $(n, n)$, that is, those whose $2n$ entries are distinct and lie in $\{1, \dots, 2n\}$.

Since $f(w)$ is standard, $i$ lies in the first row of $f(w)$ exactly when the $i$th letter of $w$
is $U$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Lemma 22 (Gudmundsson, Theorem 6) (`jis-2024-24.8.6-lem-22`). -/
public theorem_wanted exists_dyckWord_standardYoungTableau_bijOn (n : ℕ) :
    ∃ f : DyckWord → SemistandardYoungTableau (twoRowShape n),
      (∀ w : DyckWord, w.semilength = n → ∀ i : ℕ,
        (w.toList[i]? = some DyckStep.U → ∃ j < n, f w 0 j = i + 1) ∧
        (w.toList[i]? = some DyckStep.D → ∃ j < n, f w 1 j = i + 1)) ∧
      Set.BijOn f {w | w.semilength = n}
        {T | (∀ c ∈ twoRowShape n,
            ∀ c' ∈ twoRowShape n, T c.1 c.2 = T c'.1 c'.2 → c = c') ∧
          ∀ c ∈ twoRowShape n, 1 ≤ T c.1 c.2 ∧ T c.1 c.2 ≤ 2 * n}

/-- **Dyck words and nondecreasing parking functions.** For every $n$ there is a map $g$ from Dyck
words to maps $\{0, \dots, n-1\} \to \{0, \dots, n-1\}$ such that, for every Dyck word $w$ of
semilength $n$ and every $i < n$, $g(w)(i)$ is the number of down steps $D$ of $w$ before its
$(i+1)$st up step $U$, and $g$ restricts to a bijection from the Dyck words of semilength $n$
onto the nondecreasing parking functions of length $n$.

With one-based entries, the $i$th entry of the parking function is one plus the number of $D$s
before the $i$th $U$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Lemma 23 (`jis-2024-24.8.6-lem-23`). -/
public theorem_wanted exists_dyckWord_nondecreasing_parkingFunction_bijOn (n : ℕ) :
    ∃ g : DyckWord → Fin n → Fin n,
      (∀ w : DyckWord, w.semilength = n → ∀ (i : Fin n) (k : ℕ),
        w.toList[k]? = some DyckStep.U → (w.toList.take k).count DyckStep.U = i.val →
        ((g w i : Fin n) : ℕ) = (w.toList.take k).count DyckStep.D) ∧
      Set.BijOn g {w | w.semilength = n} ↑(ndpfSet n)

/-- **Peakless parking functions with $n - 2$ ties.** For every $n \ge 2$, the number of parking
functions $(a_1, \dots, a_n)$ of length $n$ that have no peaks (no $i$ with $a_{i-1} < a_i$ and
$a_i > a_{i+1}$) and exactly $n - 2$ ties (indices $i \in \{1, \dots, n - 1\}$ with
$a_i = a_{i+1}$) is $(n - 1)n$.

The paper prints $n(n + 1)$, which contradicts its own table ($2, 6, 12, 20, 30$ for
$n = 2, \dots, 6$); its proof counts tuples with $i$ leading ones followed by $n - i \ge 1$
copies of one value, so $1 \le i \le n - 1$ and each monotone direction contributes
$\sum_{i=1}^{n-1} i$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Lemma 43 (`jis-2024-24.8.6-lem-43`). -/
public theorem_wanted card_peakless_parkingFunction_ties_eq_sub_two (n : ℕ) (hn : 2 ≤ n) :
    ((pfSet n).filter (fun f => (NoPeaks f) ∧
      (Finset.univ.filter (fun i : Fin n => ∃ j : Fin n, j.val = i.val + 1 ∧ f i = f j)).card =
        n - 2)).card = (n - 1) * n

end

end MetaMathlibExt
