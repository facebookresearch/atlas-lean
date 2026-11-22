/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Order.Hom.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.PermutationStatistics
public import WantedExt.Combinatorics.Enumerative.OddFibonacciWanted

namespace MetaMathlibExt

@[expose] public section

open MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

/-- **No king permutation of length at least $2$ is separable.** For every $n \ge 2$, every
permutation $\sigma$ of $\{0, 1, \dots, n - 1\}$ in which adjacent entries never differ by exactly
$1$, that is, $|\sigma(i + 1) - \sigma(i)| \ne 1$ whenever $i + 1 < n$, contains the classical
pattern $2413$ or the classical pattern $3142$. Since the separable permutations are those
avoiding both $2413$ and $3142$, no such permutation is separable.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Theorem 2 (`integers-2026-A59-thm-2`). -/
public theorem_wanted king_permutation_not_separable (n : ℕ) (hn : 2 ≤ n)
    (σ : Equiv.Perm (Fin n))
    (hking : ∀ i j : Fin n, (j : ℕ) = i + 1 →
      (σ i : ℕ) + 1 ≠ σ j ∧ (σ j : ℕ) + 1 ≠ σ i) :
    HasPattern σ ![1, 3, 0, 2] ∨ HasPattern σ ![2, 0, 3, 1]

/-- **King permutations of length at least $2$ contain $12$, $21$, $132$, $213$, $231$ and $312$.**
For every $n \ge 2$, every permutation $\sigma$ of $\{0, 1, \dots, n - 1\}$ in which adjacent
entries never differ by exactly $1$, that is, $|\sigma(i + 1) - \sigma(i)| \ne 1$ whenever
$i + 1 < n$, contains each of the classical patterns $12$, $21$, $132$, $213$, $231$ and $312$.

Theorem 1 also lists nine partially ordered patterns that no such permutation avoids; they are
not part of this statement.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Theorem 1 (`integers-2026-A59-thm-1`). -/
public theorem_wanted king_permutation_hasPattern_classical (n : ℕ) (hn : 2 ≤ n)
    (σ : Equiv.Perm (Fin n))
    (hking : ∀ i j : Fin n, (j : ℕ) = i + 1 →
      (σ i : ℕ) + 1 ≠ σ j ∧ (σ j : ℕ) + 1 ≠ σ i) :
    HasPattern σ ![0, 1] ∧ HasPattern σ ![1, 0] ∧ HasPattern σ ![0, 2, 1] ∧
      HasPattern σ ![1, 0, 2] ∧ HasPattern σ ![1, 2, 0] ∧ HasPattern σ ![2, 0, 1]

/-- **King permutations.** A permutation $\sigma$ of $\{0, 1, \dots, n - 1\}$ is a king permutation
if adjacent entries never differ by exactly $1$: for every position $i$ with $i + 1 < n$, neither
$\sigma(i + 1) = \sigma(i) + 1$ nor $\sigma(i) = \sigma(i + 1) + 1$. Equivalently,
$|\sigma(i + 1) - \sigma(i)| > 1$ for all adjacent positions $i$ and $i + 1$.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1.3. -/
def IsKingPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, (j : ℕ) = i + 1 → (σ i : ℕ) + 1 ≠ σ j ∧ (σ j : ℕ) + 1 ≠ σ i

/-- **Number of ascents of a permutation.** For a permutation $\sigma$ of $\{0, 1, \dots, n - 1\}$
written in one-line notation, $\operatorname{asc}(\sigma)$ is the number of positions $i$ with
$i + 1 < n$ and $\sigma(i) < \sigma(i + 1)$.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1 (statistics). -/
def permAscentCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => ∃ j : Fin n, (j : ℕ) = i + 1 ∧ σ i < σ j).card

/-- **Number of descents of a permutation.** For a permutation $\sigma$ of $\{0, 1, \dots, n - 1\}$
written in one-line notation, $\operatorname{des}(\sigma)$ is the number of positions $i$ with
$i + 1 < n$ and $\sigma(i + 1) < \sigma(i)$.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1 (statistics). -/
def permDescentCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => ∃ j : Fin n, (j : ℕ) = i + 1 ∧ σ j < σ i).card

/-- **Statistics of the permutation $123$.** The identity permutation of $\{0, 1, 2\}$, written
$012$ in one-line notation and $123$ after shifting every value up by one, has two ascents, no
descents, three left-to-right maxima, one right-to-left maximum, one left-to-right minimum and
three right-to-left minima.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1 (statistics). -/
theorem permStats_one_fin_three :
    permAscentCount (1 : Equiv.Perm (Fin 3)) = 2 ∧ permDescentCount (1 : Equiv.Perm (Fin 3)) = 0 ∧
      permLeftToRightMaxCount (1 : Equiv.Perm (Fin 3)) = 3 ∧
      permRightToLeftMaxCount (1 : Equiv.Perm (Fin 3)) = 1 ∧
      permLeftToRightMinCount (1 : Equiv.Perm (Fin 3)) = 1 ∧
      permRightToLeftMinCount (1 : Equiv.Perm (Fin 3)) = 3 := by
  decide

/-- **Statistics of the permutation $321$.** The reversal permutation $i \mapsto 2 - i$ of
$\{0, 1, 2\}$, written $210$ in one-line notation and $321$ after shifting every value up by
one, has no ascents, two descents, one left-to-right maximum, three right-to-left maxima, three
left-to-right minima and one right-to-left minimum.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1 (statistics). -/
theorem permStats_revPerm_fin_three :
    permAscentCount (Fin.revPerm : Equiv.Perm (Fin 3)) = 0 ∧
      permDescentCount (Fin.revPerm : Equiv.Perm (Fin 3)) = 2 ∧
      permLeftToRightMaxCount (Fin.revPerm : Equiv.Perm (Fin 3)) = 1 ∧
      permRightToLeftMaxCount (Fin.revPerm : Equiv.Perm (Fin 3)) = 3 ∧
      permLeftToRightMinCount (Fin.revPerm : Equiv.Perm (Fin 3)) = 3 ∧
      permRightToLeftMinCount (Fin.revPerm : Equiv.Perm (Fin 3)) = 1 := by
  decide

/-- **Containing a flat pattern with one bottom label.** Let $\sigma$ be a permutation of
$\{0, 1, \dots, n - 1\}$ and let $j \in \{0, 1, 2, 3\}$. Then $\sigma$ contains the flat partially
ordered pattern $P_{j+1}$ of size $4$, in which label $j + 1$ lies below the other three labels
(which are mutually incomparable), if there are positions $i_0 < i_1 < i_2 < i_3$ such that
$\sigma(i_j) < \sigma(i_m)$ for every $m \in \{0, 1, 2, 3\}$ with $m \neq j$.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1.1 and Table 1. -/
def ContainsFlatPOPBelow {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : Fin 4) : Prop :=
  ∃ f : Fin 4 ↪o Fin n, ∀ m, m ≠ j → σ (f j) < σ (f m)

/-- **Containing a flat pattern with one top label.** Let $\sigma$ be a permutation of
$\{0, 1, \dots, n - 1\}$ and let $j \in \{0, 1, 2, 3\}$. Then $\sigma$ contains the flat partially
ordered pattern $Q_{j+1}$ of size $4$, in which label $j + 1$ lies above the other three labels,
if there are positions $i_0 < i_1 < i_2 < i_3$ such that $\sigma(i_m) < \sigma(i_j)$ for every
$m \in \{0, 1, 2, 3\}$ with $m \neq j$.

The pattern $Q_k$ is the complement of the pattern $P_k$ of Table 1, in which label $k$ lies
below the other three labels.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1.1 and Table 1. -/
def ContainsFlatPOPAbove {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : Fin 4) : Prop :=
  ∃ f : Fin 4 ↪o Fin n, ∀ m, m ≠ j → σ (f m) < σ (f j)

/-- **Containing $P_{j+1}$ forces length at least $4$.** Let $\sigma$ be a permutation of
$\{0, 1, \dots, n - 1\}$ and let $j \in \{0, 1, 2, 3\}$. If $\sigma$ contains the flat partially
ordered pattern $P_{j+1}$ of size $4$, in which label $j + 1$ lies below the other three labels,
then $n \ge 4$.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1.1. -/
theorem four_le_of_containsFlatPOPBelow {n : ℕ} {σ : Equiv.Perm (Fin n)} {j : Fin 4}
    (h : ContainsFlatPOPBelow σ j) : 4 ≤ n := by
  obtain ⟨f, -⟩ := h
  simpa using Fintype.card_le_of_embedding f.toEmbedding

/-- **Containing $Q_{j+1}$ forces length at least $4$.** Let $\sigma$ be a permutation of
$\{0, 1, \dots, n - 1\}$ and let $j \in \{0, 1, 2, 3\}$. If $\sigma$ contains the flat partially
ordered pattern $Q_{j+1}$ of size $4$, in which label $j + 1$ lies above the other three labels,
then $n \ge 4$.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1.1. -/
theorem four_le_of_containsFlatPOPAbove {n : ℕ} {σ : Equiv.Perm (Fin n)} {j : Fin 4}
    (h : ContainsFlatPOPAbove σ j) : 4 ≤ n := by
  obtain ⟨f, -⟩ := h
  simpa using Fintype.card_le_of_embedding f.toEmbedding

open Classical in
/-- **Generating function of king permutations avoiding $P_{j+1}$.** For $j \in \{0, 1, 2, 3\}$
let $P_{j+1}$ be the flat partially ordered pattern of length $4$ whose element number $j + 1$
lies below each of the other three: a permutation $\sigma$ contains $P_{j+1}$ if there are
positions $i_0 < i_1 < i_2 < i_3$ with $\sigma(i_j) < \sigma(i_m)$ for every $m \ne j$. A king
permutation is one in which adjacent entries never differ by exactly $1$; let $K_n(P_{j+1})$ be
the set of king permutations of length $n$ that do not contain $P_{j+1}$. The generating function
$A_{P_{j+1}}$ is the formal power series in $x$ with coefficients in $\mathbb{Z}[p, q, u, v]$
$$
A_{P_{j+1}}(x; p, q, u, v) = \sum_{n \ge 0} \sum_{\sigma \in K_n(P_{j+1})}
x^n p^{\operatorname{asc}(\sigma)} q^{\operatorname{des}(\sigma)}
u^{\operatorname{lmax}(\sigma)} v^{\operatorname{rmax}(\sigma)},
$$
where $\operatorname{asc}$, $\operatorname{des}$, $\operatorname{lmax}$ and $\operatorname{rmax}$
count ascents, descents, left-to-right maxima and right-to-left maxima.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1.4. -/
noncomputable def kingFlatPOPBelowGF (j : Fin 4) : PowerSeries (MvPolynomial (Fin 4) ℤ) :=
  PowerSeries.mk fun n =>
    ∑ σ ∈ Finset.univ.filter
        (fun σ : Equiv.Perm (Fin n) => IsKingPerm σ ∧ ¬ ContainsFlatPOPBelow σ j),
      MvPolynomial.X 0 ^ permAscentCount σ * MvPolynomial.X 1 ^ permDescentCount σ *
        MvPolynomial.X 2 ^ permLeftToRightMaxCount σ * MvPolynomial.X 3 ^ permRightToLeftMaxCount σ

open Classical in
/-- **Generating function of king permutations avoiding $Q_{j+1}$.** For $j \in \{0, 1, 2, 3\}$
let $Q_{j+1}$ be the flat partially ordered pattern of length $4$ whose element number $j + 1$
lies above each of the other three: a permutation $\sigma$ contains $Q_{j+1}$ if there are
positions $i_0 < i_1 < i_2 < i_3$ with $\sigma(i_m) < \sigma(i_j)$ for every $m \ne j$. A king
permutation is one in which adjacent entries never differ by exactly $1$; let $K_n(Q_{j+1})$ be
the set of king permutations of length $n$ that do not contain $Q_{j+1}$. The generating function
$\bar A_{Q_{j+1}}$ is the formal power series in $x$ with coefficients in $\mathbb{Z}[p, q, s, t]$
$$
\bar A_{Q_{j+1}}(x; p, q, s, t) = \sum_{n \ge 0} \sum_{\sigma \in K_n(Q_{j+1})}
x^n p^{\operatorname{asc}(\sigma)} q^{\operatorname{des}(\sigma)}
s^{\operatorname{lmin}(\sigma)} t^{\operatorname{rmin}(\sigma)},
$$
where $\operatorname{asc}$, $\operatorname{des}$, $\operatorname{lmin}$ and $\operatorname{rmin}$
count ascents, descents, left-to-right minima and right-to-left minima.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1.4. -/
noncomputable def kingFlatPOPAboveGF (j : Fin 4) : PowerSeries (MvPolynomial (Fin 4) ℤ) :=
  PowerSeries.mk fun n =>
    ∑ σ ∈ Finset.univ.filter
        (fun σ : Equiv.Perm (Fin n) => IsKingPerm σ ∧ ¬ ContainsFlatPOPAbove σ j),
      MvPolynomial.X 0 ^ permAscentCount σ * MvPolynomial.X 1 ^ permDescentCount σ *
        MvPolynomial.X 2 ^ permLeftToRightMinCount σ * MvPolynomial.X 3 ^ permRightToLeftMinCount σ

/-- **Constant term of $A_{P_{j+1}}$.** For every $j \in \{0, 1, 2, 3\}$, the coefficient of $x^0$
in the generating function $A_{P_{j+1}}(x; p, q, u, v)$ of king permutations avoiding the flat
partially ordered pattern $P_{j+1}$ is the constant polynomial $1$.

The empty permutation is the only permutation of length $0$; it is a king permutation, it avoids
$P_{j+1}$, and it has no ascents, descents, left-to-right maxima or right-to-left maxima.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1.4 and proof of Theorem 3. -/
theorem constantCoeff_kingFlatPOPBelowGF (j : Fin 4) :
    PowerSeries.constantCoeff (kingFlatPOPBelowGF j) = 1 := by
  classical
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, kingFlatPOPBelowGF, PowerSeries.coeff_mk]
  rw [Finset.sum_eq_single_of_mem (1 : Equiv.Perm (Fin 0))]
  · simp [permAscentCount, permDescentCount, permLeftToRightMaxCount, permRightToLeftMaxCount]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun i => i.elim0, fun h => by simpa using four_le_of_containsFlatPOPBelow h⟩
  · intro b _ hb
    exact absurd (Subsingleton.elim b 1) hb

/-- **Constant term of $\bar A_{Q_{j+1}}$.** For every $j \in \{0, 1, 2, 3\}$, the coefficient of
$x^0$ in the generating function $\bar A_{Q_{j+1}}(x; p, q, s, t)$ of king permutations avoiding
the flat partially ordered pattern $Q_{j+1}$ is the constant polynomial $1$.

The empty permutation is the only permutation of length $0$; it is a king permutation, it avoids
$Q_{j+1}$, and it has no ascents, descents, left-to-right minima or right-to-left minima.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1.4 and proof of Theorem 3. -/
theorem constantCoeff_kingFlatPOPAboveGF (j : Fin 4) :
    PowerSeries.constantCoeff (kingFlatPOPAboveGF j) = 1 := by
  classical
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, kingFlatPOPAboveGF, PowerSeries.coeff_mk]
  rw [Finset.sum_eq_single_of_mem (1 : Equiv.Perm (Fin 0))]
  · simp [permAscentCount, permDescentCount, permLeftToRightMinCount, permRightToLeftMinCount]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun i => i.elim0, fun h => by simpa using four_le_of_containsFlatPOPAbove h⟩
  · intro b _ hb
    exact absurd (Subsingleton.elim b 1) hb

/-- **Rational generating function for king permutations avoiding $P_1$.** Let $P_1$ be the flat
partially ordered pattern of length $4$ whose first element lies below each of the other three,
and let $A_{P_1}(x; p, q, u, v)$ be the generating function of king permutations avoiding $P_1$,
in which $x$ marks length and $p$, $q$, $u$, $v$ mark ascents, descents, left-to-right maxima and
right-to-left maxima. Then $B \cdot A_{P_1} = A$ in $\mathbb{Z}[p, q, u, v][[x]]$, where
$A = \sum_{k=0}^{7} a_k x^k$ and $B = \sum_{k=0}^{7} b_k x^k$ with $a_0 = b_0 = -1$, $a_1 = -uv$,
$b_1 = 0$, $a_2 = b_2 = pqv$, $a_3 = pq^2v + pquv^2$, $b_3 = pq^2v$,
$a_4 = p^2q^2v^2 + pq^3v^2 + pq^2uv^2 - p^2qu^2v^2 - pq^2u^2v^2$, $b_4 = p^2q^2v^2 + pq^3v^2$,
$a_5 = p^2q^3v^2 - p^2q^2u^2v^2 + 2p^2q^3v^3 + pq^4v^3 - 2p^2q^2u^2v^3 - pq^3u^2v^3$,
$b_5 = p^2q^3v^2 + 2p^2q^3v^3 + pq^4v^3$,
$a_6 = 2p^2q^4v^3 - 2p^2q^3u^2v^3 + p^2q^4v^4 - p^2q^3u^2v^4$, $b_6 = 2p^2q^4v^3 + p^2q^4v^4$,
$a_7 = p^2q^5v^4 - p^2q^4u^2v^4$ and $b_7 = p^2q^5v^4$. Since $B$ has constant term $-1$, this
determines $A_{P_1} = A / B$.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Theorem 3. -/
theorem_wanted kingFlatPOPBelowGF_zero_eq :
    let p : MvPolynomial (Fin 4) ℤ := MvPolynomial.X 0
    let q : MvPolynomial (Fin 4) ℤ := MvPolynomial.X 1
    let u : MvPolynomial (Fin 4) ℤ := MvPolynomial.X 2
    let v : MvPolynomial (Fin 4) ℤ := MvPolynomial.X 3
    let x : PowerSeries (MvPolynomial (Fin 4) ℤ) := PowerSeries.X
    let c : MvPolynomial (Fin 4) ℤ → PowerSeries (MvPolynomial (Fin 4) ℤ) := PowerSeries.C
    (c (-1) + c (p * q * v) * x ^ 2 + c (p * q ^ 2 * v) * x ^ 3 +
        c (p ^ 2 * q ^ 2 * v ^ 2 + p * q ^ 3 * v ^ 2) * x ^ 4 +
        c (p ^ 2 * q ^ 3 * v ^ 2 + 2 * p ^ 2 * q ^ 3 * v ^ 3 + p * q ^ 4 * v ^ 3) * x ^ 5 +
        c (2 * p ^ 2 * q ^ 4 * v ^ 3 + p ^ 2 * q ^ 4 * v ^ 4) * x ^ 6 +
        c (p ^ 2 * q ^ 5 * v ^ 4) * x ^ 7) * kingFlatPOPBelowGF 0 =
      c (-1) - c (u * v) * x + c (p * q * v) * x ^ 2 +
        c (p * q ^ 2 * v + p * q * u * v ^ 2) * x ^ 3 +
        c (p ^ 2 * q ^ 2 * v ^ 2 + p * q ^ 3 * v ^ 2 + p * q ^ 2 * u * v ^ 2 -
          p ^ 2 * q * u ^ 2 * v ^ 2 - p * q ^ 2 * u ^ 2 * v ^ 2) * x ^ 4 +
        c (p ^ 2 * q ^ 3 * v ^ 2 - p ^ 2 * q ^ 2 * u ^ 2 * v ^ 2 + 2 * p ^ 2 * q ^ 3 * v ^ 3 +
          p * q ^ 4 * v ^ 3 - 2 * p ^ 2 * q ^ 2 * u ^ 2 * v ^ 3 -
            p * q ^ 3 * u ^ 2 * v ^ 3) * x ^ 5 +
        c (2 * p ^ 2 * q ^ 4 * v ^ 3 - 2 * p ^ 2 * q ^ 3 * u ^ 2 * v ^ 3 + p ^ 2 * q ^ 4 * v ^ 4 -
          p ^ 2 * q ^ 3 * u ^ 2 * v ^ 4) * x ^ 6 +
        c (p ^ 2 * q ^ 5 * v ^ 4 - p ^ 2 * q ^ 4 * u ^ 2 * v ^ 4) * x ^ 7

/-- **Rational generating function for king permutations avoiding $P_2$.** Let $P_2$ be the flat
partially ordered pattern of length $4$ whose second element lies below each of the other three,
and let $A_{P_2}(x; p, q, u, v)$ be the generating function of king permutations avoiding $P_2$,
in which $x$ marks length and $p$, $q$, $u$, $v$ mark ascents, descents, left-to-right maxima and
right-to-left maxima. Then $B \cdot A_{P_2} = A$ in $\mathbb{Z}[p, q, u, v][[x]]$, where
$A = \sum_{k=0}^{6} a_k x^k$ and $B = \sum_{k=0}^{6} b_k x^k$ with $a_0 = b_0 = -1$, $a_1 = -uv$,
$b_1 = 0$, $a_2 = b_2 = pqu + pquv$, $a_3 = p^2quv + pqu^2v + pqu^2v^2$, $b_3 = p^2quv$,
$a_4 = b_4 = p^2q^2uv + p^3qu^2v - p^2q^2u^2v + p^2q^2uv^2$,
$a_5 = p^3q^2u^2v + p^2q^3uv^2 + p^3q^2u^2v^2 - p^2q^2u^3v^2$,
$b_5 = p^3q^2u^2v + p^2q^3uv^2 + p^3q^2u^2v^2$ and $a_6 = b_6 = p^3q^3u^2v^2$. Since $B$ has
constant term $-1$, this determines $A_{P_2} = A / B$.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Theorem 4. -/
theorem_wanted kingFlatPOPBelowGF_one_eq :
    let p : MvPolynomial (Fin 4) ℤ := MvPolynomial.X 0
    let q : MvPolynomial (Fin 4) ℤ := MvPolynomial.X 1
    let u : MvPolynomial (Fin 4) ℤ := MvPolynomial.X 2
    let v : MvPolynomial (Fin 4) ℤ := MvPolynomial.X 3
    let x : PowerSeries (MvPolynomial (Fin 4) ℤ) := PowerSeries.X
    let c : MvPolynomial (Fin 4) ℤ → PowerSeries (MvPolynomial (Fin 4) ℤ) := PowerSeries.C
    (c (-1) + c (p * q * u + p * q * u * v) * x ^ 2 + c (p ^ 2 * q * u * v) * x ^ 3 +
        c (p ^ 2 * q ^ 2 * u * v + p ^ 3 * q * u ^ 2 * v - p ^ 2 * q ^ 2 * u ^ 2 * v +
          p ^ 2 * q ^ 2 * u * v ^ 2) * x ^ 4 +
        c (p ^ 3 * q ^ 2 * u ^ 2 * v + p ^ 2 * q ^ 3 * u * v ^ 2 + p ^ 3 * q ^ 2 * u ^ 2 * v ^ 2) *
          x ^ 5 +
        c (p ^ 3 * q ^ 3 * u ^ 2 * v ^ 2) * x ^ 6) * kingFlatPOPBelowGF 1 =
      c (-1) - c (u * v) * x + c (p * q * u + p * q * u * v) * x ^ 2 +
        c (p ^ 2 * q * u * v + p * q * u ^ 2 * v + p * q * u ^ 2 * v ^ 2) * x ^ 3 +
        c (p ^ 2 * q ^ 2 * u * v + p ^ 3 * q * u ^ 2 * v - p ^ 2 * q ^ 2 * u ^ 2 * v +
          p ^ 2 * q ^ 2 * u * v ^ 2) * x ^ 4 +
        c (p ^ 3 * q ^ 2 * u ^ 2 * v + p ^ 2 * q ^ 3 * u * v ^ 2 + p ^ 3 * q ^ 2 * u ^ 2 * v ^ 2 -
          p ^ 2 * q ^ 2 * u ^ 3 * v ^ 2) * x ^ 5 +
        c (p ^ 3 * q ^ 3 * u ^ 2 * v ^ 2) * x ^ 6

/-- **The generating functions for $P_4$ and $P_1$ differ by a change of variables.** For $k = 1$
and $k = 4$ let $P_k$ be the flat partially ordered pattern of length $4$ whose $k$-th element lies
below each of the other three, and let $A_{P_k}(x; p, q, u, v)$ be the generating function of king
permutations avoiding $P_k$, in which $x$ marks length and $p$, $q$, $u$, $v$ mark ascents,
descents, left-to-right maxima and right-to-left maxima. Then
$A_{P_4}(x; p, q, u, v) = A_{P_1}(x; q, p, v, u)$: the series $A_{P_4}$ is obtained from
$A_{P_1}$ by exchanging $p$ with $q$ and $u$ with $v$ in every coefficient.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Corollary 1. -/
theorem_wanted kingFlatPOPBelowGF_three_eq_rename :
    kingFlatPOPBelowGF 3 =
      PowerSeries.map (MvPolynomial.rename
          ⇑(Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4))).toRingHom
        (kingFlatPOPBelowGF 0)

/-- **The generating functions for $Q_1$ and $P_1$ differ by a change of variables.** Let $P_1$
(respectively $Q_1$) be the flat partially ordered pattern of length $4$ whose first element lies
below (respectively above) each of the other three. Let $A_{P_1}(x; p, q, u, v)$ be the
generating function of king permutations avoiding $P_1$, in which $x$ marks length and $p$, $q$,
$u$, $v$ mark ascents, descents, left-to-right maxima and right-to-left maxima, and let
$\bar A_{Q_1}(x; p, q, s, t)$ be the generating function of king permutations avoiding $Q_1$, in
which $s$ and $t$ mark left-to-right minima and right-to-left minima instead. Then
$\bar A_{Q_1}(x; p, q, s, t) = A_{P_1}(x; q, p, s, t)$: the series $\bar A_{Q_1}$ is obtained
from $A_{P_1}$ by exchanging $p$ with $q$ in every coefficient and writing $s$, $t$ for $u$, $v$.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Corollary 2. -/
theorem_wanted kingFlatPOPAboveGF_zero_eq_rename :
    kingFlatPOPAboveGF 0 =
      PowerSeries.map (MvPolynomial.rename ⇑(Equiv.swap (0 : Fin 4) 1)).toRingHom
        (kingFlatPOPBelowGF 0)

/-- **The king generating function avoiding $Q_4$.** Let $A_{P_1}(x, p, q, u, v)$ be the
generating function of king permutations avoiding the flat pattern $P_1$ (label $1$ below labels
$2, 3, 4$), where $x, p, q, u, v$ mark length, ascents, descents, left-to-right maxima and
right-to-left maxima, and let $\bar A_{Q_4}(x, p, q, s, t)$ be the generating function of king
permutations avoiding the flat pattern $Q_4$ (label $4$ above labels $1, 2, 3$), where
$x, p, q, s, t$ mark length, ascents, descents, left-to-right minima and right-to-left minima.
Then $\bar A_{Q_4}(x, p, q, s, t) = A_{P_1}(x, p, q, t, s)$: the coefficient of each power of $x$
in $\bar A_{Q_4}$ is obtained from the corresponding coefficient of $A_{P_1}$ by exchanging the
last two variables.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Corollary 3. -/
theorem_wanted kingFlatPOPAboveGF_three_eq_rename :
    kingFlatPOPAboveGF 3 =
      PowerSeries.map (MvPolynomial.rename ⇑(Equiv.swap (2 : Fin 4) 3)).toRingHom
        (kingFlatPOPBelowGF 0)

/-- **The generating functions for $P_3$ and $P_2$ differ by a change of variables.** For $k = 2$
and $k = 3$ let $P_k$ be the flat partially ordered pattern of length $4$ whose $k$-th element lies
below each of the other three, and let $A_{P_k}(x; p, q, u, v)$ be the generating function of king
permutations avoiding $P_k$, in which $x$ marks length and $p$, $q$, $u$, $v$ mark ascents,
descents, left-to-right maxima and right-to-left maxima. Then
$A_{P_3}(x; p, q, u, v) = A_{P_2}(x; q, p, v, u)$: the series $A_{P_3}$ is obtained from
$A_{P_2}$ by exchanging $p$ with $q$ and $u$ with $v$ in every coefficient.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Corollary 4. -/
theorem_wanted kingFlatPOPBelowGF_two_eq_rename :
    kingFlatPOPBelowGF 2 =
      PowerSeries.map (MvPolynomial.rename
          ⇑(Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4))).toRingHom
        (kingFlatPOPBelowGF 1)

/-- **The king generating function avoiding $Q_2$.** Let $A_{P_2}(x, p, q, u, v)$ be the
generating function of king permutations avoiding the flat pattern $P_2$ (label $2$ below labels
$1, 3, 4$), where $x, p, q, u, v$ mark length, ascents, descents, left-to-right maxima and
right-to-left maxima, and let $\bar A_{Q_2}(x, p, q, s, t)$ be the generating function of king
permutations avoiding the flat pattern $Q_2$ (label $2$ above labels $1, 3, 4$), where
$x, p, q, s, t$ mark length, ascents, descents, left-to-right minima and right-to-left minima.
Then $\bar A_{Q_2}(x, p, q, s, t) = A_{P_2}(x, q, p, s, t)$: the coefficient of each power of $x$
in $\bar A_{Q_2}$ is obtained from the corresponding coefficient of $A_{P_2}$ by exchanging $p$
and $q$.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Corollary 5. -/
theorem_wanted kingFlatPOPAboveGF_one_eq_rename :
    kingFlatPOPAboveGF 1 =
      PowerSeries.map (MvPolynomial.rename ⇑(Equiv.swap (0 : Fin 4) 1)).toRingHom
        (kingFlatPOPBelowGF 1)

/-- **The king generating function avoiding $Q_3$.** Let $A_{P_2}(x, p, q, u, v)$ be the
generating function of king permutations avoiding the flat pattern $P_2$ (label $2$ below labels
$1, 3, 4$), where $x, p, q, u, v$ mark length, ascents, descents, left-to-right maxima and
right-to-left maxima, and let $\bar A_{Q_3}(x, p, q, s, t)$ be the generating function of king
permutations avoiding the flat pattern $Q_3$ (label $3$ above labels $1, 2, 4$), where
$x, p, q, s, t$ mark length, ascents, descents, left-to-right minima and right-to-left minima.
Then $\bar A_{Q_3}(x, p, q, s, t) = A_{P_2}(x, p, q, t, s)$: the coefficient of each power of $x$
in $\bar A_{Q_3}$ is obtained from the corresponding coefficient of $A_{P_2}$ by exchanging the
last two variables.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Corollary 6. -/
theorem_wanted kingFlatPOPAboveGF_two_eq_rename :
    kingFlatPOPAboveGF 2 =
      PowerSeries.map (MvPolynomial.rename ⇑(Equiv.swap (2 : Fin 4) 3)).toRingHom
        (kingFlatPOPBelowGF 1)

end

end MetaMathlibExt
