/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Order.Hom.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.PermutationStatistics
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Complement symmetry for flat patterns in king permutations

Complementing values maps king permutations avoiding the flat pattern $P_2$ to those avoiding
its complement $Q_2$. It swaps ascents and descents and takes maxima to minima on the same side.
-/

namespace MetaMathlibExt

@[expose] public section

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

private def complement {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  σ.trans Fin.revPerm

private theorem complement_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    complement σ i < complement σ j ↔ σ j < σ i :=
  Fin.rev_lt_rev

private theorem complement_involutive {n : ℕ} :
    Function.Involutive (complement (n := n)) := by
  intro σ
  apply Equiv.ext
  intro i
  exact Fin.rev_rev (σ i)

private theorem rev_succ_iff {n : ℕ} (i j : Fin n) :
    (i.rev : ℕ) + 1 = j.rev ↔ (j : ℕ) + 1 = i := by
  simp only [Fin.val_rev]
  have hi := i.isLt
  have hj := j.isLt
  omega

private theorem isKingPerm_complement {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    IsKingPerm (complement σ) ↔ IsKingPerm σ := by
  simp only [IsKingPerm, complement, Equiv.trans_apply, Fin.revPerm_apply, ne_eq, rev_succ_iff,
    and_comm]

private theorem containsFlatPOPAbove_complement {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : Fin 4) :
    ContainsFlatPOPAbove (complement σ) j ↔ ContainsFlatPOPBelow σ j := by
  simp only [ContainsFlatPOPAbove, ContainsFlatPOPBelow, complement_lt]

private theorem permAscentCount_complement {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permAscentCount (complement σ) = permDescentCount σ := by
  simp only [permAscentCount, permDescentCount, complement_lt]

private theorem permDescentCount_complement {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permDescentCount (complement σ) = permAscentCount σ := by
  simp only [permDescentCount, permAscentCount, complement_lt]

private theorem permLeftToRightMinCount_complement {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permLeftToRightMinCount (complement σ) = permLeftToRightMaxCount σ := by
  simp only [permLeftToRightMinCount, permLeftToRightMaxCount, complement_lt]

private theorem permRightToLeftMinCount_complement {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permRightToLeftMinCount (complement σ) = permRightToLeftMaxCount σ := by
  simp only [permRightToLeftMinCount, permRightToLeftMaxCount, complement_lt]

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
theorem kingFlatPOPAboveGF_one_eq_rename :
    kingFlatPOPAboveGF 1 =
      PowerSeries.map (MvPolynomial.rename ⇑(Equiv.swap (0 : Fin 4) 1)).toRingHom
        (kingFlatPOPBelowGF 1) := by
  classical
  apply PowerSeries.ext
  intro n
  simp only [kingFlatPOPAboveGF, kingFlatPOPBelowGF, PowerSeries.coeff_map, PowerSeries.coeff_mk,
    map_sum]
  -- The same position embedding witnesses the complementary pattern.
  symm
  let e : Equiv.Perm (Equiv.Perm (Fin n)) :=
    ⟨complement, complement, complement_involutive, complement_involutive⟩
  refine Finset.sum_equiv e ?_ ?_
  · intro σ
    change _ ↔ complement σ ∈ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, isKingPerm_complement,
      containsFlatPOPAbove_complement]
  · intro σ _
    have h₂ : Equiv.swap (0 : Fin 4) 1 2 = 2 := by decide
    have h₃ : Equiv.swap (0 : Fin 4) 1 3 = 3 := by decide
    change _ = MvPolynomial.X 0 ^ permAscentCount (complement σ) *
      MvPolynomial.X 1 ^ permDescentCount (complement σ) *
      MvPolynomial.X 2 ^ permLeftToRightMinCount (complement σ) *
      MvPolynomial.X 3 ^ permRightToLeftMinCount (complement σ)
    have rename_X (i : Fin 4) :
        (MvPolynomial.rename ⇑(Equiv.swap (0 : Fin 4) 1)).toRingHom (MvPolynomial.X i) =
          (MvPolynomial.X (Equiv.swap 0 1 i) : MvPolynomial (Fin 4) ℤ) :=
      MvPolynomial.rename_X _ _
    simp only [map_mul, map_pow, rename_X,
      Equiv.swap_apply_left, Equiv.swap_apply_right, h₂, h₃,
      permAscentCount_complement, permDescentCount_complement,
      permLeftToRightMinCount_complement, permRightToLeftMinCount_complement]
    rw [mul_comm (MvPolynomial.X 1 ^ permAscentCount σ)]


end

end MetaMathlibExt
