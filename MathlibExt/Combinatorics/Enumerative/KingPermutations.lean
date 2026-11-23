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

/-!
# King permutations avoiding flat patterns

Reversing both positions and values identifies king permutations avoiding a flat pattern with
a unique minimum and those avoiding the reflected pattern with a unique maximum.
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

namespace kingFlatPOPAboveGF_three_eq_rename

variable {n : ℕ}

-- Conjugating by reversal reverses both the positions and the values of a permutation.
private abbrev reverseComplement : Equiv.Perm (Equiv.Perm (Fin n)) := Fin.revPerm.permCongr

private theorem rev_adjacent (i j : Fin n) :
    i.rev.val + 1 = j.rev.val ↔ j.val + 1 = i.val := by
  have := i.isLt
  have := j.isLt
  simp only [Fin.val_rev]
  omega

private theorem king_reverseComplement {σ : Equiv.Perm (Fin n)} (h : IsKingPerm σ) :
    IsKingPerm (reverseComplement σ) := by
  intro i j hij
  obtain ⟨h₁, h₂⟩ := h j.rev i.rev ((rev_adjacent j i).2 hij.symm).symm
  exact ⟨fun he => h₁ ((rev_adjacent _ _).1 he), fun he => h₂ ((rev_adjacent _ _).1 he)⟩

private def reversePositions (f : Fin 4 ↪o Fin n) : Fin 4 ↪o Fin n :=
  OrderEmbedding.ofStrictMono (fun i => (f i.rev).rev)
    fun _ _ hij => Fin.rev_lt_rev.mpr (f.strictMono (Fin.rev_lt_rev.mpr hij))

private theorem contains_reverseComplement (σ : Equiv.Perm (Fin n)) (j : Fin 4) :
    ContainsFlatPOPAbove (reverseComplement σ) j.rev ↔ ContainsFlatPOPBelow σ j := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨reversePositions f, fun m hm =>
      Fin.rev_lt_rev.mp (hf m.rev (Fin.rev_injective.ne hm))⟩
  · rintro ⟨f, hf⟩
    refine ⟨reversePositions f, fun m hm => ?_⟩
    apply Fin.rev_lt_rev.mpr
    change σ (f j.rev.rev).rev.rev < σ (f m.rev).rev.rev
    simpa only [Fin.rev_rev] using hf m.rev (Fin.rev_ne_iff.mpr hm)

-- Index adjacent pairs by their left endpoint in Fin n, omitting the final position.
private theorem card_adjacent (r : Fin (n + 1) → Fin (n + 1) → Prop) [DecidableRel r] :
    (Finset.univ.filter fun i => ∃ j, j.val = i.val + 1 ∧ r i j).card =
      (Finset.univ.filter fun i : Fin n => r i.castSucc i.succ).card := by
  have h (i : Fin n) : (∃ j, j.val = i.castSucc.val + 1 ∧ r i.castSucc j) ↔
      r i.castSucc i.succ := by
    constructor
    · rintro ⟨j, hj, h⟩
      exact (Fin.ext hj : j = i.succ) ▸ h
    · exact fun h => ⟨_, rfl, h⟩
  have hlast : ¬ ∃ j, j.val = (Fin.last n).val + 1 ∧ r (Fin.last n) j := by
    rintro ⟨j, hj, _⟩
    exact j.isLt.ne (by simpa using hj)
  simp only [Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  simp only [h, hlast, ite_false, add_zero]

private theorem card_adjacent_rev (r : Fin n → Fin n → Prop) [DecidableRel r] :
    (Finset.univ.filter fun i : Fin n => ∃ j : Fin n, j.val = i.val + 1 ∧ r j.rev i.rev).card =
      (Finset.univ.filter fun i => ∃ j, j.val = i.val + 1 ∧ r i j).card := by
  cases n with
  | zero => simp
  | succ n =>
    rw [card_adjacent (fun i j => r j.rev i.rev), card_adjacent r]
    apply Finset.card_equiv Fin.revPerm
    simp [Fin.rev_succ, Fin.rev_castSucc]

private theorem ascent_reverseComplement (σ : Equiv.Perm (Fin n)) :
    permAscentCount (reverseComplement σ) = permAscentCount σ := by
  simpa only [permAscentCount, reverseComplement, Equiv.permCongr_apply, Fin.revPerm_symm,
    Fin.revPerm_apply, Fin.rev_lt_rev] using card_adjacent_rev (fun i j => σ i < σ j)

private theorem descent_reverseComplement (σ : Equiv.Perm (Fin n)) :
    permDescentCount (reverseComplement σ) = permDescentCount σ := by
  simpa only [permDescentCount, reverseComplement, Equiv.permCongr_apply, Fin.revPerm_symm,
    Fin.revPerm_apply, Fin.rev_lt_rev] using card_adjacent_rev (fun i j => σ j < σ i)

private theorem leftMin_reverseComplement (σ : Equiv.Perm (Fin n)) :
    permLeftToRightMinCount (reverseComplement σ) = permRightToLeftMaxCount σ := by
  apply Finset.card_equiv Fin.revPerm
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.revPerm_apply]
  rw [Fin.rev_surjective.forall]
  simp [reverseComplement, Fin.rev_lt_iff]

private theorem rightMin_reverseComplement (σ : Equiv.Perm (Fin n)) :
    permRightToLeftMinCount (reverseComplement σ) = permLeftToRightMaxCount σ := by
  apply Finset.card_equiv Fin.revPerm
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.revPerm_apply]
  rw [Fin.rev_surjective.forall]
  simp [reverseComplement, Fin.lt_rev_iff]

end kingFlatPOPAboveGF_three_eq_rename

open kingFlatPOPAboveGF_three_eq_rename in
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
theorem kingFlatPOPAboveGF_three_eq_rename :
    kingFlatPOPAboveGF 3 =
      PowerSeries.map (MvPolynomial.rename ⇑(Equiv.swap (2 : Fin 4) 3)).toRingHom
        (kingFlatPOPBelowGF 0) := by
  classical
  apply PowerSeries.ext
  intro n
  simp only [kingFlatPOPAboveGF, kingFlatPOPBelowGF, PowerSeries.coeff_map, PowerSeries.coeff_mk,
    map_sum]
  symm
  apply Finset.sum_equiv reverseComplement
  · intro σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hking : IsKingPerm σ ↔ IsKingPerm (reverseComplement σ) :=
      ⟨king_reverseComplement, fun h =>
        (Fin.revPerm.permCongr.symm_apply_apply σ) ▸ king_reverseComplement h⟩
    exact hking.and ((contains_reverseComplement σ 0).not.symm)
  · intro σ _
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_mul, map_pow,
      MvPolynomial.rename_X, ascent_reverseComplement, descent_reverseComplement,
      leftMin_reverseComplement, rightMin_reverseComplement]
    rw [Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 3),
      Equiv.swap_apply_of_ne_of_ne (by decide : (1 : Fin 4) ≠ 2) (by decide : (1 : Fin 4) ≠ 3),
      Equiv.swap_apply_left, Equiv.swap_apply_right]
    ac_rfl

end

end MetaMathlibExt
