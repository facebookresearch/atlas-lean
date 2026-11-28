/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Counting base phi representations

We define finite base phi expansions and prove the natural expansion counts of Fibonacci numbers.

A finite binary expansion is represented by the set of positions of its digits equal to one.
Bounds on the value of a Bergman expansion in terms of its occupied positions give uniqueness.
To count natural expansions, we first show that their possible positions form a finite interval
determined by the Bergman expansion. The count of equal-valued words on that interval uses three
carry values. For Fibonacci numbers the Bergman words grow by a block of four digits, which
advances the counts by two steps of the Fibonacci recurrence.
-/

open scoped goldenRatio

namespace MetaMathlibExt

@[expose] public section

/-- **Value of a base phi expansion.** For a finite set $S$ of integers, the base phi value of
$S$ is the real number $\sum_{i \in S} \varphi^i$, where $\varphi = (1 + \sqrt 5)/2$ is the golden
ratio. It is the number represented by the base phi expansion with digit $1$ at each position in
$S$ and digit $0$ at every other position.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1 (definition of a base phi
representation). -/
noncomputable def basePhiValue (S : Finset ℤ) : ℝ :=
  ∑ i ∈ S, φ ^ i

/-- **Bergman expansions.** Encode a finite base phi expansion with digits $0$ and $1$ by the
finite set $S \subseteq \mathbb{Z}$ of positions of its digits $1$. The expansion is a Bergman
expansion when no two digits $1$ are adjacent, that is, $i + 1 \notin S$ for every $i \in S$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1 (Bergman representation). -/
def IsBergmanExpansion (S : Finset ℤ) : Prop :=
  ∀ i ∈ S, i + 1 ∉ S

/-- **Golden mean flips.** Encode a finite base phi expansion with digits $0$ and $1$ by the
finite set of positions of its digits $1$. An expansion $T$ arises from an expansion $S$ by a
golden mean flip $100 \to 011$ when there is a position $i \in S$ with $i - 1 \notin S$ and
$i - 2 \notin S$ such that $T = (S \setminus \{i\}) \cup \{i - 1, i - 2\}$: the digit $1$ at
position $i$ is replaced by digits $1$ at positions $i - 1$ and $i - 2$, which were $0$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Sections 1 and 2 (the map `T_i`). -/
def IsGoldenMeanFlip (S T : Finset ℤ) : Prop :=
  ∃ i ∈ S, i - 1 ∉ S ∧ i - 2 ∉ S ∧ T = insert (i - 1) (insert (i - 2) (S.erase i))

/-- **Knott's truncation rule.** Let $\varphi$ be the golden ratio. Encode a finite base $\varphi$
expansion with digits $0$ and $1$ by the finite set $S \subseteq \mathbb{Z}$ of the positions of
its digits $1$, and write $a_i$ for its digit at position $i$. The expansion satisfies Knott's
condition when it does not end in the digits $0, 1, 1$: if $S$ is nonempty with least element $R$,
then $a_{R+2} a_{R+1} a_R \ne 011$, that is, it is not the case that both $R + 1 \in S$ and
$R + 2 \notin S$. The empty expansion satisfies the condition.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1, Equation (1.1). -/
def SatisfiesKnottCondition (S : Finset ℤ) : Prop :=
  ∀ m ∈ S, (∀ j ∈ S, m ≤ j) → ¬ (m + 1 ∈ S ∧ m + 2 ∉ S)

/-- **Knott expansions.** Let $\varphi$ be the golden ratio and $N$ a natural number. Encode a
finite base phi expansion with digits $0$ and $1$ by the finite set $S \subseteq \mathbb{Z}$ of the
positions of its digits $1$. The Knott expansions of $N$ are the expansions of value $N$ that
satisfy Knott's truncation rule: the set of all such $S$ with $\sum_{i \in S} \varphi^i = N$ that
satisfy Knott's condition.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1. -/
def knottExpansions (N : ℕ) : Set (Finset ℤ) :=
  {S | basePhiValue S = N ∧ SatisfiesKnottCondition S}

/-- **Number of Knott expansions.** For a natural number $N$, $\mathrm{Tot}_\kappa(N)$ is the
number of Knott expansions of $N$ (OEIS A289749).

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1. -/
noncomputable def knottExpansionCount (N : ℕ) : ℕ :=
  (knottExpansions N).ncard

/-- **Natural base phi expansions.** Let $\varphi$ be the golden ratio and $N$ a natural number.
Encode a finite base phi expansion with digits $0$ and $1$ by the finite set
$S \subseteq \mathbb{Z}$ of the positions of its digits $1$. The natural expansions of $N$ are the
Knott expansions $S$ of $N$ for which there is a Bergman expansion $T$ with
$\sum_{i \in T} \varphi^i = N$ whose lowest digit $1$ is at the same position as the lowest
digit $1$ of $S$, that is, $\min T = \min S$, where $S$ and $T$ both empty also counts as
equal.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 4. -/
def naturalExpansions (N : ℕ) : Set (Finset ℤ) :=
  {S | S ∈ knottExpansions N ∧
    ∃ T : Finset ℤ, IsBergmanExpansion T ∧ basePhiValue T = N ∧ T.min = S.min}

/-- **Number of natural expansions.** For a natural number $N$, $\mathrm{Tot}_\nu(N)$ is the
number of natural base phi expansions of $N$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 4. -/
noncomputable def naturalExpansionCount (N : ℕ) : ℕ :=
  (naturalExpansions N).ncard

/-- **Number of Fibonacci representations.** For a natural number $m$,
$\mathrm{Tot}_{\mathrm{FIB}}(m)$ is the number of finite sets $T$ of indices $i \ge 2$ with
$\sum_{i \in T} F_i = m$, where $F_i$ are the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$); that is,
the number of ways to write $m$ as a sum of Fibonacci numbers with distinct indices at least $2$
(OEIS A000119). Indices above $m + 1$ never occur because $F_{m+2} > m$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1 (base Fibonacci representations). -/
def fibonacciRepresentationCount (m : ℕ) : ℕ :=
  ((Finset.Icc 2 (m + 1)).powerset.filter fun T => ∑ i ∈ T, Nat.fib i = m).card

/-- **The empty base phi expansion has value zero.** The base phi value of the empty set of
positions is $0$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1. -/
theorem basePhiValue_empty : basePhiValue ∅ = 0 := by
  simp [basePhiValue]

/-- **The single digit $1$ at position $0$ has value one.** The base phi value of the set $\{0\}$
is $1$, that is, $\varphi^0 = 1$, where $\varphi$ is the golden ratio.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1. -/
theorem basePhiValue_singleton_zero : basePhiValue {0} = 1 := by
  simp [basePhiValue]

/-- **The base phi expansion $10.01$ has value two.** The base phi value of the set $\{1, -2\}$
is $2$, that is, $\varphi + \varphi^{-2} = 2$, where $\varphi$ is the golden ratio.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), proof of Proposition 3.1. -/
theorem basePhiValue_one_neg_two : basePhiValue {1, -2} = 2 := by
  have hinv : φ⁻¹ = φ - 1 := by
    rw [Real.inv_goldenRatio, ← Real.one_sub_goldenConj]; ring
  rw [basePhiValue, Finset.sum_pair (by decide), zpow_one, zpow_neg, zpow_ofNat, ← inv_pow,
    hinv]
  linear_combination Real.goldenRatio_sq

/-- **The base phi expansion $1.11$ has value two.** The base phi value of the set
$\{0, -1, -2\}$ is $2$, that is, $1 + \varphi^{-1} + \varphi^{-2} = 2$, where $\varphi$ is the
golden ratio.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 2. -/
theorem basePhiValue_zero_neg_one_neg_two : basePhiValue {0, -1, -2} = 2 := by
  have hinv : φ⁻¹ = φ - 1 := by
    rw [Real.inv_goldenRatio, ← Real.one_sub_goldenConj]; ring
  rw [basePhiValue, Finset.sum_insert (by decide), Finset.sum_pair (by decide), zpow_zero,
    zpow_neg, zpow_neg, zpow_one, zpow_ofNat, ← inv_pow, hinv]
  linear_combination Real.goldenRatio_sq

/-- **The expansion 10.01 is a Bergman expansion.** The base phi expansion $10.01$, with digits $1$
at positions $1$ and $-2$ and digits $0$ elsewhere, has no two adjacent digits $1$, so it is a
Bergman expansion.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1. -/
theorem isBergmanExpansion_one_neg_two : IsBergmanExpansion {1, -2} := by
  unfold IsBergmanExpansion
  decide

/-- **A golden mean flip from 10.01 to 1.11.** Applying the golden mean flip $100 \to 011$ at the
leading digit of $10.01$ (the digit $1$ at position $1$, followed by digits $0$ at positions $0$
and $-1$) gives $1.11$, the expansion with digits $1$ at positions $0$, $-1$ and $-2$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 2. -/
theorem isGoldenMeanFlip_one_neg_two : IsGoldenMeanFlip {1, -2} {0, -1, -2} :=
  ⟨1, by decide, by decide, by decide, by decide⟩

/-- **A Knott expansion of two.** Let $\varphi$ be the golden ratio. The base $\varphi$ expansion
$1.11$, whose digits $1$ sit at the positions $0$, $-1$ and $-2$, is a Knott expansion of $2$:
its value is $1 + \varphi^{-1} + \varphi^{-2} = 2$ and it satisfies Knott's truncation rule.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1. -/
theorem zero_neg_one_neg_two_mem_knottExpansions : ({0, -1, -2} : Finset ℤ) ∈ knottExpansions 2 :=
  ⟨by rw [basePhiValue_zero_neg_one_neg_two]; norm_num, by unfold SatisfiesKnottCondition; decide⟩

/-- **The expansion 0.11 violates Knott's truncation rule.** The finite base phi expansion
$0.11$, with digits $1$ at positions $-1$ and $-2$ and no others, ends in the digits $011$, so it
does not satisfy Knott's truncation rule.

It represents $1$, since $\varphi^{-1} + \varphi^{-2} = 1$ for the golden ratio $\varphi$, but
is not a Knott expansion of $1$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1, Equation (1.1). -/
theorem not_satisfiesKnottCondition_neg_one_neg_two :
    ¬ SatisfiesKnottCondition {-1, -2} := by
  unfold SatisfiesKnottCondition
  decide

/-- **The expansion 10.01 is a natural expansion of 2.** The finite base phi expansion $10.01$,
with digits $1$ exactly at positions $1$ and $-2$, is a natural base phi expansion of $2$.

It is the Bergman expansion of $2$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 4. -/
theorem one_neg_two_mem_naturalExpansions : ({1, -2} : Finset ℤ) ∈ naturalExpansions 2 :=
  ⟨⟨by rw [basePhiValue_one_neg_two]; norm_num, by unfold SatisfiesKnottCondition; decide⟩,
    {1, -2}, isBergmanExpansion_one_neg_two, by rw [basePhiValue_one_neg_two]; norm_num, rfl⟩

/-- **Small values of the Fibonacci representation count.** Let $F_i$ be the Fibonacci numbers
($F_0 = 0$, $F_1 = 1$), and let $\mathrm{Tot}_{\mathrm{FIB}}(m)$ be the number of ways to write
$m$ as a sum of Fibonacci numbers $F_i$ with distinct indices $i \ge 2$. Then
$\mathrm{Tot}_{\mathrm{FIB}}(0), \dots, \mathrm{Tot}_{\mathrm{FIB}}(8)$ are
$1, 1, 1, 2, 1, 2, 2, 1, 3$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1 (the listed values of `Tot_FIB`). -/
theorem fibonacciRepresentationCount_small :
    (List.range 9).map fibonacciRepresentationCount = [1, 1, 1, 2, 1, 2, 2, 1, 3] := by
  decide

end

namespace BasePhiRepresentations

/-- At every integer position, the sum of two adjacent powers of the golden ratio is the next
power of the golden ratio. -/
public lemma pow_add_prev (i : ℤ) : φ ^ i + φ ^ (i - 1) = φ ^ (i + 1) := by
  rw [show i = (i - 1) + 1 by omega, show i - 1 + 1 - 1 = i - 1 by omega,
    show i - 1 + 1 + 1 = (i - 1) + 2 by omega, zpow_add₀ Real.goldenRatio_ne_zero,
    zpow_add₀ Real.goldenRatio_ne_zero (i - 1) 2, zpow_one, zpow_ofNat, Real.goldenRatio_sq]
  ring

private theorem value_nonneg (S : Finset ℤ) : 0 ≤ basePhiValue S := by
  exact Finset.sum_nonneg fun _ _ => (zpow_pos Real.goldenRatio_pos _).le

private theorem value_insert {S : Finset ℤ} {i : ℤ} (hi : i ∉ S) :
    basePhiValue (insert i S) = φ ^ i + basePhiValue S :=
  Finset.sum_insert hi

-- Spacing one bounds arbitrary binary supports, and spacing two bounds Bergman supports.
private theorem value_lt_of_spacing (S : Finset ℤ) (g : ℤ) (hg : g = 1 ∨ g = 2)
    (hgap : ∀ i ∈ S, ∀ j ∈ S, i < j → i + g ≤ j) (k : ℤ) (hk : ∀ i ∈ S, i < k) :
    basePhiValue S < φ ^ (k + 2 - g) := by
  induction S using Finset.strongInductionOn generalizing k
  rename_i S ih
  by_cases hS : S.Nonempty
  · let m := S.max' hS
    have hm : m ∈ S := Finset.max'_mem _ _
    have hrest := ih (S.erase m) (Finset.erase_ssubset hm)
      (fun i hi j hj hij => hgap i (Finset.mem_of_mem_erase hi) j
        (Finset.mem_of_mem_erase hj) hij) (m + 1 - g) (by
      intro i hi
      have hiS := Finset.mem_of_mem_erase hi
      have him : i < m :=
        lt_of_le_of_ne (Finset.le_max' S i hiS) (Finset.ne_of_mem_erase hi)
      have := hgap i hiS m hm him
      omega)
    have heq : basePhiValue S = φ ^ m + basePhiValue (S.erase m) := by
      rw [← value_insert (Finset.notMem_erase m S), Finset.insert_erase hm]
    have hm' := hk m hm
    rw [heq]
    rcases hg with rfl | rfl
    · have h₁ : m + 1 - 1 + 2 - 1 = m + 1 := by omega
      rw [h₁] at hrest
      calc
        _ < φ ^ (m + 1) + φ ^ m := by linarith
        _ = φ ^ (m + 2) := by
          simpa only [show m + 1 - 1 = m by omega, show m + 1 + 1 = m + 2 by omega]
            using pow_add_prev (m + 1)
        _ ≤ _ := zpow_le_zpow_right₀ Real.one_lt_goldenRatio.le (by omega)
    · have h₂ : m + 1 - 2 + 2 - 2 = m - 1 := by omega
      rw [h₂] at hrest
      calc
        _ < φ ^ m + φ ^ (m - 1) := by linarith
        _ = φ ^ (m + 1) := pow_add_prev m
        _ ≤ _ := zpow_le_zpow_right₀ Real.one_lt_goldenRatio.le (by omega)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, basePhiValue_empty]
    exact zpow_pos Real.goldenRatio_pos _

/-- If every occupied position of a Bergman expansion is below `k`, its value is strictly
less than the golden ratio raised to `k`. -/
public lemma bergman_value_lt {S : Finset ℤ} (hS : IsBergmanExpansion S)
    {k : ℤ} (hk : ∀ i ∈ S, i < k) : basePhiValue S < φ ^ k := by
  simpa using value_lt_of_spacing S 2 (Or.inr rfl) (by
    intro i hi j hj hij
    have hn := hS i hi
    by_contra! h
    obtain rfl : j = i + 1 := by omega
    exact hn hj) k hk

private theorem value_lt {S : Finset ℤ} {k : ℤ} (hk : ∀ i ∈ S, i < k) :
    basePhiValue S < φ ^ (k + 1) := by
  simpa only [show k + 2 - 1 = k + 1 by omega] using
    value_lt_of_spacing S 1 (Or.inl rfl) (fun _ _ _ _ h => by omega) k hk

/-- The contribution of any occupied position is at most the value of the whole expansion. -/
public lemma value_pow_le_of_mem {S : Finset ℤ} {i : ℤ} (hi : i ∈ S) :
    φ ^ i ≤ basePhiValue S :=
  Finset.single_le_sum (fun j _ => (zpow_pos Real.goldenRatio_pos j).le) hi

/-- Two finite Bergman expansions with the same base phi value have identical occupied positions.
See *Counting Base Phi Representations*, Section 1, for Bergman expansions and uniqueness. -/
public lemma bergman_eq_of_value_eq {S T : Finset ℤ}
    (hS : IsBergmanExpansion S) (hT : IsBergmanExpansion T)
    (hval : basePhiValue S = basePhiValue T) : S = T := by
  classical
  by_contra hne
  let D := (S \ T) ∪ (T \ S)
  have hD : D.Nonempty := by
    by_contra h
    apply hne
    ext i
    have hni : i ∉ D := fun hi => h ⟨i, hi⟩
    simp only [D, Finset.mem_union, Finset.mem_sdiff] at hni
    tauto
  let k := D.max' hD
  have hk : k ∈ D := Finset.max'_mem _ _
  have hdiff : basePhiValue (S \ T) = basePhiValue (T \ S) := by
    have hs := Finset.sum_sdiff (s₁ := S ∩ T) (s₂ := S) (f := fun i : ℤ => φ ^ i)
      Finset.inter_subset_left
    have ht := Finset.sum_sdiff (s₁ := S ∩ T) (s₂ := T) (f := fun i : ℤ => φ ^ i)
      Finset.inter_subset_right
    rw [Finset.sdiff_inter_self_left] at hs
    rw [Finset.sdiff_inter_self_right] at ht
    unfold basePhiValue at *
    linarith
  have impossible {A B : Finset ℤ} (hAB : A ∪ B = D)
      (hA : k ∈ A) (hB : k ∉ B) (hBerg : IsBergmanExpansion B)
      (hval : basePhiValue A = basePhiValue B) : False := by
    have hlt := bergman_value_lt hBerg (k := k) (by
      intro i hi
      have hle := Finset.le_max' D i (hAB ▸ Finset.mem_union_right A hi)
      exact lt_of_le_of_ne hle fun h => hB (h ▸ hi))
    exact hlt.not_ge (hval ▸ value_pow_le_of_mem hA)
  rcases Finset.mem_union.mp hk with h | h
  · exact impossible rfl h (fun h' => (Finset.mem_sdiff.mp h').2 (Finset.mem_sdiff.mp h).1)
      (fun i hi hj => hT i (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1) hdiff
  · exact impossible (Finset.union_comm ..) h
      (fun h' => (Finset.mem_sdiff.mp h').2 (Finset.mem_sdiff.mp h).1)
      (fun i hi hj => hS i (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1) hdiff.symm

end BasePhiRepresentations

open BasePhiRepresentations

namespace naturalExpansionCount_fib

-- Collapsing 011 to 100 decreases the cardinality and preserves the lower bound.
private theorem carry {S : Finset ℤ} {i : ℤ} (hi : i ∈ S)
    (hp : i - 1 ∈ S) (hn : i + 1 ∉ S) :
    basePhiValue (insert (i + 1) ((S.erase i).erase (i - 1))) = basePhiValue S := by
  have hp' : i - 1 ∈ S.erase i := Finset.mem_erase.mpr ⟨by omega, hp⟩
  have h₁ := value_insert (Finset.notMem_erase i S)
  rw [Finset.insert_erase hi] at h₁
  have h₂ := value_insert (Finset.notMem_erase (i - 1) (S.erase i))
  rw [Finset.insert_erase hp'] at h₂
  rw [value_insert (fun h => hn (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)))]
  linarith [pow_add_prev i]

-- The chain runs from the normalized expansion back to the original support.
private theorem exists_bergman_above (R : ℤ) (S : Finset ℤ) (hS : ∀ i ∈ S, R ≤ i) :
    ∃ T, IsBergmanExpansion T ∧ basePhiValue T = basePhiValue S ∧
      (∀ i ∈ T, R ≤ i) ∧ Relation.ReflTransGen IsGoldenMeanFlip T S := by
  classical
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | ind n ih =>
    by_cases hB : IsBergmanExpansion S
    · exact ⟨S, hB, rfl, hS, .refl⟩
    · let A := S.filter (fun i => i - 1 ∈ S)
      have hA : A.Nonempty := by
        unfold IsBergmanExpansion at hB
        push Not at hB
        obtain ⟨i, hi, hj⟩ := hB
        exact ⟨i + 1, Finset.mem_filter.mpr ⟨hj, by simpa using hi⟩⟩
      let i := A.max' hA
      obtain ⟨hi, hp⟩ : i ∈ S ∧ i - 1 ∈ S :=
        Finset.mem_filter.mp (Finset.max'_mem _ _)
      have hn : i + 1 ∉ S := by
        intro hh
        have hle := Finset.le_max' A (i + 1)
          (Finset.mem_filter.mpr ⟨hh, by simpa using hi⟩)
        change i + 1 ≤ i at hle
        omega
      let U := insert (i + 1) ((S.erase i).erase (i - 1))
      have hfresh : i + 1 ∉ (S.erase i).erase (i - 1) :=
        fun h => hn (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
      have hp' : i - 1 ∈ S.erase i := Finset.mem_erase.mpr ⟨by omega, hp⟩
      have hu : U.card < n := by
        have h₁ := Finset.card_erase_add_one hi
        have h₂ := Finset.card_erase_add_one hp'
        simp only [U, Finset.card_insert_of_notMem hfresh]
        omega
      obtain ⟨T, hT, hval, habove, hchain⟩ := ih U.card hu U (by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · have := hS i hi
          omega
        · exact hS j (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj))) rfl
      have hflip : IsGoldenMeanFlip U S := by
        refine ⟨i + 1, Finset.mem_insert_self _ _, ?_, ?_, ?_⟩
        · simp [U, Finset.mem_erase, show i ≠ i + 1 by omega]
        · simp [U, Finset.mem_erase, show i + 1 - 2 = i - 1 by omega,
            show i - 1 ≠ i + 1 by omega]
        · simp only [show i + 1 - 1 = i by omega, show i + 1 - 2 = i - 1 by omega,
            U, Finset.erase_insert hfresh, Finset.insert_erase hp', Finset.insert_erase hi]
      exact ⟨T, hT, hval.trans (carry hi hp hn), habove, hchain.tail hflip⟩

private theorem min_mem_of_bergman {S T : Finset ℤ} {R : ℤ}
    (hT : IsBergmanExpansion T) (hR : R ∈ T)
    (hv : basePhiValue S = basePhiValue T) (hS : ∀ i ∈ S, R ≤ i) : R ∈ S := by
  by_contra hn
  obtain ⟨U, hU, hval, hUmin, _⟩ := exists_bergman_above (R + 1) S (by
    intro i hi
    have := hS i hi
    have hne : i ≠ R := fun h => hn (h ▸ hi)
    omega)
  have heq := bergman_eq_of_value_eq hU hT (hval.trans hv)
  have := hUmin R (heq.symm ▸ hR)
  omega

private theorem knott_of_bergman {S T : Finset ℤ} {R : ℤ}
    (hT : IsBergmanExpansion T) (hR : R ∈ T)
    (hv : basePhiValue S = basePhiValue T) (hS : ∀ i ∈ S, R ≤ i) :
    SatisfiesKnottCondition S := by
  have hRS := min_mem_of_bergman hT hR hv hS
  intro m hm hmin hbad
  have heq : m = R := le_antisymm (hmin R hRS) (hS m hm)
  subst m
  obtain ⟨hp, hn⟩ := hbad
  let U := insert (R + 1 + 1) ((S.erase (R + 1)).erase R)
  have hUV : basePhiValue U = basePhiValue T := by
    have h := carry (i := R + 1) hp (by simpa using hm)
      (by simpa [add_assoc] using hn)
    simpa only [U, add_sub_cancel_right] using h.trans hv
  have hU : ∀ i ∈ U, R ≤ i := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · omega
    · exact hS i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
  have hRU := min_mem_of_bergman hT hR hUV hU
  rcases Finset.mem_insert.mp hRU with h | h
  · omega
  · exact Finset.notMem_erase _ _ h

private noncomputable def slice (R : ℤ) (n : ℕ) (x : ℝ) : Finset (Finset ℤ) :=
  ((Finset.Ico R (R + n)).powerset).filter (fun S => basePhiValue S = x)

private theorem mem_slice {R : ℤ} {n : ℕ} {x : ℝ} {S : Finset ℤ} :
    S ∈ slice R n x ↔ (∀ i ∈ S, R ≤ i ∧ i < R + n) ∧ basePhiValue S = x := by
  classical
  simp only [slice, Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff, Finset.mem_Ico]

private theorem slice_card_succ (R : ℤ) (n : ℕ) (x : ℝ) :
    (slice R (n + 1) x).card =
      (slice R n x).card + (slice R n (x - φ ^ (R + n : ℤ))).card := by
  classical
  let k : ℤ := R + n
  have hnot {S : Finset ℤ} {y : ℝ} (hS : S ∈ slice R n y) : k ∉ S :=
    fun h => lt_irrefl _ ((mem_slice.mp hS).1 k h).2
  have hsplit : slice R (n + 1) x =
      slice R n x ∪ (slice R n (x - φ ^ k)).image (insert k) := by
    ext S
    simp only [Finset.mem_union, Finset.mem_image]
    constructor
    · intro h
      obtain ⟨hS, hval⟩ := mem_slice.mp h
      by_cases hk : k ∈ S
      · have hv := value_insert (Finset.notMem_erase k S)
        rw [Finset.insert_erase hk, hval] at hv
        refine Or.inr ⟨S.erase k, mem_slice.mpr ⟨?_, by linarith⟩, Finset.insert_erase hk⟩
        intro i hi
        obtain ⟨hl, hu⟩ := hS i (Finset.mem_of_mem_erase hi)
        have hne := Finset.ne_of_mem_erase hi
        exact ⟨hl, by dsimp [k] at hne; omega⟩
      · refine Or.inl (mem_slice.mpr ⟨?_, hval⟩)
        intro i hi
        obtain ⟨hl, hu⟩ := hS i hi
        have hne : i ≠ k := fun he => hk (he ▸ hi)
        exact ⟨hl, by dsimp [k] at hne; omega⟩
    · rintro (h | ⟨T, hT, rfl⟩)
      · obtain ⟨hS, hval⟩ := mem_slice.mp h
        refine mem_slice.mpr ⟨fun i hi => ?_, hval⟩
        obtain ⟨hl, hu⟩ := hS i hi
        exact ⟨hl, by omega⟩
      · obtain ⟨hS, hval⟩ := mem_slice.mp hT
        refine mem_slice.mpr ⟨?_, by rw [value_insert (hnot hT), hval]; ring⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · dsimp [k]
          omega
        · obtain ⟨hl, hu⟩ := hS i hi
          exact ⟨hl, by omega⟩
  rw [hsplit, Finset.card_union_of_disjoint, Finset.card_image_of_injOn]
  · intro S hS T hT he
    simpa [Finset.erase_insert (hnot hS), Finset.erase_insert (hnot hT)] using
      congrArg (fun U : Finset ℤ => U.erase k) he
  · exact Finset.disjoint_left.mpr fun S hS h => by
      obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp h
      exact hnot hS (Finset.mem_insert_self _ _)

-- Words are written most significant digit first, with leading zeros allowed.
private def positions (R : ℤ) : List Bool → Finset ℤ
  | [] => ∅
  | a :: w => if a then insert (R + w.length) (positions R w) else positions R w

private theorem positions_bounds (R : ℤ) (w : List Bool) :
    ∀ i ∈ positions R w, R ≤ i ∧ i < R + w.length := by
  induction w with
  | nil => simp [positions]
  | cons a w ih =>
    cases a <;> simp only [positions, Bool.false_eq_true, ↓reduceIte, List.length_cons]
    · intro i hi
      obtain ⟨hl, hu⟩ := ih i hi
      exact ⟨hl, by omega⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · omega
      · obtain ⟨hl, hu⟩ := ih i hi
        exact ⟨hl, by omega⟩

private theorem top_notMem (R : ℤ) (w : List Bool) : R + w.length ∉ positions R w :=
  fun h => lt_irrefl _ (positions_bounds R w _ h).2

private def digit (a : Bool) : ℝ := if a then 1 else 0

private theorem value_cons (R : ℤ) (a : Bool) (w : List Bool) :
    basePhiValue (positions R (a :: w)) =
      basePhiValue (positions R w) + digit a * φ ^ (R + w.length : ℤ) := by
  cases a <;> simp [positions, digit, value_insert (top_notMem R w), add_comm]

-- The carry is measured in units of the power just above the remaining word.
private noncomputable def count (R : ℤ) (w : List Bool) (c : ℝ) : ℕ :=
  (slice R w.length (basePhiValue (positions R w) + c * φ ^ (R + w.length : ℤ))).card

private theorem count_nil (R : ℤ) (c : ℝ) : count R [] c = if c = 0 then 1 else 0 := by
  classical
  simp [count, slice, positions, basePhiValue_empty, Finset.filter_singleton,
    zpow_ne_zero _ Real.goldenRatio_ne_zero]
  split <;> simp

private theorem count_cons (R : ℤ) (w : List Bool) (a : Bool) (c : ℝ) :
    count R (a :: w) c = count R w (φ * c + digit a) + count R w (φ * c + digit a - 1) := by
  simp only [count, List.length_cons, value_cons, slice_card_succ]
  rw [show (R + (w.length + 1 : ℕ) : ℤ) = R + w.length + 1 by omega,
    zpow_add_one₀ Real.goldenRatio_ne_zero]
  congr 2 <;> ring_nf

private theorem count_eq_zero_of_ge (R : ℤ) (w : List Bool) {c : ℝ} (hc : φ ≤ c) :
    count R w c = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  obtain ⟨hb, hv⟩ := mem_slice.mp hS
  have hlu := value_lt (fun i hi => (hb i hi).2)
  rw [zpow_add_one₀ Real.goldenRatio_ne_zero, hv] at hlu
  have hmul := mul_le_mul_of_nonneg_right hc
    (zpow_pos Real.goldenRatio_pos (R + w.length : ℤ)).le
  linarith [value_nonneg (positions R w)]

private theorem count_neg_one (R : ℤ) (w : List Bool)
    (hB : IsBergmanExpansion (positions R w)) : count R w (-1) = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  have hv := (mem_slice.mp hS).2
  have hlt := bergman_value_lt hB (fun i hi => (positions_bounds R w i hi).2)
  linarith [value_nonneg S]

private theorem count_zero (R : ℤ) (w : List Bool)
    (hB : IsBergmanExpansion (positions R w)) :
    count R (false :: w) 0 = count R w 0 ∧
      count R (false :: w) 1 = count R w (φ - 1) ∧
      count R (false :: w) (φ - 1) = count R w 1 + count R w 0 := by
  have hφ : φ * (φ - 1) = 1 := by nlinarith only [Real.goldenRatio_sq]
  simp [count_cons, digit, hφ, count_neg_one R w hB, count_eq_zero_of_ge R w le_rfl]

private theorem count_one (R : ℤ) (w : List Bool) :
    count R (true :: w) 0 = count R w 0 + count R w 1 ∧
      count R (true :: w) 1 = 0 ∧
      count R (true :: w) (φ - 1) = count R w 1 := by
  have hφ : φ * (φ - 1) = 1 := by nlinarith only [Real.goldenRatio_sq]
  have h₁ : φ ≤ φ + 1 := by linarith
  rw [count_cons, count_cons, count_cons]
  simp only [digit, ↓reduceIte, mul_zero, zero_add, sub_self, mul_one, hφ, add_sub_cancel_right]
  rw [show (1 : ℝ) + 1 = 2 by norm_num, count_eq_zero_of_ge R w h₁,
    count_eq_zero_of_ge R w le_rfl, count_eq_zero_of_ge R w Real.goldenRatio_lt_two.le]
  simp [add_comm]

private theorem min_eq_of_mem_of_le {S : Finset ℤ} {R : ℤ}
    (hR : R ∈ S) (hmin : ∀ i ∈ S, R ≤ i) : S.min = (R : WithTop ℤ) :=
  le_antisymm (Finset.min_le hR) (Finset.le_min fun i hi => WithTop.coe_le_coe.mpr (hmin i hi))

private theorem naturalExpansionCount_eq_count (R : ℤ) (w : List Bool) (N : ℕ)
    (hB : IsBergmanExpansion (positions R w)) (hR : R ∈ positions R w)
    (hv : basePhiValue (positions R w) = N) : naturalExpansionCount N = count R w 0 := by
  classical
  rw [naturalExpansionCount, count, zero_mul, add_zero, hv, ← Set.ncard_coe_finset]
  apply congrArg Set.ncard
  ext S
  change S ∈ naturalExpansions N ↔ S ∈ slice R w.length N
  have hmin := min_eq_of_mem_of_le hR (fun i hi => (positions_bounds R w i hi).1)
  constructor
  · rintro ⟨⟨hval, _⟩, T, hT, hTV, hTS⟩
    have hTm := bergman_eq_of_value_eq hT hB (hTV.trans hv.symm)
    have hSmin : S.min = (R : WithTop ℤ) := hTS.symm.trans (hTm.symm ▸ hmin)
    refine mem_slice.mpr ⟨fun i hi => ⟨Finset.min_le_of_eq hi hSmin, ?_⟩, hval⟩
    have hSP := value_pow_le_of_mem hi
    have hlt := bergman_value_lt hB (fun i hi => (positions_bounds R w i hi).2)
    rw [hval, ← hv] at hSP
    exact (zpow_lt_zpow_iff_right₀ Real.one_lt_goldenRatio).mp (hSP.trans_lt hlt)
  · intro hS
    obtain ⟨hb, hval⟩ := mem_slice.mp hS
    have habove : ∀ i ∈ S, R ≤ i := fun i hi => (hb i hi).1
    have hval' := hval.trans hv.symm
    have hSR := min_mem_of_bergman hB hR hval' habove
    exact ⟨⟨hval, knott_of_bergman hB hR hval' habove⟩, positions R w, hB, hv,
      hmin.trans (min_eq_of_mem_of_le hSR habove).symm⟩

private def block (w : List Bool) : List Bool := true :: false :: false :: false :: w

private def fibWord (odd : Bool) : ℕ → List Bool
  | 0 => if odd then [true, false, false, true] else [true]
  | n + 1 => block (fibWord odd n)

private theorem positions_block (R : ℤ) (w : List Bool) :
    positions R (block w) = insert (R + (w.length + 3 : ℕ)) (positions R w) := by
  simp only [block, positions, ↓reduceIte, List.length_cons]
  congr 2

private theorem bergman_insert_above {S : Finset ℤ} {k : ℤ} (hB : IsBergmanExpansion S)
    (hk : ∀ i ∈ S, i + 1 < k) : IsBergmanExpansion (insert k S) := by
  intro i hi hj
  rcases Finset.mem_insert.mp hi with rfl | hi <;>
    rcases Finset.mem_insert.mp hj with hj | hj
  · omega
  · have := hk _ hj
    omega
  · exact (hk _ hi).ne hj
  · exact hB i hi hj

private theorem fibWord_bergman (R : ℤ) (odd : Bool) (n : ℕ) :
    IsBergmanExpansion (positions R (fibWord odd n)) := by
  induction n with
  | zero =>
    cases odd
    · simp [fibWord, positions, IsBergmanExpansion]
    · change IsBergmanExpansion (insert (R + (3 : ℕ)) (insert (R + (0 : ℕ)) ∅))
      apply bergman_insert_above
      · simp [IsBergmanExpansion]
      · simp
  | succ n ih =>
    rw [fibWord, positions_block]
    apply bergman_insert_above ih
    intro i hi
    have := (positions_bounds R (fibWord odd n) i hi).2
    omega

private theorem fibWord_min_mem (R : ℤ) (odd : Bool) (n : ℕ) :
    R ∈ positions R (fibWord odd n) := by
  induction n with
  | zero => cases odd <;> simp [fibWord, positions]
  | succ n ih =>
    rw [fibWord, positions_block]
    exact Finset.mem_insert_of_mem ih

private theorem value_block (R : ℤ) (w : List Bool) :
    basePhiValue (positions R (block w)) =
      φ ^ (R + (w.length + 3 : ℕ) : ℤ) + basePhiValue (positions R w) := by
  rw [positions_block, value_insert]
  intro hi
  have := (positions_bounds R w _ hi).2
  omega

-- Reading the block 1000 changes the two relevant counts from (a, c) to (2a+c, a+c).
private theorem count_block (R : ℤ) (w : List Bool)
    (hB : IsBergmanExpansion (positions R w)) :
    count R (block w) 0 = 2 * count R w 0 + count R w (φ - 1) ∧
      count R (block w) (φ - 1) = count R w 0 + count R w (φ - 1) := by
  obtain ⟨z₀, _, z₂⟩ := count_zero R w hB
  obtain ⟨z₀', _, z₂'⟩ := count_zero R (false :: w) hB
  obtain ⟨z₀'', z₁'', _⟩ := count_zero R (false :: false :: w) hB
  obtain ⟨o₀, _, o₂⟩ := count_one R (false :: false :: false :: w)
  unfold block
  constructor
  · rw [o₀, z₀'', z₀', z₀, z₁'', z₂', (count_zero R w hB).2.1, z₀]
    omega
  · rw [o₂, z₁'', z₂', (count_zero R w hB).2.1, z₀]
    omega

private theorem count_fibWord (R : ℤ) (odd : Bool) (n : ℕ) :
    count R (fibWord odd n) 0 = Nat.fib (2 * n + (if odd then 2 else 0) + 1) ∧
      count R (fibWord odd n) (φ - 1) = Nat.fib (2 * n + (if odd then 2 else 0)) := by
  induction n with
  | zero =>
    have h0 : count R [] 0 = 1 := by simp [count_nil]
    have h1 : count R [] 1 = 0 := by simp [count_nil]
    obtain ⟨o₀, o₁, o₂⟩ := count_one R []
    have hB : IsBergmanExpansion (positions R [true]) := fibWord_bergman R false 0
    obtain ⟨z₀, z₁, z₂⟩ := count_zero R [true] hB
    obtain ⟨z₀', z₁', _⟩ := count_zero R [false, true] hB
    obtain ⟨o₀', _, o₂'⟩ := count_one R [false, false, true]
    cases odd
    · simp [fibWord, o₀, o₂, h0, h1]
    · simp [fibWord, o₀', o₂', z₀', z₀, z₁', z₂, o₀, o₁, h0, h1, Nat.fib]
  | succ n ih =>
    let k := 2 * n + (if odd then 2 else 0)
    change count R (fibWord odd n) 0 = Nat.fib (k + 1) ∧
      count R (fibWord odd n) (φ - 1) = Nat.fib k at ih
    rw [fibWord]
    obtain ⟨h₀, h₂⟩ := count_block R (fibWord odd n) (fibWord_bergman R odd n)
    rw [h₀, h₂, ih.1, ih.2]
    have hk : 2 * (n + 1) + (if odd then 2 else 0) = k + 2 := by unfold k; omega
    rw [hk, Nat.fib_add_two (n := k + 1), Nat.fib_add_two (n := k)]
    omega

private theorem fib_step (m : ℕ) :
    (Nat.fib (m + 2) : ℝ) = φ ^ m + φ ^ (-2 : ℤ) * (Nat.fib m : ℝ) := by
  have h : φ ^ (-2 : ℤ) = ψ + 1 := by
    rw [zpow_neg, zpow_ofNat, ← inv_pow, Real.inv_goldenRatio, neg_sq, Real.goldenConj_sq]
  rw [h, Nat.fib_add_two, Nat.cast_add]
  have hfib := Real.fib_succ_sub_goldenConj_mul_fib m
  linear_combination hfib

private theorem fibWord_length (odd : Bool) (n : ℕ) :
    (fibWord odd n).length = 4 * n + (if odd then 4 else 1) := by
  induction n with
  | zero => cases odd <;> rfl
  | succ n ih =>
    simp only [fibWord, block, List.length_cons, ih]
    omega

private theorem value_fibWord (R : ℤ) (odd : Bool) (n : ℕ) :
    basePhiValue (positions R (fibWord odd n)) =
      φ ^ (R + 2 * (n : ℤ) + (if odd then 2 else 0)) *
        (Nat.fib (2 * n + (if odd then 3 else 2)) : ℝ) := by
  induction n with
  | zero =>
    cases odd
    · simp [fibWord, Nat.fib, positions, basePhiValue]
    · have h1 := pow_add_prev (R + 1)
      have h2 := pow_add_prev (R + 2)
      rw [show R + 1 - 1 = R by omega, show R + 1 + 1 = R + 2 by omega] at h1
      rw [show R + 2 - 1 = R + 1 by omega, show R + 2 + 1 = R + 3 by omega] at h2
      change basePhiValue (insert (R + (3 : ℕ)) (insert (R + (0 : ℕ)) ∅)) = _
      rw [value_insert (by simp), value_insert (Finset.notMem_empty _)]
      norm_num [Nat.fib, basePhiValue_empty]
      linarith
  | succ n ih =>
    let m := 2 * n + (if odd then 3 else 2)
    let e : ℤ := R + 2 * (n : ℤ) + (if odd then 2 else 0)
    change basePhiValue (positions R (fibWord odd n)) = φ ^ e * (Nat.fib m : ℝ) at ih
    have hm : 2 * (n + 1) + (if odd then 3 else 2) = m + 2 := by unfold m; omega
    have he : R + 2 * (↑(n + 1) : ℤ) + (if odd then 2 else 0) = e + 2 := by unfold e; omega
    have hlen : R + ((fibWord odd n).length + 3 : ℕ) = e + 2 + (m : ℤ) := by
      rw [fibWord_length]
      cases odd <;> simp [m, e] <;> omega
    rw [fibWord, value_block, ih, hm, he, hlen, fib_step, zpow_add₀ Real.goldenRatio_ne_zero,
      zpow_natCast, mul_add]
    have hc : φ ^ (e + 2) * φ ^ (-2 : ℤ) = φ ^ e := by
      rw [← zpow_add₀ Real.goldenRatio_ne_zero, show e + 2 + -2 = e by omega]
    rw [← mul_assoc, hc]

end naturalExpansionCount_fib

/-- **Golden mean flips connect all expansions to the Bergman expansion.** Let $N$ be a natural
number, let $S$ be a Bergman expansion of $N$ and let $T$ be any finite base phi expansion of
$N$ with digits $0$ and $1$. Then $T$ is obtained from $S$ by finitely many (possibly zero)
golden mean flips $100 \to 011$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 2.1
(`fq-2024-dekking11102023-thm-2.1`). -/
public theorem reflTransGen_isGoldenMeanFlip_of_isBergmanExpansion (N : ℕ)
    {S T : Finset ℤ} (hS : IsBergmanExpansion S) (hSN : basePhiValue S = N)
    (hTN : basePhiValue T = N) :
    Relation.ReflTransGen IsGoldenMeanFlip S T := by
  open naturalExpansionCount_fib in
  obtain ⟨R, hR⟩ := T.finite_toSet.bddBelow
  obtain ⟨U, hU, hval, _, hchain⟩ := exists_bergman_above R T (fun _ hi => hR hi)
  have hUS := bergman_eq_of_value_eq hU hS (hval.trans (hTN.trans hSN.symm))
  exact hUS ▸ hchain

/-- **Natural expansions of Fibonacci numbers.** Write $\mathrm{Tot}_\nu(N)$ for the number of
natural base phi expansions of a natural number $N$ and $F_k$ for the $k$-th Fibonacci number.
Then for every $n \ge 0$, $\mathrm{Tot}_\nu(F_{2n+2}) = F_{2n+1}$ and
$\mathrm{Tot}_\nu(F_{2n+3}) = F_{2n+3}$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 4.3
(`fq-2024-dekking11102023-thm-4.3`). -/
public theorem naturalExpansionCount_fib (n : ℕ) :
    naturalExpansionCount (Nat.fib (2 * n + 2)) = Nat.fib (2 * n + 1) ∧
      naturalExpansionCount (Nat.fib (2 * n + 3)) = Nat.fib (2 * n + 3) := by
  open naturalExpansionCount_fib in
  constructor
  · let R : ℤ := -(2 * (n : ℤ))
    have hv : basePhiValue (positions R (fibWord false n)) = Nat.fib (2 * n + 2) := by
      simpa [R] using value_fibWord R false n
    rw [naturalExpansionCount_eq_count R _ _ (fibWord_bergman R false n)
      (fibWord_min_mem R false n) hv]
    simpa using (count_fibWord R false n).1
  · let R : ℤ := -(2 * (n : ℤ) + 2)
    have hv : basePhiValue (positions R (fibWord true n)) = Nat.fib (2 * n + 3) := by
      simpa [R] using value_fibWord R true n
    rw [naturalExpansionCount_eq_count R _ _ (fibWord_bergman R true n)
      (fibWord_min_mem R true n) hv]
    simpa only [Bool.true_eq, ↓reduceIte, Nat.add_assoc] using (count_fibWord R true n).1

end MetaMathlibExt
