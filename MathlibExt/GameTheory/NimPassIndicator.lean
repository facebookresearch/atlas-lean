/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module


public import MathlibExt.GameTheory.ChocolateBarNSProperty
public import Mathlib.Data.Fintype.Basic

/-! # Restricted Nim pass indicator

A coordinate section is either constant one or the indicator of an upper interval.

## References

- Ryohei Miyadera, Hikaru Manabe and Aditi Singh,
  *Generalizations of Two-Dimensional and Three-Dimensional Chocolate Bar Games*,
  INTEGERS 25 (2025), Article G3, pp. 1–29, Lemma 10 (using Lemma 9).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Pass indicator of Nim with a restricted pass.** For $s$ piles with thresholds
$m_0, \dots, m_{s-1}$ and pile sizes $x_0, \dots, x_{s-1}$ (natural numbers), the pass
indicator is $1$ if $m_j \le x_j$ for some pile $j$ (the pass may be used), and $0$ if
$x_j < m_j$ for every pile $j$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 10 and Corollary 2 (the function `F`). -/
public def nimPassIndicator {s : ℕ} (m x : Fin s → ℕ) : ℕ :=
  if ∃ j, m j ≤ x j then 1 else 0

/-- **When a pile reaches its pass threshold.** The pass indicator is one exactly when
at least one pile has reached its threshold. -/
public theorem nimPassIndicator_eq_one_iff {s : ℕ} {m x : Fin s → ℕ} :
    nimPassIndicator m x = 1 ↔ ∃ j, m j ≤ x j := by
  by_cases h : ∃ j, m j ≤ x j <;> simp [nimPassIndicator, h]

/-- **When every pile is below its pass threshold.** The pass indicator is zero exactly when
all piles are strictly below their thresholds. -/
public theorem nimPassIndicator_eq_zero_iff {s : ℕ} {m x : Fin s → ℕ} :
    nimPassIndicator m x = 0 ↔ ∀ j, x j < m j := by
  by_cases h : ∃ j, m j ≤ x j
  · obtain ⟨j, hj⟩ := h
    simp [nimPassIndicator, show ∃ k, m k ≤ x k from ⟨j, hj⟩, show ¬ ∀ k, x k < m k from
      fun hall ↦ (hall j).not_ge hj]
  · have hall : ∀ j, x j < m j := fun j ↦ Nat.lt_of_not_ge (fun hj ↦ h ⟨j, hj⟩)
    simp [nimPassIndicator, h, hall]

/-- **Sections of the Nim pass indicator with the NS property.** Let $s \in \mathbb{N}$ and
$m \in \mathbb{N}^s$ with $m_i > 0$ for every $i < s$, and let $F : \mathbb{N}^s \to \mathbb{N}$ be
the pass indicator of $m$: $F(x) = 1$ if $m_j \le x_j$ for some $j$, and $F(x) = 0$ otherwise.
For $x \in \mathbb{N}^s$, $i < s$ and $t \in \mathbb{N}$ write $x[i \mapsto t]$ for $x$ with its
$i$-th coordinate replaced by $t$. Then the following are equivalent: (a) for all
$x \in \mathbb{N}^s$ and $i < s$, the function $t \mapsto F(x[i \mapsto t])$ has the NS property;
(b) $m_i$ is even for every $i < s$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 10 (`integers-2025-G3-lem-10`). -/
public theorem nimPassIndicator_sections_hasNSProperty_iff {s : ℕ} {m : Fin s → ℕ}
    (hm : ∀ i, 0 < m i) :
    (∀ (x : Fin s → ℕ) i, HasNSProperty fun t ↦ nimPassIndicator m (Function.update x i t)) ↔
      ∀ i, Even (m i) := by
  have section_eq (x : Fin s → ℕ) (i : Fin s) (h : ¬ ∃ j ≠ i, m j ≤ x j) :
      (fun t ↦ nimPassIndicator m (Function.update x i t)) = (Set.Ici (m i)).indicator 1 := by
    funext t
    have hex : (∃ j, m j ≤ Function.update x i t j) ↔ m i ≤ t := by
      constructor
      · rintro ⟨j, hj⟩
        by_cases hji : j = i
        · simpa [hji] using hj
        · exact (h ⟨j, hji, by simpa [Function.update_of_ne hji] using hj⟩).elim
      · intro ht
        exact ⟨i, by simpa using ht⟩
    simp [nimPassIndicator, hex, Set.indicator]
  have threshold_iff (a : ℕ) : HasNSProperty ((Set.Ici a).indicator (1 : ℕ → ℕ)) ↔ Even a := by
    have hmono : Monotone ((Set.Ici a).indicator (1 : ℕ → ℕ)) := by
      intro u v huv
      by_cases hu : a ≤ u
      · simp [Set.indicator, hu, hu.trans huv]
      · simp [Set.indicator, hu]
    have hle (u : ℕ) : (Set.Ici a).indicator (1 : ℕ → ℕ) u ≤ 1 := by
      simp only [Set.indicator, Set.mem_Ici, Pi.one_apply]
      split <;> decide
    have hone : ∃ u, (Set.Ici a).indicator (1 : ℕ → ℕ) u = 1 :=
      ⟨a, by simp [Set.indicator]⟩
    rw [← indicator_Ici_even_iff_hasNSProperty hmono hle hone]
    constructor
    · rintro ⟨b, hb, heq⟩
      have hab : a ≤ b := by
        by_contra h
        simpa [Set.indicator, h] using congrFun heq b
      have hba : b ≤ a := by
        by_contra h
        simpa [Set.indicator, h] using congrFun heq.symm a
      rwa [le_antisymm hba hab] at hb
    · exact fun ha ↦ ⟨a, ha, rfl⟩
  constructor
  · intro h i
    rw [← threshold_iff, ← section_eq (fun _ ↦ 0) i]
    · exact h _ i
    · rintro ⟨j, _, hj⟩
      exact (Nat.not_le.mpr (hm j)) hj
  · intro heven x i
    by_cases h : ∃ j ≠ i, m j ≤ x j
    · obtain ⟨j, hji, hj⟩ := h
      have heq : (fun t ↦ nimPassIndicator m (Function.update x i t)) = fun _ ↦ 1 := by
        funext t
        exact ite_eq_left ⟨j, by simpa [Function.update_of_ne hji] using hj⟩
      rw [heq]
      exact hasNSProperty_const 1
    · rw [section_eq x i h]
      exact (threshold_iff (m i)).mpr (heven i)

end

end MetaMathlibExt
