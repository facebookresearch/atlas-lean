/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.Coset.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination

/-!
# Cosets and weighted zero sums of pairs

A singleton cannot sum to zero with a unit weight. When both positions are used, the
ratio of the two weights belongs to the subgroup and gives the coset relation.
-/

namespace MetaMathlibExt

/-- **Weighted zero-sum free pairs in a field.** Let $F$ be a field, let $A$ be a subgroup of the
multiplicative group $F^*$, and let $x, y \in F$ be nonzero. Then the sequence
$(x_1, x_2) = (x, y)$ has no $A$-weighted zero-sum subsequence, that is, there is no nonempty
set $I \subseteq \{1, 2\}$ with elements $a_i \in A$ for $i \in I$ such that
$\sum_{i \in I} a_i x_i = 0$, if and only if $x$ and $-y$ lie in different cosets of $A$ in $F^*$.

A zero term is by itself a zero-sum subsequence, so the cosets are taken for nonzero $x$ and $y$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 7.6 (`integers-2024-A38-lem-7-6`). -/
public theorem pair_no_weightedZeroSum_iff {F : Type*} [Field F] (A : Subgroup Fˣ)
    {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    (¬ ∃ I : Finset (Fin 2), I.Nonempty ∧ ∃ a : Fin 2 → F,
      (∀ i ∈ I, a i ∈ ((↑) : Fˣ → F) '' A) ∧ ∑ i ∈ I, a i * ![x, y] i = 0) ↔
      (QuotientGroup.mk (Units.mk0 x hx) : Fˣ ⧸ A) ≠
        QuotientGroup.mk (Units.mk0 (-y) (neg_ne_zero.mpr hy)) := by
  let u := Units.mk0 x hx
  let v := Units.mk0 (-y) (neg_ne_zero.mpr hy)
  apply not_congr
  change (∃ I : Finset (Fin 2), I.Nonempty ∧ ∃ a : Fin 2 → F,
      (∀ i ∈ I, a i ∈ ((↑) : Fˣ → F) '' A) ∧ ∑ i ∈ I, a i * ![x, y] i = 0) ↔
    (u : Fˣ ⧸ A) = v
  rw [QuotientGroup.eq]
  constructor
  · rintro ⟨I, hI, a, ha, hsum⟩
    have hne (i) (hi : i ∈ I) : a i ≠ 0 := by
      obtain ⟨w, _, hw⟩ := ha i hi
      rw [← hw]
      exact Units.ne_zero w
    by_cases h0 : (0 : Fin 2) ∈ I
    · by_cases h1 : (1 : Fin 2) ∈ I
      · have hfull : I = Finset.univ := by
          ext i
          fin_cases i <;> simp [h0, h1]
        obtain ⟨w₀, hw₀, hval₀⟩ := ha 0 h0
        obtain ⟨w₁, hw₁, hval₁⟩ := ha 1 h1
        have hsum' : (w₀ : F) * x + (w₁ : F) * y = 0 := by
          simpa [hfull, Fin.sum_univ_two, hval₀, hval₁] using hsum
        have heq : w₀ * u = w₁ * v := Units.ext (by
          change (w₀ : F) * x = (w₁ : F) * -y
          linear_combination hsum')
        have hratio : u⁻¹ * v = w₁⁻¹ * w₀ := by
          calc
            _ = (w₁ * u)⁻¹ * (w₁ * v) := by group
            _ = (w₁ * u)⁻¹ * (w₀ * u) := by rw [heq]
            _ = _ := by rw [mul_comm w₁ u, mul_comm w₀ u]; group
        rw [hratio]
        exact A.mul_mem (A.inv_mem hw₁) hw₀
      · have hone : I = {0} := by
          ext i
          fin_cases i <;> simp [h0, h1]
        exact (mul_ne_zero (hne 0 h0) hx (by simpa [hone] using hsum)).elim
    · have h1 : (1 : Fin 2) ∈ I := by
        obtain ⟨i, hi⟩ := hI
        fin_cases i
        · exact (h0 hi).elim
        · exact hi
      have hone : I = {1} := by
        ext i
        fin_cases i <;> simp [h0, h1]
      exact (mul_ne_zero (hne 1 h1) hy (by simpa [hone] using hsum)).elim
  · intro hw
    let w := u⁻¹ * v
    refine ⟨Finset.univ, ⟨0, Finset.mem_univ _⟩, ![(w : F), 1], ?_, ?_⟩
    · intro i _
      fin_cases i
      · exact ⟨w, hw, rfl⟩
      · exact ⟨1, A.one_mem, rfl⟩
    · have hwu : w * u = v := by
        dsimp [w]
        rw [mul_comm (u⁻¹ * v) u, ← mul_assoc, mul_inv_cancel, one_mul]
      have hval := congrArg (fun z : Fˣ => (z : F)) hwu
      change (w : F) * x = -y at hval
      simp [Fin.sum_univ_two, hval]

end MetaMathlibExt
