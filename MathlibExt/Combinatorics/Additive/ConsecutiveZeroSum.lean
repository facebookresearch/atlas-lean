/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Consecutive zero sums in finite abelian groups

Two equal prefix sums delimit a consecutive block with sum zero. Conversely, taking successive
differences of distinct group elements gives a sequence in which every nonempty block has
nonzero sum.
-/

namespace MetaMathlibExt

/-- **Consecutive zero-sum constant of a finite abelian group.** Let $G$ be a finite abelian
group and let $C(G)$ be the least positive integer $k$ such that every sequence
$x_1, \dots, x_k$ in $G$ has a block of consecutive terms $x_s, \dots, x_t$ with $s \le t$ and
$x_s + \dots + x_t = 0$. Then $C(G) = |G|$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 3.1 (`integers-2024-A38-thm-3-1`). -/
public theorem consecutive_constant_eq_card (G : Type*) [AddCommGroup G] [Fintype G] :
    IsLeast {k : ℕ | 0 < k ∧ ∀ x : Fin k → G, ∃ s t : Fin k, s ≤ t ∧
      ∃ a : Fin k → ℤ, (∀ i ∈ Finset.Icc s t, a i ∈ ({1} : Set ℤ)) ∧
        ∑ i ∈ Finset.Icc s t, a i • x i = 0} (Fintype.card G) := by
  constructor
  · refine ⟨Fintype.card_pos, fun x => ?_⟩
    obtain ⟨i, j, hij, heq⟩ : ∃ i j, i < j ∧ Fin.partialSum x i = Fin.partialSum x j := by
      obtain ⟨i, j, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (Fin.partialSum x) (by simp)
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨i, j, h, heq⟩
      · exact ⟨j, i, h, heq.symm⟩
    obtain ⟨s, rfl⟩ := Fin.exists_castSucc_eq.mpr (hij.trans_le (Fin.le_last j)).ne
    obtain ⟨t, rfl⟩ := Fin.exists_succ_eq.mpr ((Fin.zero_le s.castSucc).trans_lt hij).ne'
    have hst := Fin.castSucc_lt_succ_iff.mp hij
    refine ⟨s, t, hst, fun _ => 1, fun _ _ => rfl, ?_⟩
    simpa [Fin.partialSum_succ] using
      (Fin.sum_Icc_sub hst (Fin.partialSum x)).trans (sub_eq_zero.mpr heq.symm)
  · rintro k ⟨_, hk⟩
    by_contra! hlt
    obtain ⟨f⟩ : Nonempty (Fin (k + 1) ↪ G) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hlt)
    obtain ⟨s, t, hst, a, ha, hsum⟩ := hk (fun i => f i.succ - f i.castSucc)
    have heq : f t.succ - f s.castSucc = 0 := calc
      _ = ∑ i ∈ Finset.Icc s t, (f i.succ - f i.castSucc) := (Fin.sum_Icc_sub hst f).symm
      _ = ∑ i ∈ Finset.Icc s t, a i • (f i.succ - f i.castSucc) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [show a i = 1 from ha i hi, one_zsmul]
      _ = 0 := hsum
    exact (Fin.castSucc_lt_succ_iff.mpr hst).ne (f.injective (sub_eq_zero.mp heq).symm)

end MetaMathlibExt
