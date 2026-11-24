/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.Shuffle
public import MathlibExt.AlgebraicTopology.SimplexCategory.EdgePullback
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Shuffle surjections and permutation edge coordinates

Increasing positions in two blocks determine their
rank surjections and complementary tensor edge words.
The formulas include zero-length blocks. The ordinal
laws require no ring structure; word products use
a multiplicative type with one.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped Simplicial

namespace AlgebraicTopology.EilenbergZilber

variable {p q : ℕ}

/-- Card step for `Fin`-valued filters. -/
private theorem filter_card_step {N : ℕ} (L : Finset (Fin N)) (k : Fin N) :
    (L.filter (fun x => x.val < k.val + 1)).card =
      (L.filter (fun x => x.val < k.val)).card + (if k ∈ L then 1 else 0) := by
  have hiff : ∀ x : Fin N, (x.val < k.val + 1) ↔ (x.val < k.val ∨ x = k) := by
    intro x
    constructor
    · intro h
      by_cases hx : x = k
      · exact Or.inr hx
      · exact Or.inl (by
          have hne : x.val ≠ k.val := fun heq => hx (Fin.ext heq)
          omega)
    · rintro (h | rfl)
      · omega
      · exact Nat.lt_succ_self _
  have hfilter : L.filter (fun x => x.val < k.val + 1)
      = L.filter (fun x => x.val < k.val) ∪ (if k ∈ L then {k} else ∅) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_union, hiff]
    by_cases hx : x = k <;> by_cases hk : k ∈ L <;> simp [hx, hk]
  have hdisj : Disjoint (L.filter (fun x => x.val < k.val))
      (if k ∈ L then {k} else ∅) := by
    by_cases hk : k ∈ L <;> simp [hk]
  rw [hfilter, Finset.card_union_of_disjoint hdisj]
  by_cases hk : k ∈ L <;> simp [hk]

/-- Successor step of `leftHom` detects left positions. -/
theorem leftHom_step (s : Shuffle p q) (k : Fin (p + q)) :
    (s.leftHom.toOrderHom k.succ).val
      = (s.leftHom.toOrderHom k.castSucc).val
        + (if k ∈ s.leftPositions.val then 1 else 0) := by
  rw [Shuffle.leftHom_val_eq_card_filter_leftPositions,
    Shuffle.leftHom_val_eq_card_filter_leftPositions,
    Fin.val_succ, Fin.val_castSucc]
  exact filter_card_step _ _

/-- Successor step of `rightHom` detects right positions. -/
theorem rightHom_step (s : Shuffle p q) (k : Fin (p + q)) :
    (s.rightHom.toOrderHom k.succ).val
      = (s.rightHom.toOrderHom k.castSucc).val
        + (if k ∈ s.rightPositions.val then 1 else 0) := by
  rw [Shuffle.rightHom_val_eq_card_filter_rightPositions,
    Shuffle.rightHom_val_eq_card_filter_rightPositions,
    Fin.val_succ, Fin.val_castSucc]
  exact filter_card_step _ _

theorem leftHom_zero (s : Shuffle p q) : s.leftHom.toOrderHom 0 = 0 := by
  apply Fin.ext
  rw [Shuffle.leftHom_val_eq_card_filter_leftPositions]
  simp

theorem leftHom_last (s : Shuffle p q) :
    s.leftHom.toOrderHom (Fin.last _) = Fin.last _ := by
  apply Fin.ext
  rw [Shuffle.leftHom_val_eq_card_filter_leftPositions, Fin.val_last, Fin.val_last]
  have hfilter : s.leftPositions.val.filter (fun x : Fin (p + q) => x.val < p + q)
      = s.leftPositions.val := by
    apply Finset.filter_true_of_mem
    intro x _
    exact x.isLt
  rw [hfilter, s.leftPositions.property]

theorem rightHom_zero (s : Shuffle p q) : s.rightHom.toOrderHom 0 = 0 := by
  apply Fin.ext
  rw [Shuffle.rightHom_val_eq_card_filter_rightPositions]
  simp

theorem rightHom_last (s : Shuffle p q) :
    s.rightHom.toOrderHom (Fin.last _) = Fin.last _ := by
  apply Fin.ext
  rw [Shuffle.rightHom_val_eq_card_filter_rightPositions, Fin.val_last, Fin.val_last]
  have hfilter : s.rightPositions.val.filter (fun x : Fin (p + q) => x.val < p + q)
      = s.rightPositions.val := by
    apply Finset.filter_true_of_mem
    intro x _
    exact x.isLt
  rw [hfilter, s.rightPositions.property]


namespace Shuffle

/-- The native shuffle structure and literal increasing-permutation subtype have the same index. -/
def equivPermutationSubtype :
    Shuffle p q ≃ {σ : Equiv.Perm (Fin (p + q)) // IsShuffle σ} where
  toFun s := ⟨s.perm, s.isShuffle⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv s := by cases s; rfl
  right_inv s := by cases s; rfl

/-- The native left rank at an original left-block position is its original index. -/
theorem leftHom_leftPosition (s : Shuffle p q) (i : Fin p) :
    (s.leftHom.toOrderHom (s.perm (Fin.castAdd q i)).castSucc).val = i.val := by
  classical
  rw [leftHom_val_eq_card_filter_leftPositions, leftPositions,
    Set.powersetCard.val_ofFinEmb, Finset.filter_map, Finset.card_map]
  have hfilter : Finset.univ.filter (fun j : Fin p =>
      (s.perm (Fin.castAdd q j)).val < (s.perm (Fin.castAdd q i)).val) =
        Finset.Iio i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    exact s.isShuffle.1.lt_iff_lt
  change (Finset.univ.filter (fun j : Fin p =>
    (s.perm (Fin.castAdd q j)).val < (s.perm (Fin.castAdd q i)).val)).card = i.val
  rw [hfilter, Fin.card_Iio]

/-- The native right rank at an original right-block position is its original index. -/
theorem rightHom_rightPosition (s : Shuffle p q) (i : Fin q) :
    (s.rightHom.toOrderHom (s.perm (Fin.natAdd p i)).castSucc).val = i.val := by
  classical
  rw [rightHom_val_eq_card_filter_rightPositions, rightPositions,
    Set.powersetCard.val_ofFinEmb, Finset.filter_map, Finset.card_map]
  have hfilter : Finset.univ.filter (fun j : Fin q =>
      (s.perm (Fin.natAdd p j)).val < (s.perm (Fin.natAdd p i)).val) =
        Finset.Iio i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    exact s.isShuffle.2.lt_iff_lt
  change (Finset.univ.filter (fun j : Fin q =>
    (s.perm (Fin.natAdd p j)).val < (s.perm (Fin.natAdd p i)).val)).card = i.val
  rw [hfilter, Fin.card_Iio]

/-- The left simplex map reaches every left-block ordinal vertex. -/
theorem leftHom_surjective (s : Shuffle p q) :
    Function.Surjective s.leftHom.toOrderHom := by
  intro i
  by_cases hi : i.val < p
  · let j : Fin p := ⟨i.val, hi⟩
    refine ⟨(s.perm (Fin.castAdd q j)).castSucc, ?_⟩
    apply Fin.ext
    exact leftHom_leftPosition s j
  · refine ⟨Fin.last (p + q), ?_⟩
    rw [leftHom_last]
    apply Fin.ext
    have hbound : i.val < p + 1 := i.isLt
    change p = i.val
    omega

/-- The right simplex map reaches every right-block ordinal vertex. -/
theorem rightHom_surjective (s : Shuffle p q) :
    Function.Surjective s.rightHom.toOrderHom := by
  intro i
  by_cases hi : i.val < q
  · let j : Fin q := ⟨i.val, hi⟩
    refine ⟨(s.perm (Fin.natAdd p j)).castSucc, ?_⟩
    apply Fin.ext
    exact rightHom_rightPosition s j
  · refine ⟨Fin.last (p + q), ?_⟩
    rw [rightHom_last]
    apply Fin.ext
    have hbound : i.val < q + 1 := i.isLt
    change q = i.val
    omega

/-- Left shuffle maps earn their epimorphism instance from the rank map. -/
instance leftHom_epi (s : Shuffle p q) : Epi s.leftHom :=
  SimplexCategory.epi_iff_surjective.mpr (leftHom_surjective s)

/-- Right shuffle maps earn their epimorphism instance from the rank map. -/
instance rightHom_epi (s : Shuffle p q) : Epi s.rightHom :=
  SimplexCategory.epi_iff_surjective.mpr (rightHom_surjective s)

/-- The two complementary edge pullbacks recover the original word at σ⁻¹. -/
theorem pullbackEdges_mul {A : Type*} [MulOneClass A] (s : Shuffle p q)
    (a : Fin p → A) (b : Fin q → A) :
    (fun i => SimplexCategory.pullbackEdges s.leftHom a i *
      SimplexCategory.pullbackEdges s.rightHom b i) =
        (fun i => Fin.append a b (s.perm.symm i)) := by
  classical
  funext i
  obtain ⟨j, rfl⟩ := s.perm.surjective i
  obtain ⟨j, rfl⟩ := (_root_.finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)).surjective j
  rcases j with j | j
  · simp only [_root_.finSumFinEquiv_apply_left, Equiv.symm_apply_apply,
      Fin.append_left]
    have hmem : s.perm (Fin.castAdd q j) ∈ s.leftPositions.val :=
      (mem_leftPositions_iff s _).mpr ⟨j, rfl⟩
    have hnmem : s.perm (Fin.castAdd q j) ∉ s.rightPositions.val := by
      change s.perm (Fin.castAdd q j) ∉ s.rightPositions
      intro hright
      exact ((mem_rightPositions_iff_not_mem_leftPositions s _).mp hright) hmem
    have hl : s.leftHom.toOrderHom (s.perm (Fin.castAdd q j)).castSucc <
        s.leftHom.toOrderHom (s.perm (Fin.castAdd q j)).succ := by
      have hs := leftHom_step s (s.perm (Fin.castAdd q j))
      rw [ite_eq_left hmem] at hs
      exact Fin.lt_def.mpr (by omega)
    have hr : ¬s.rightHom.toOrderHom (s.perm (Fin.castAdd q j)).castSucc <
        s.rightHom.toOrderHom (s.perm (Fin.castAdd q j)).succ := by
      have hs := rightHom_step s (s.perm (Fin.castAdd q j))
      rw [ite_eq_right hnmem] at hs
      exact Fin.not_lt.mpr (Fin.le_iff_val_le_val.mpr (by omega))
    simp only [SimplexCategory.pullbackEdges, dite_eq_left hl, dite_eq_right hr, mul_one]
    congr 1
    apply Fin.ext
    exact leftHom_leftPosition s j
  · simp only [_root_.finSumFinEquiv_apply_right, Equiv.symm_apply_apply,
      Fin.append_right]
    have hmem : s.perm (Fin.natAdd p j) ∈ s.rightPositions.val :=
      (mem_rightPositions_iff s _).mpr ⟨j, rfl⟩
    have hnmem : s.perm (Fin.natAdd p j) ∉ s.leftPositions.val :=
      (mem_rightPositions_iff_not_mem_leftPositions s _).mp hmem
    have hl : ¬s.leftHom.toOrderHom (s.perm (Fin.natAdd p j)).castSucc <
        s.leftHom.toOrderHom (s.perm (Fin.natAdd p j)).succ := by
      have hs := leftHom_step s (s.perm (Fin.natAdd p j))
      rw [ite_eq_right hnmem] at hs
      exact Fin.not_lt.mpr (Fin.le_iff_val_le_val.mpr (by omega))
    have hr : s.rightHom.toOrderHom (s.perm (Fin.natAdd p j)).castSucc <
        s.rightHom.toOrderHom (s.perm (Fin.natAdd p j)).succ := by
      have hs := rightHom_step s (s.perm (Fin.natAdd p j))
      rw [ite_eq_left hmem] at hs
      exact Fin.lt_def.mpr (by omega)
    simp only [SimplexCategory.pullbackEdges, dite_eq_right hl, dite_eq_left hr, one_mul]
    congr 1
    apply Fin.ext
    exact rightHom_rightPosition s j

end Shuffle

end AlgebraicTopology.EilenbergZilber
