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
# Rank surjections and edge coordinates of ordered shuffles

An ordered (p, q)-shuffle is a permutation σ of p + q positions which is increasing on each
original block. Its left positions are σ(0), …, σ(p − 1); its right positions are their
complement. Counting these positions before each vertex defines surjections ⦋p + q⦌ → ⦋p⦌ and
⦋p + q⦌ → ⦋q⦌.

A rank increases exactly on an edge belonging to its block, and its value at the position of
an original block element is that element's block index. The two complementary edge-coordinate
maps, multiplied left factor first, reconstruct the concatenated word at σ⁻¹. This coordinate
formula requires only multiplication with a two-sided unit and includes zero-length blocks.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped Simplicial

namespace AlgebraicTopology.EilenbergZilber

variable {p q : ℕ}

/-- For N : ℕ, a finite subset L of Fin N and k : Fin N, the cardinality of {x ∈ L | x.val < k.val
+ 1} is the cardinality of {x ∈ L | x.val < k.val} plus 1 if k ∈ L and plus 0 otherwise. -/
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

/-- For p, q : ℕ and an ordered (p, q)-shuffle s, let L be its set of left positions and ℓ : Fin
(p + q + 1) → Fin (p + 1) its left rank map. For every edge k : Fin (p + q), ℓ(k.succ).val =
ℓ(k.castSucc).val + (if k ∈ L then 1 else 0). -/
theorem leftHom_step (s : Shuffle p q) (k : Fin (p + q)) :
    (s.leftHom.toOrderHom k.succ).val
      = (s.leftHom.toOrderHom k.castSucc).val
        + (if k ∈ s.leftPositions.val then 1 else 0) := by
  rw [Shuffle.leftHom_val_eq_card_filter_leftPositions,
    Shuffle.leftHom_val_eq_card_filter_leftPositions,
    Fin.val_succ, Fin.val_castSucc]
  exact filter_card_step _ _

/-- For p, q : ℕ and an ordered (p, q)-shuffle s, let R be its set of right positions and r : Fin
(p + q + 1) → Fin (q + 1) its right rank map. For every edge k : Fin (p + q), r(k.succ).val =
r(k.castSucc).val + (if k ∈ R then 1 else 0). -/
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

/-- For p, q : ℕ, Shuffle p q is equivalent to the subtype of permutations σ of Fin (p + q) whose
restrictions i ↦ σ(Fin.castAdd q i) and j ↦ σ(Fin.natAdd p j) are strictly increasing. The
forward map returns s.perm with its IsShuffle proof, and the inverse packages that same
permutation. -/
def equivPermutationSubtype :
    Shuffle p q ≃ {σ : Equiv.Perm (Fin (p + q)) // IsShuffle σ} where
  toFun s := ⟨s.perm, s.isShuffle⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv s := by cases s; rfl
  right_inv s := by cases s; rfl

/-- For p, q : ℕ and an ordered (p, q)-shuffle s, and i : Fin p, the left rank at the vertex
(s.perm (Fin.castAdd q i)).castSucc has value i.val. Equivalently, exactly i.val left
positions precede the shuffled position of the i-th original left element. -/
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

/-- For p, q : ℕ and an ordered (p, q)-shuffle s, and i : Fin q, the right rank at the vertex
(s.perm (Fin.natAdd p i)).castSucc has value i.val. Thus exactly i.val right positions precede
that original right element's shuffled position. -/
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

/-- For p, q : ℕ and an ordered (p, q)-shuffle s, the order-preserving vertex map s.leftHom : ⦋p +
q⦌ ⟶ ⦋p⦌ is surjective as a function Fin (p + q + 1) → Fin (p + 1). The ranks before left
positions give vertices 0 through p − 1, and the final vertex maps to p; this also covers p =
0. -/
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

/-- For p, q : ℕ and an ordered (p, q)-shuffle s, the order-preserving vertex map s.rightHom : ⦋p
+ q⦌ ⟶ ⦋q⦌ is surjective as a function Fin (p + q + 1) → Fin (q + 1). The ranks before right
positions give vertices 0 through q − 1, and the final vertex maps to q, including q = 0. -/
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

/-- For p, q : ℕ and an ordered (p, q)-shuffle s, the morphism s.leftHom : ⦋p + q⦌ ⟶ ⦋p⦌ is an
epimorphism in the simplex category. Its underlying function on ordinal vertices is the
surjective left rank map. -/
instance leftHom_epi (s : Shuffle p q) : Epi s.leftHom :=
  SimplexCategory.epi_iff_surjective.mpr (leftHom_surjective s)

/-- For p, q : ℕ and an ordered (p, q)-shuffle s, the morphism s.rightHom : ⦋p + q⦌ ⟶ ⦋q⦌ is an
epimorphism in the simplex category because its underlying right rank function is surjective. -/
instance rightHom_epi (s : Shuffle p q) : Epi s.rightHom :=
  SimplexCategory.epi_iff_surjective.mpr (rightHom_surjective s)

/-- Let A be a type with multiplication and a two-sided unit, let s be an ordered (p, q)-shuffle
with permutation σ, and let a : Fin p → A and b : Fin q → A be words. For each i : Fin (p +
q), pullbackEdges s.leftHom a i * pullbackEdges s.rightHom b i = Fin.append a b (σ.symm i).
The factor from the block not occupying i is 1, so the multiplication order is left pullback
followed by right pullback. -/
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
