/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Combinatorics.Perm.ShuffleFactorization
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.Shuffle

/-!
# Genuine sorting fibers of native shuffle products

A global labeling is split along the actual two increasing value blocks of
a native shuffle. The native lexicographic sorting criterion identifies
when the global sort rank makes the original permutation a shuffle. The
unique original shuffle/block factorization then gives inverse
fiber maps for the two sides of shuffle multiplicativity. The empty-block
and empty-alphabet cases are part of the original finite types.
-/

@[expose] public section
noncomputable section

namespace Equiv.Perm

open AlgebraicTopology.EilenbergZilber

/-- The original sorted label graph with its exact stable tie order. -/
def sortedLabelGraph {n m : ℕ} (f : Fin n → Fin m) : Fin n → Fin m ×ₗ Fin n :=
  fun i => toLex (f (Tuple.sort f i), Tuple.sort f i)

/-- The original native sorting criterion gives the strictly ordered graph. -/
theorem strictMono_sortedLabelGraph {n m : ℕ} (f : Fin n → Fin m) :
    StrictMono (sortedLabelGraph f) :=
  Tuple.eq_sort_iff'.mp (rfl : Tuple.sort f = Tuple.sort f)

/-- A global labeling is in bijection with the original two labels on an actual shuffle's value blocks. -/
def splitShuffleLabelsEquiv (p q m : ℕ) (s : Shuffle p q) :
    (Fin (p + q) → Fin m) ≃ (Fin p → Fin m) × (Fin q → Fin m) where
  toFun f := (fun i => f (s.perm (Fin.castAdd q i)), fun i => f (s.perm (Fin.natAdd p i)))
  invFun f := fun i => Fin.addCases f.1 f.2 (s.perm.symm i)
  left_inv f := by
    funext i
    obtain ⟨j, rfl⟩ := s.perm.surjective i
    obtain ⟨k, rfl⟩ := (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)).surjective j
    cases k <;> simp
  right_inv f := by
    apply Prod.ext
    · funext i
      simp
    · funext i
      simp

/-- The native global sort rank makes a block factorization a shuffle exactly when its two actual split sorts are
  the original rank permutations. -/
theorem isShuffle_sortRank_block_iff (p q m : ℕ) (s : Shuffle p q)
    (α : Perm (Fin p)) (β : Perm (Fin q)) (f : Fin (p + q) → Fin m) :
    IsShuffle ((Tuple.sort f).symm * (s.perm * blockPermutation p q α β)) ↔
      Tuple.sort (splitShuffleLabelsEquiv p q m s f).1 = α ∧
        Tuple.sort (splitShuffleLabelsEquiv p q m s f).2 = β := by
  have hglobal := strictMono_sortedLabelGraph f
  have hleft := Prod.Lex.strictMono_map_right (γ := Fin m)
    (fun i => s.perm (Fin.castAdd q i)) s.isShuffle.1
  have hright := Prod.Lex.strictMono_map_right (γ := Fin m)
    (fun i => s.perm (Fin.natAdd p i)) s.isShuffle.2
  constructor
  · intro hs
    constructor
    · apply Eq.symm
      apply Tuple.eq_sort_iff'.mpr
      intro i j hij
      apply hleft.lt_iff_lt.mp
      have h := hs.1 hij
      change (Tuple.sort f).symm (s.perm (blockPermutation p q α β (Fin.castAdd q i))) <
        (Tuple.sort f).symm (s.perm (blockPermutation p q α β (Fin.castAdd q j))) at h
      rw [blockPermutation_castAdd, blockPermutation_castAdd] at h
      change toLex (f (s.perm (Fin.castAdd q (α i))), s.perm (Fin.castAdd q (α i))) <
        toLex (f (s.perm (Fin.castAdd q (α j))), s.perm (Fin.castAdd q (α j)))
      simpa only [sortedLabelGraph, Equiv.apply_symm_apply] using hglobal h
    · apply Eq.symm
      apply Tuple.eq_sort_iff'.mpr
      intro i j hij
      apply hright.lt_iff_lt.mp
      have h := hs.2 hij
      change (Tuple.sort f).symm (s.perm (blockPermutation p q α β (Fin.natAdd p i))) <
        (Tuple.sort f).symm (s.perm (blockPermutation p q α β (Fin.natAdd p j))) at h
      rw [blockPermutation_natAdd, blockPermutation_natAdd] at h
      change toLex (f (s.perm (Fin.natAdd p (β i))), s.perm (Fin.natAdd p (β i))) <
        toLex (f (s.perm (Fin.natAdd p (β j))), s.perm (Fin.natAdd p (β j)))
      simpa only [sortedLabelGraph, Equiv.apply_symm_apply] using hglobal h
  · rintro ⟨hα, hβ⟩
    have hgleft := Tuple.eq_sort_iff'.mp hα.symm
    have hgright := Tuple.eq_sort_iff'.mp hβ.symm
    constructor
    · intro i j hij
      change (Tuple.sort f).symm (s.perm (blockPermutation p q α β (Fin.castAdd q i))) <
        (Tuple.sort f).symm (s.perm (blockPermutation p q α β (Fin.castAdd q j)))
      rw [blockPermutation_castAdd, blockPermutation_castAdd]
      apply hglobal.lt_iff_lt.mp
      have hh := hleft (hgleft hij)
      change toLex (f (s.perm (Fin.castAdd q (α i))), s.perm (Fin.castAdd q (α i))) <
        toLex (f (s.perm (Fin.castAdd q (α j))), s.perm (Fin.castAdd q (α j))) at hh
      simpa only [sortedLabelGraph, Equiv.apply_symm_apply] using hh
    · intro i j hij
      change (Tuple.sort f).symm (s.perm (blockPermutation p q α β (Fin.natAdd p i))) <
        (Tuple.sort f).symm (s.perm (blockPermutation p q α β (Fin.natAdd p j)))
      rw [blockPermutation_natAdd, blockPermutation_natAdd]
      apply hglobal.lt_iff_lt.mp
      have hh := hright (hgright hij)
      change toLex (f (s.perm (Fin.natAdd p (β i))), s.perm (Fin.natAdd p (β i))) <
        toLex (f (s.perm (Fin.natAdd p (β j))), s.perm (Fin.natAdd p (β j))) at hh
      simpa only [sortedLabelGraph, Equiv.apply_symm_apply] using hh

/-- The actual global-sort/shuffle composition fiber at the original output permutation. -/
abbrev ShuffleSortFiber (p q m : ℕ) (γ : Perm (Fin (p + q))) :=
  {z : (Fin (p + q) → Fin m) × Shuffle p q // Tuple.sort z.1 * z.2.perm = γ}

/-- The actual shuffle/two-block-sort composition fiber at the original output permutation. -/
abbrev SplitShuffleSortFiber (p q m : ℕ) (γ : Perm (Fin (p + q))) :=
  {z : Shuffle p q × (Fin p → Fin m) × (Fin q → Fin m) //
    z.1.perm * blockPermutation p q (Tuple.sort z.2.1) (Tuple.sort z.2.2) = γ}

/-- The actual finite global-label/shuffle fiber, including empty alphabets and blocks. -/
instance shuffleSortFiberFintype (p q m : ℕ) (γ : Perm (Fin (p + q))) :
    Fintype (ShuffleSortFiber p q m γ) := Fintype.ofFinite _

/-- The actual finite two-block-label/shuffle fiber uses its original predicate. -/
instance splitShuffleSortFiberFintype (p q m : ℕ) (γ : Perm (Fin (p + q))) :
    Fintype (SplitShuffleSortFiber p q m γ) := Fintype.ofFinite _

/-- The original fiber equation computes exactly the shuffle permutation in global-sort rank coordinates. -/
theorem shuffleSortFiber_rank_perm (p q m : ℕ) (γ : Perm (Fin (p + q)))
    (z : ShuffleSortFiber p q m γ) :
    (Tuple.sort z.val.1).symm * γ = z.val.2.perm := by
  have h := congrArg (fun τ : Perm (Fin (p + q)) => (Tuple.sort z.val.1).symm * τ) z.property
  change (Tuple.sort z.val.1)⁻¹ * (Tuple.sort z.val.1 * z.val.2.perm) =
    (Tuple.sort z.val.1)⁻¹ * γ at h
  exact h.symm.trans (inv_mul_cancel_left _ _)

/-- The exact original composition fiber is equivalent to its actual global-sort rank labelings. -/
def shuffleSortFiberEquivRankLabels (p q m : ℕ) (γ : Perm (Fin (p + q))) :
    ShuffleSortFiber p q m γ ≃
      {f : Fin (p + q) → Fin m // IsShuffle ((Tuple.sort f).symm * γ)} where
  toFun z := ⟨z.val.1, by
    have hp := shuffleSortFiber_rank_perm p q m γ z
    exact Eq.mpr (congrArg (fun τ : Perm (Fin (p + q)) => IsShuffle (p := p) (q := q) τ) hp)
      z.val.2.isShuffle⟩
  invFun f := ⟨(f.val, ⟨(Tuple.sort f.val).symm * γ, f.property⟩), by
    change Tuple.sort f.val * ((Tuple.sort f.val)⁻¹ * γ) = γ
    exact mul_inv_cancel_left _ _⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Shuffle.ext
      exact shuffleSortFiber_rank_perm p q m γ z
  right_inv f := rfl

/-- Actual split-label restriction identifies rank labelings with the two original sorting fibers. -/
def rankLabelsEquivSplitSortFibers (p q m : ℕ) (s : Shuffle p q)
    (α : Perm (Fin p)) (β : Perm (Fin q)) :
    {f : Fin (p + q) → Fin m // IsShuffle ((Tuple.sort f).symm * (s.perm * blockPermutation p q α β))} ≃
      {g : Fin p → Fin m // Tuple.sort g = α} × {h : Fin q → Fin m // Tuple.sort h = β} where
  toFun f :=
    (⟨(splitShuffleLabelsEquiv p q m s f.val).1,
       ((isShuffle_sortRank_block_iff p q m s α β f.val).mp f.property).1⟩,
     ⟨(splitShuffleLabelsEquiv p q m s f.val).2,
       ((isShuffle_sortRank_block_iff p q m s α β f.val).mp f.property).2⟩)
  invFun f := ⟨(splitShuffleLabelsEquiv p q m s).symm (f.1.val, f.2.val), by
    apply (isShuffle_sortRank_block_iff p q m s α β _).mpr
    rw [Equiv.apply_symm_apply]
    exact ⟨f.1.property, f.2.property⟩⟩
  left_inv f := by apply Subtype.ext; exact (splitShuffleLabelsEquiv p q m s).symm_apply_apply f.val
  right_inv f := by
    have h := (splitShuffleLabelsEquiv p q m s).apply_symm_apply (f.1.val, f.2.val)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · apply Subtype.ext
      exact congrArg Prod.snd h

/-- The actual left product fiber is in bijection with the original two block sorting fibers. -/
def shuffleSortFiberEquiv (p q m : ℕ) (γ : Perm (Fin (p + q))) :
    ShuffleSortFiber p q m γ ≃
      {g : Fin p → Fin m // Tuple.sort g = blockRankLeft p q γ} ×
        {h : Fin q → Fin m // Tuple.sort h = blockRankRight p q γ} := by
  let e := shuffleSortFiberEquivRankLabels p q m γ
  have hγ := sortedBlockShuffle_factorization p q γ
  exact e.trans
    ((Equiv.subtypeEquiv (Equiv.refl _) (fun f => by simp only [Equiv.refl_apply, hγ])).trans
      (rankLabelsEquivSplitSortFibers p q m (sortedBlockShuffle p q γ)
        (blockRankLeft p q γ) (blockRankRight p q γ)))

/-- The actual right product fiber has the same pair of original sorting fibers. -/
def splitShuffleSortFiberEquiv (p q m : ℕ) (γ : Perm (Fin (p + q))) :
    SplitShuffleSortFiber p q m γ ≃
      {g : Fin p → Fin m // Tuple.sort g = blockRankLeft p q γ} ×
        {h : Fin q → Fin m // Tuple.sort h = blockRankRight p q γ} where
  toFun z :=
    (⟨z.val.2.1, (sortedBlockShuffle_factorization_unique p q z.val.1
        (Tuple.sort z.val.2.1) (Tuple.sort z.val.2.2) γ z.property).1⟩,
     ⟨z.val.2.2, (sortedBlockShuffle_factorization_unique p q z.val.1
        (Tuple.sort z.val.2.1) (Tuple.sort z.val.2.2) γ z.property).2.1⟩)
  invFun z := ⟨(sortedBlockShuffle p q γ, z.1.val, z.2.val), by
    rw [z.1.property, z.2.property]
    exact sortedBlockShuffle_factorization p q γ⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact (sortedBlockShuffle_factorization_unique p q z.val.1
        (Tuple.sort z.val.2.1) (Tuple.sort z.val.2.2) γ z.property).2.2.symm
    · rfl
  right_inv z := rfl

/-- The actual composition fibers of the two shuffle products have exactly the same cardinality. -/
theorem card_shuffleSortFiber_eq (p q m : ℕ) (γ : Perm (Fin (p + q))) :
    Fintype.card (ShuffleSortFiber p q m γ) = Fintype.card (SplitShuffleSortFiber p q m γ) :=
  Fintype.card_congr ((shuffleSortFiberEquiv p q m γ).trans
    (splitShuffleSortFiberEquiv p q m γ).symm)

end Equiv.Perm
