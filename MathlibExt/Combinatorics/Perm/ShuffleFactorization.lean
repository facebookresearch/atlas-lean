/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShufflePosition
public import MathlibExt.Data.Fin.Tuple.StableSort

/-!
# Actual native shuffle and block-permutation factorization

Sorting each original block of permutation values constructs an actual
native shuffle. Its two original block rank permutations give the genuine
factorization, and native stable-sort uniqueness proves this factorization
is unique. Empty blocks are retained. No factorization certificate is an
input.
-/

@[expose] public section
noncomputable section

namespace Equiv.Perm

/-- The actual block permutation on the original concatenated finite index. -/
def blockPermutation (p q : ℕ) (α : Perm (Fin p)) (β : Perm (Fin q)) : Perm (Fin (p + q)) :=
  (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)).permCongr (Equiv.sumCongr α β)

/-- The actual block permutation keeps the original first block and its original rank action. -/
@[simp]
theorem blockPermutation_castAdd (p q : ℕ) (α : Perm (Fin p)) (β : Perm (Fin q)) (i : Fin p) :
    blockPermutation p q α β (Fin.castAdd q i) = Fin.castAdd q (α i) := by
  simp [blockPermutation, Equiv.permCongr_apply]

/-- The actual block permutation keeps the original second block and its original rank action. -/
@[simp]
theorem blockPermutation_natAdd (p q : ℕ) (α : Perm (Fin p)) (β : Perm (Fin q)) (i : Fin q) :
    blockPermutation p q α β (Fin.natAdd p i) = Fin.natAdd p (β i) := by
  simp [blockPermutation, Equiv.permCongr_apply]

/-- Original block permutation composition is actual componentwise permutation composition. -/
theorem blockPermutation_mul (p q : ℕ) (α α' : Perm (Fin p)) (β β' : Perm (Fin q)) :
    blockPermutation p q (α * α') (β * β') = blockPermutation p q α β * blockPermutation p q α' β' := by
  apply Equiv.ext
  intro i
  rw [Equiv.Perm.mul_apply]
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)).surjective i
  cases j with
  | inl j =>
    change blockPermutation p q (α * α') (β * β') (Fin.castAdd q j) =
      blockPermutation p q α β (blockPermutation p q α' β' (Fin.castAdd q j))
    rw [blockPermutation_castAdd, blockPermutation_castAdd, blockPermutation_castAdd]
    rfl
  | inr j =>
    change blockPermutation p q (α * α') (β * β') (Fin.natAdd p j) =
      blockPermutation p q α β (blockPermutation p q α' β' (Fin.natAdd p j))
    rw [blockPermutation_natAdd, blockPermutation_natAdd, blockPermutation_natAdd]
    rfl

/-- The actual block construction is a native monoid homomorphism. -/
def blockPermutationHom (p q : ℕ) : Perm (Fin p) × Perm (Fin q) →* Perm (Fin (p + q)) where
  toFun z := blockPermutation p q z.1 z.2
  map_one' := by
    ext i
    obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)).surjective i
    cases j <;> simp
  map_mul' z z' := blockPermutation_mul p q z.1 z'.1 z.2 z'.2

/-- The actual first-block permutation inclusion is a native monoid map. -/
def blockLeftHom (p q : ℕ) : Perm (Fin p) →* Perm (Fin (p + q)) where
  toFun α := blockPermutation p q α 1
  map_one' := (blockPermutationHom p q).map_one
  map_mul' α β := by simpa only [one_mul] using blockPermutation_mul p q α β 1 1

/-- The actual second-block permutation inclusion is a native monoid map. -/
def blockRightHom (p q : ℕ) : Perm (Fin q) →* Perm (Fin (p + q)) where
  toFun β := blockPermutation p q 1 β
  map_one' := (blockPermutationHom p q).map_one
  map_mul' α β := by simpa only [one_mul] using blockPermutation_mul p q 1 1 α β

/-- The original two block inclusions multiply to the actual combined original block permutation. -/
theorem blockLeftHom_mul_blockRightHom (p q : ℕ) (α : Perm (Fin p)) (β : Perm (Fin q)) :
    blockLeftHom p q α * blockRightHom p q β = blockPermutation p q α β := by
  change blockPermutation p q α 1 * blockPermutation p q 1 β = _
  rw [← blockPermutation_mul, mul_one, one_mul]

/-- The original block sign is the actual product of the original two signs. -/
theorem sign_blockPermutation (p q : ℕ) (α : Perm (Fin p)) (β : Perm (Fin q)) :
    (blockPermutation p q α β).sign = α.sign * β.sign := by
  rw [blockPermutation, sign_permCongr, sign_sumCongr]

/-- The original first block rank permutation. -/
def blockRankLeft (p q : ℕ) (γ : Perm (Fin (p + q))) : Perm (Fin p) :=
  (Tuple.sort (fun i => γ (Fin.castAdd q i))).symm

/-- The original second block rank permutation. -/
def blockRankRight (p q : ℕ) (γ : Perm (Fin (p + q))) : Perm (Fin q) :=
  (Tuple.sort (fun i => γ (Fin.natAdd p i))).symm

/-- Sorting the two original value blocks constructs an actual native shuffle. -/
def sortedBlockShuffle (p q : ℕ) (γ : Perm (Fin (p + q))) :
    AlgebraicTopology.EilenbergZilber.Shuffle p q where
  perm := γ * blockPermutation p q (blockRankLeft p q γ).symm (blockRankRight p q γ).symm
  isShuffle := by
    constructor
    · change StrictMono (fun i => γ (blockPermutation p q
        (blockRankLeft p q γ).symm (blockRankRight p q γ).symm (Fin.castAdd q i)))
      simp only [blockPermutation_castAdd, blockRankLeft, Equiv.symm_symm]
      apply (Tuple.monotone_sort (fun i => γ (Fin.castAdd q i))).strictMono_of_injective
      exact γ.injective.comp (Fin.castAdd_injective p q) |>.comp (Tuple.sort _).injective
    · change StrictMono (fun i => γ (blockPermutation p q
        (blockRankLeft p q γ).symm (blockRankRight p q γ).symm (Fin.natAdd p i)))
      simp only [blockPermutation_natAdd, blockRankRight, Equiv.symm_symm]
      apply (Tuple.monotone_sort (fun i => γ (Fin.natAdd p i))).strictMono_of_injective
      exact γ.injective.comp (by
        intro i j hij
        apply Fin.ext
        exact Nat.add_left_cancel (congrArg Fin.val hij)) |>.comp (Tuple.sort _).injective

/-- The actual sorted-block shuffle and original two rank permutations give the original permutation. -/
theorem sortedBlockShuffle_factorization (p q : ℕ) (γ : Perm (Fin (p + q))) :
    (sortedBlockShuffle p q γ).perm * blockPermutation p q (blockRankLeft p q γ) (blockRankRight p q γ) = γ := by
  change (γ * blockPermutationHom p q ((blockRankLeft p q γ).symm, (blockRankRight p q γ).symm)) *
    blockPermutationHom p q (blockRankLeft p q γ, blockRankRight p q γ) = γ
  rw [mul_assoc, ← map_mul]
  change γ * blockPermutationHom p q
    ((blockRankLeft p q γ, blockRankRight p q γ)⁻¹ *
      (blockRankLeft p q γ, blockRankRight p q γ)) = γ
  rw [inv_mul_cancel, map_one, mul_one]

/-- The native increasing-block condition proves the original factorization is unique. -/
theorem sortedBlockShuffle_factorization_unique (p q : ℕ)
    (s : AlgebraicTopology.EilenbergZilber.Shuffle p q) (α : Perm (Fin p)) (β : Perm (Fin q))
    (γ : Perm (Fin (p + q))) (hγ : s.perm * blockPermutation p q α β = γ) :
    α = blockRankLeft p q γ ∧ β = blockRankRight p q γ ∧ s = sortedBlockShuffle p q γ := by
  have hleft : (fun i => γ (Fin.castAdd q i)) =
      (fun i => s.perm (Fin.castAdd q i)) ∘ α := by
    funext i
    rw [← hγ]
    change s.perm (blockPermutation p q α β (Fin.castAdd q i)) = _
    rw [blockPermutation_castAdd]
    rfl
  have hright : (fun i => γ (Fin.natAdd p i)) =
      (fun i => s.perm (Fin.natAdd p i)) ∘ β := by
    funext i
    rw [← hγ]
    change s.perm (blockPermutation p q α β (Fin.natAdd p i)) = _
    rw [blockPermutation_natAdd]
    rfl
  have hα : α = blockRankLeft p q γ := by
    rw [blockRankLeft, hleft, Tuple.sort_comp_strictMono α _ s.isShuffle.1, Tuple.sort_perm]
    rfl
  have hβ : β = blockRankRight p q γ := by
    rw [blockRankRight, hright, Tuple.sort_comp_strictMono β _ s.isShuffle.2, Tuple.sort_perm]
    rfl
  refine ⟨hα, hβ, ?_⟩
  have hperm : s.perm = (sortedBlockShuffle p q γ).perm := by
    have hh : s.perm * blockPermutation p q α β =
        (sortedBlockShuffle p q γ).perm * blockPermutation p q α β := by
      rw [hγ, hα, hβ, sortedBlockShuffle_factorization]
    exact mul_right_cancel hh
  cases s with
  | mk σ hs =>
    cases hsorted : sortedBlockShuffle p q γ with
    | mk τ ht =>
      have hστ : σ = τ := by simpa only [hsorted] using hperm
      subst τ
      rfl

end Equiv.Perm

namespace Prod.Lex

variable {α β γ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/-- An actual strictly increasing second-coordinate map preserves and reflects the original lexicographic order. -/
theorem strictMono_map_right (f : α → β) (hf : StrictMono f) :
    StrictMono (fun z : γ ×ₗ α => toLex ((ofLex z).1, f (ofLex z).2)) := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  apply toLex_lt_toLex.mpr
  obtain hfirst | ⟨heq, hsecond⟩ := toLex_lt_toLex.mp h
  · exact Or.inl hfirst
  · exact Or.inr ⟨heq, hf hsecond⟩

end Prod.Lex
