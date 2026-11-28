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
# Shuffle factorization by ordered value blocks

For `p,q : ℕ`, a block permutation acts independently on the first `p` and last `q` positions
of `Fin(p+q)`. Its sign is the product of the two block signs.

Given `γ ∈ S_(p+q)`, let `α` and `β` be the inverses of the stable sorting permutations of its
left and right value blocks. Then `s = γ * blockPermutation(α⁻¹,β⁻¹)` is a `(p,q)`-shuffle,
and `γ = s.perm * blockPermutation(α,β)`. This decomposition is unique, including empty
blocks.

References: Stanley, *Enumerative Combinatorics*, Volume 1, Chapter 1; Loday, *Cyclic
Homology*, Section 4.2.
-/

@[expose] public section
noncomputable section

namespace Equiv.Perm

/-- Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. For `α ∈ S_p` and `β ∈ S_q`, `blockPermutation p q α β` sends `L(i)` to
`L(α i)` and `R(j)` to `R(β j)`. -/
def blockPermutation (p q : ℕ) (α : Perm (Fin p)) (β : Perm (Fin q)) : Perm (Fin (p + q)) :=
  (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)).permCongr (Equiv.sumCongr α β)

/-- Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. For `α ∈ S_p`, `β ∈ S_q`, and `i : Fin p`, `blockPermutation p q α β (L
i) = L(α i)`. -/
@[simp]
theorem blockPermutation_castAdd (p q : ℕ) (α : Perm (Fin p)) (β : Perm (Fin q)) (i : Fin p) :
    blockPermutation p q α β (Fin.castAdd q i) = Fin.castAdd q (α i) := by
  simp [blockPermutation, Equiv.permCongr_apply]

/-- Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. For `α ∈ S_p`, `β ∈ S_q`, and `j : Fin q`, `blockPermutation p q α β (R
j) = R(β j)`. -/
@[simp]
theorem blockPermutation_natAdd (p q : ℕ) (α : Perm (Fin p)) (β : Perm (Fin q)) (i : Fin q) :
    blockPermutation p q α β (Fin.natAdd p i) = Fin.natAdd p (β i) := by
  simp [blockPermutation, Equiv.permCongr_apply]

/-- Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. For `α,α' ∈ S_p` and `β,β' ∈ S_q`, `blockPermutation(α*α',β*β') =
blockPermutation(α,β) * blockPermutation(α',β')`. -/
theorem blockPermutation_mul (p q : ℕ) (α α' : Perm (Fin p)) (β β' : Perm (Fin q)) :
    blockPermutation p q (α * α') (β * β') =
      blockPermutation p q α β * blockPermutation p q α' β' := by
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

/-- Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. The assignment `(α,β) ↦ blockPermutation p q α β` is the monoid
homomorphism `S_p × S_q →* S_N`. -/
def blockPermutationHom (p q : ℕ) : Perm (Fin p) × Perm (Fin q) →* Perm (Fin (p + q)) where
  toFun z := blockPermutation p q z.1 z.2
  map_one' := by
    ext i
    obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)).surjective i
    cases j <;> simp
  map_mul' z z' := blockPermutation_mul p q z.1 z'.1 z.2 z'.2

/-- Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. `blockLeftHom p q : S_p →* S_N` sends `α` to `blockPermutation p q α 1`,
acting on the left block and fixing the right block. -/
def blockLeftHom (p q : ℕ) : Perm (Fin p) →* Perm (Fin (p + q)) where
  toFun α := blockPermutation p q α 1
  map_one' := (blockPermutationHom p q).map_one
  map_mul' α β := by simpa only [one_mul] using blockPermutation_mul p q α β 1 1

/-- Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. `blockRightHom p q : S_q →* S_N` sends `β` to `blockPermutation p q 1
β`, fixing the left block and acting on the right block. -/
def blockRightHom (p q : ℕ) : Perm (Fin q) →* Perm (Fin (p + q)) where
  toFun β := blockPermutation p q 1 β
  map_one' := (blockPermutationHom p q).map_one
  map_mul' α β := by simpa only [one_mul] using blockPermutation_mul p q 1 1 α β

/-- Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. For `α ∈ S_p` and `β ∈ S_q`, `blockLeftHom p q α * blockRightHom p q β =
blockPermutation p q α β`. -/
theorem blockLeftHom_mul_blockRightHom (p q : ℕ) (α : Perm (Fin p)) (β : Perm (Fin q)) :
    blockLeftHom p q α * blockRightHom p q β = blockPermutation p q α β := by
  change blockPermutation p q α 1 * blockPermutation p q 1 β = _
  rw [← blockPermutation_mul, mul_one, one_mul]

/-- Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. For `α ∈ S_p` and `β ∈ S_q`, `(blockPermutation p q α β).sign = α.sign *
β.sign` in `ℤˣ`. -/
theorem sign_blockPermutation (p q : ℕ) (α : Perm (Fin p)) (β : Perm (Fin q)) :
    (blockPermutation p q α β).sign = α.sign * β.sign := by
  rw [blockPermutation, sign_permCongr, sign_sumCongr]

/-- Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. For `γ ∈ S_N`, `blockRankLeft p q γ = (Tuple.sort (fun i : Fin p ↦ γ(L
i)))⁻¹ ∈ S_p`. It records the rank of each left-block value in its ascending order. -/
def blockRankLeft (p q : ℕ) (γ : Perm (Fin (p + q))) : Perm (Fin p) :=
  (Tuple.sort (fun i => γ (Fin.castAdd q i))).symm

/-- Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. For `γ ∈ S_N`, `blockRankRight p q γ = (Tuple.sort (fun j : Fin q ↦ γ(R
j)))⁻¹ ∈ S_q`. It records the rank of each right-block value in its ascending order. -/
def blockRankRight (p q : ℕ) (γ : Perm (Fin (p + q))) : Perm (Fin q) :=
  (Tuple.sort (fun i => γ (Fin.natAdd p i))).symm

/-- Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. For `γ ∈ S_N`, put `α = blockRankLeft p q γ` and `β = blockRankRight p q
γ`. The permutation `γ * blockPermutation p q α⁻¹ β⁻¹` is increasing on each block and defines
`sortedBlockShuffle p q γ : Shuffle p q`. -/
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

/-- Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. For `γ ∈ S_N`, with `α = blockRankLeft p q γ` and `β = blockRankRight p
q γ`, `(sortedBlockShuffle p q γ).perm * blockPermutation p q α β = γ`. -/
theorem sortedBlockShuffle_factorization (p q : ℕ) (γ : Perm (Fin (p + q))) :
    (sortedBlockShuffle p q γ).perm *
      blockPermutation p q (blockRankLeft p q γ) (blockRankRight p q γ) = γ := by
  change (γ * blockPermutationHom p q ((blockRankLeft p q γ).symm, (blockRankRight p q γ).symm)) *
    blockPermutationHom p q (blockRankLeft p q γ, blockRankRight p q γ) = γ
  rw [mul_assoc, ← map_mul]
  change γ * blockPermutationHom p q
    ((blockRankLeft p q γ, blockRankRight p q γ)⁻¹ *
      (blockRankLeft p q γ, blockRankRight p q γ)) = γ
  rw [inv_mul_cancel, map_one, mul_one]

/-- Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. Let `s : Shuffle p q`, `α ∈ S_p`, `β ∈ S_q`, and `γ ∈ S_N` satisfy
`s.perm * blockPermutation p q α β = γ`. Then `α = blockRankLeft p q γ`, `β = blockRankRight p
q γ`, and `s = sortedBlockShuffle p q γ`. -/
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

/-- Let `α,β,γ` be linearly ordered types and `f : α → β` strictly increasing. The map `γ ×ₗ α → γ
×ₗ β`, `(x,y) ↦ (x,f y)`, is strictly increasing in lexicographic order. -/
theorem strictMono_map_right (f : α → β) (hf : StrictMono f) :
    StrictMono (fun z : γ ×ₗ α => toLex ((ofLex z).1, f (ofLex z).2)) := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  apply toLex_lt_toLex.mpr
  obtain hfirst | ⟨heq, hsecond⟩ := toLex_lt_toLex.mp h
  · exact Or.inl hfirst
  · exact Or.inr ⟨heq, hf hsecond⟩

end Prod.Lex
