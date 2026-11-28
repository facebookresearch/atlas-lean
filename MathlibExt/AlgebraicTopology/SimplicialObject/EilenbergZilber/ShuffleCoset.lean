/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.Shuffle
public import Mathlib.LinearAlgebra.Alternating.DomCoprod
public import Mathlib.GroupTheory.Perm.Finite

/-!
# Block-permutation cosets and ordered shuffles

For B = Fin p ⊕ Fin q, quotient the permutation group of B by right composition with
permutations of each block separately. A coset determines the p-element set of images of the
left block under the standard equivalence B ≃ Fin (p + q). Conversely, each such set
determines a unique ordered (p, q)-shuffle.

These maps give equivalences from the block-permutation coset space to p-element position sets
and to ordered shuffles. The inverse assigns the coset of the ordered shuffle transported back
to B. Both blocks may be empty, and the identification uses position sets without division by
factorials.
-/

@[expose] public section

noncomputable section

namespace AlgebraicTopology.EilenbergZilber.Shuffle

open Function

variable (p q : ℕ)

local notation "B" => Fin p ⊕ Fin q
local notation "e" => (finSumFinEquiv : B ≃ Fin (p + q))

/-- Let p, q : ℕ, B = Fin p ⊕ Fin q, and e : B ≃ Fin (p + q) be finSumFinEquiv. Let H be the
subgroup of permutations of B that permute each block separately. For a permutation σ of B,
blockLeftPositions p q σ is the p-element subset {e(σ(Sum.inl i)) | i : Fin p} of Fin (p + q).
The embedding of the left block makes this set have cardinality p. -/
def blockLeftPositions (σ : Equiv.Perm B) : Set.powersetCard (Fin (p + q)) p :=
  Set.powersetCard.ofFinEmb p _
    ⟨fun i => e (σ (Sum.inl i)),
      (finSumFinEquiv : B ≃ Fin (p + q)).injective.comp (σ.injective.comp Sum.inl_injective)⟩

@[simp]
theorem mem_blockLeftPositions (σ : Equiv.Perm B) (k : Fin (p + q)) :
    k ∈ blockLeftPositions p q σ ↔ ∃ i : Fin p, e (σ (Sum.inl i)) = k := by
  rw [blockLeftPositions, Set.powersetCard.mem_ofFinEmb_iff_mem_range]
  rfl

theorem blockLeftPositions_rel (σ τ : Equiv.Perm B)
    (h : QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin p) (Fin q)).range σ τ) :
    blockLeftPositions p q σ = blockLeftPositions p q τ := by
  rw [QuotientGroup.leftRel_apply] at h
  obtain ⟨⟨sl, sr⟩, h⟩ := h
  replace h := inv_mul_eq_iff_eq_mul.mp h.symm
  rw [h]
  apply SetLike.ext
  intro k
  simp only [mem_blockLeftPositions, Equiv.Perm.coe_mul, Function.comp_apply,
    Equiv.Perm.sumCongrHom_apply, Equiv.sumCongr_apply, Sum.map_inl]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨sl.symm i, by simpa only [Equiv.apply_symm_apply] using hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨sl i, hi⟩

/-- Let p, q : ℕ, B = Fin p ⊕ Fin q, and e : B ≃ Fin (p + q) be finSumFinEquiv. Let H be the
subgroup of permutations of B that permute each block separately. The left-position map
descends to the coset space Equiv.Perm.ModSumCongr (Fin p) (Fin q). A coset represented by σ
is sent to {e(σ(Sum.inl i)) | i : Fin p}; right composition with an element of H preserves
this set. -/
def cosetLeftPositions (c : Equiv.Perm.ModSumCongr (Fin p) (Fin q)) :
    Set.powersetCard (Fin (p + q)) p :=
  Quotient.liftOn' c (blockLeftPositions p q) (blockLeftPositions_rel p q)

@[simp]
theorem cosetLeftPositions_mk (σ : Equiv.Perm B) :
    cosetLeftPositions p q (Quotient.mk'' σ) = blockLeftPositions p q σ := rfl

/-- Let p, q : ℕ, B = Fin p ⊕ Fin q, and e : B ≃ Fin (p + q) be finSumFinEquiv. Let H be the
subgroup of permutations of B that permute each block separately. An ordered shuffle s with
permutation σ on Fin (p + q) determines the block-sum permutation e⁻¹ ∘ σ ∘ e. Its transport
along e is σ, and its coset is the inverse image of s under the coset-to-shuffle equivalence. -/
def cosetRepresentative (s : Shuffle p q) : Equiv.Perm B :=
  (Equiv.permCongr e).symm s.perm

theorem cosetRepresentative_congr (s : Shuffle p q) :
    (finSumFinEquiv : B ≃ Fin (p + q)).permCongr (cosetRepresentative p q s) = s.perm :=
  (Equiv.permCongr e).apply_symm_apply s.perm

@[simp]
theorem cosetRepresentative_front (s : Shuffle p q) (i : Fin p) :
    e (cosetRepresentative p q s (Sum.inl i)) = s.perm (Fin.castAdd q i) := by
  have h := congrArg (fun σ : Equiv.Perm (Fin (p + q)) => σ (e (Sum.inl i)))
    (cosetRepresentative_congr p q s)
  simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply,
    finSumFinEquiv_apply_left, finSumFinEquiv_symm_apply_castAdd] using h

@[simp]
theorem cosetRepresentative_back (s : Shuffle p q) (i : Fin q) :
    e (cosetRepresentative p q s (Sum.inr i)) = s.perm (Fin.natAdd p i) := by
  have h := congrArg (fun σ : Equiv.Perm (Fin (p + q)) => σ (e (Sum.inr i)))
    (cosetRepresentative_congr p q s)
  simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply,
    finSumFinEquiv_apply_right, finSumFinEquiv_symm_apply_natAdd] using h

theorem cosetRepresentative_sign (s : Shuffle p q) :
    Equiv.Perm.sign (cosetRepresentative p q s) = Equiv.Perm.sign s.perm := by
  rw [← cosetRepresentative_congr p q s]
  exact (Equiv.Perm.sign_permCongr e (cosetRepresentative p q s)).symm

theorem blockLeftPositions_representative (s : Shuffle p q) :
    blockLeftPositions p q (cosetRepresentative p q s) = s.leftPositions := by
  apply SetLike.ext
  intro k
  simp only [mem_blockLeftPositions, cosetRepresentative_front, mem_leftPositions_iff]

/-- Let p, q : ℕ, B = Fin p ⊕ Fin q, and e : B ≃ Fin (p + q) be finSumFinEquiv. Let H be the
subgroup of permutations of B that permute each block separately. The map from
Equiv.Perm.ModSumCongr (Fin p) (Fin q) to p-element position sets is injective. If two cosets
have the same images of the left block in Fin (p + q), their representatives differ by right
composition with a permutation in H. -/
theorem cosetLeftPositions_injective : Function.Injective (cosetLeftPositions p q) := by
  intro c d hcd
  induction c using Quotient.inductionOn' with
  | _ σ =>
    induction d using Quotient.inductionOn' with
    | _ τ =>
      simp only [cosetLeftPositions_mk] at hcd
      rw [Quotient.eq'', QuotientGroup.leftRel_apply]
      apply Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
      rintro _ ⟨i, rfl⟩
      have hi : e (τ (Sum.inl i)) ∈ blockLeftPositions p q σ := by
        rw [hcd, mem_blockLeftPositions]
        exact ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := (mem_blockLeftPositions p q σ _).mp hi
      have hj' : σ (Sum.inl j) = τ (Sum.inl i) := (finSumFinEquiv : B ≃ Fin (p + q)).injective hj
      refine ⟨j, ?_⟩
      apply σ.injective
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      exact hj'.trans (σ.apply_symm_apply (τ (Sum.inl i))).symm

/-- Let p, q : ℕ, B = Fin p ⊕ Fin q, and e : B ≃ Fin (p + q) be finSumFinEquiv. Let H be the
subgroup of permutations of B that permute each block separately. Every p-element subset L of
Fin (p + q) is the left-position set of a block-permutation coset. A representative is e⁻¹ ∘
σ_L ∘ e, where σ_L is the unique shuffle increasing on both blocks and having left positions
L. -/
theorem cosetLeftPositions_surjective : Function.Surjective (cosetLeftPositions p q) := by
  intro a
  refine ⟨Quotient.mk'' (cosetRepresentative p q (ofLeftPositions a)), ?_⟩
  rw [cosetLeftPositions_mk, blockLeftPositions_representative, leftPositions_ofLeftPositions]

/-- Let p, q : ℕ, B = Fin p ⊕ Fin q, and e : B ≃ Fin (p + q) be finSumFinEquiv. Let H be the
subgroup of permutations of B that permute each block separately. The left-position map gives
an equivalence Equiv.Perm.ModSumCongr (Fin p) (Fin q) ≃ Set.powersetCard (Fin (p + q)) p. It
sends the coset of σ to the image of its left block and inverts this map by choosing the
ordered representative of each position set. -/
def cosetPositionsEquiv : Equiv.Perm.ModSumCongr (Fin p) (Fin q) ≃
    Set.powersetCard (Fin (p + q)) p :=
  Equiv.ofBijective (cosetLeftPositions p q)
    ⟨cosetLeftPositions_injective p q, cosetLeftPositions_surjective p q⟩

/-- Let p, q : ℕ, B = Fin p ⊕ Fin q, and e : B ≃ Fin (p + q) be finSumFinEquiv. Let H be the
subgroup of permutations of B that permute each block separately. The left-position
equivalence followed by the position-set-to-shuffle equivalence gives Equiv.Perm.ModSumCongr
(Fin p) (Fin q) ≃ Shuffle p q. Its inverse sends a shuffle with permutation σ to the coset of
e⁻¹ ∘ σ ∘ e; the equivalence includes p = 0 and q = 0. -/
def cosetEquiv : Equiv.Perm.ModSumCongr (Fin p) (Fin q) ≃ Shuffle p q :=
  (cosetPositionsEquiv p q).trans equivLeftPositions.symm

@[simp]
theorem cosetEquiv_symm_apply (s : Shuffle p q) :
    (cosetEquiv p q).symm s = Quotient.mk'' (cosetRepresentative p q s) := by
  apply cosetLeftPositions_injective p q
  change (cosetPositionsEquiv p q) ((cosetPositionsEquiv p q).symm s.leftPositions) =
    cosetLeftPositions p q (Quotient.mk'' (cosetRepresentative p q s))
  rw [Equiv.apply_symm_apply, cosetLeftPositions_mk, blockLeftPositions_representative]

end AlgebraicTopology.EilenbergZilber.Shuffle
