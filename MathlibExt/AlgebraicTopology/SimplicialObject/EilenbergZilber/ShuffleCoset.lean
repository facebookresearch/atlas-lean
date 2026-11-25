/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.Shuffle
public import Mathlib.LinearAlgebra.Alternating.DomCoprod
public import Mathlib.GroupTheory.Perm.Finite

/-!
# Ordered shuffles and block-permutation cosets

Cosets modulo permutations inside two blocks correspond to ordered
shuffles. The map records the left-block positions; the inverse uses the
ordered shuffle representative through `finSumFinEquiv`. Both empty blocks
are included, without factorial division.
-/

@[expose] public section

noncomputable section

namespace AlgebraicTopology.EilenbergZilber.Shuffle

open Function

variable (p q : ℕ)

local notation "B" => Fin p ⊕ Fin q
local notation "e" => (finSumFinEquiv : B ≃ Fin (p + q))

/-- The actual left positions of an arbitrary block permutation. -/
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

/-- The actual left-position map on native shuffle cosets. -/
def cosetLeftPositions (c : Equiv.Perm.ModSumCongr (Fin p) (Fin q)) :
    Set.powersetCard (Fin (p + q)) p :=
  Quotient.liftOn' c (blockLeftPositions p q) (blockLeftPositions_rel p q)

@[simp]
theorem cosetLeftPositions_mk (σ : Equiv.Perm B) :
    cosetLeftPositions p q (Quotient.mk'' σ) = blockLeftPositions p q σ := rfl

/-- The existing ordered shuffle represented on the native block-sum index. -/
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

/-- Equal left positions imply equal native shuffle cosets. -/
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
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.apply_symm_apply]
      exact hj'.trans (σ.apply_symm_apply (τ (Sum.inl i))).symm

/-- The existing ordered representative reaches every finite left-position set. -/
theorem cosetLeftPositions_surjective : Function.Surjective (cosetLeftPositions p q) := by
  intro a
  refine ⟨Quotient.mk'' (cosetRepresentative p q (ofLeftPositions a)), ?_⟩
  rw [cosetLeftPositions_mk, blockLeftPositions_representative, leftPositions_ofLeftPositions]

/-- The canonical ordered-position equivalence of the actual shuffle coset. -/
def cosetPositionsEquiv : Equiv.Perm.ModSumCongr (Fin p) (Fin q) ≃
    Set.powersetCard (Fin (p + q)) p :=
  Equiv.ofBijective (cosetLeftPositions p q)
    ⟨cosetLeftPositions_injective p q, cosetLeftPositions_surjective p q⟩

/-- The native coset index agrees with the existing actual ordered-shuffle index. -/
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
