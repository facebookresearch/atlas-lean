/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Sort
public import Mathlib.Data.Set.PowersetCard
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleIndex

@[expose] public section

noncomputable section

namespace AlgebraicTopology.EilenbergZilber

namespace Shuffle

variable {p q : ℕ}

def leftPositions (s : Shuffle p q) :
    Set.powersetCard (Fin (p + q)) p :=
  Set.powersetCard.ofFinEmb p _
    ⟨fun i => s.perm (Fin.castAdd q i),
      (Equiv.injective s.perm).comp (Fin.castAdd_injective p q)⟩

def rightPositions (s : Shuffle p q) :
    Set.powersetCard (Fin (p + q)) q :=
  Set.powersetCard.ofFinEmb q _
    ⟨fun j => s.perm (Fin.natAdd p j),
      (Equiv.injective s.perm).comp (Fin.natAdd_injective q p)⟩

@[simp]
theorem mem_leftPositions_iff (s : Shuffle p q) (k : Fin (p + q)) :
    k ∈ s.leftPositions ↔ ∃ i : Fin p, s.perm (Fin.castAdd q i) = k := by
  unfold leftPositions
  rw [Set.powersetCard.mem_ofFinEmb_iff_mem_range]
  rfl

@[simp]
theorem mem_rightPositions_iff (s : Shuffle p q) (k : Fin (p + q)) :
    k ∈ s.rightPositions ↔ ∃ j : Fin q, s.perm (Fin.natAdd p j) = k := by
  unfold rightPositions
  rw [Set.powersetCard.mem_ofFinEmb_iff_mem_range]
  rfl

theorem mem_rightPositions_iff_not_mem_leftPositions (s : Shuffle p q)
    (k : Fin (p + q)) :
    k ∈ s.rightPositions ↔ k ∉ s.leftPositions := by
  rw [mem_rightPositions_iff, mem_leftPositions_iff]
  constructor
  · rintro ⟨j, hj⟩ ⟨i, hi⟩
    have hperm : Fin.natAdd p j = Fin.castAdd q i :=
      s.perm.injective (hj.trans hi.symm)
    have hsum : (Sum.inl i : Fin p ⊕ Fin q) = Sum.inr j :=
      (_root_.finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)).injective (by
        simp only [_root_.finSumFinEquiv_apply_left,
          _root_.finSumFinEquiv_apply_right]
        exact hperm.symm)
    cases hsum
  · intro hk
    obtain ⟨x, hx⟩ :=
      (_root_.finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)).surjective
        (s.perm.symm k)
    rcases x with i | j
    · exfalso
      apply hk
      simp only [_root_.finSumFinEquiv_apply_left] at hx
      exact ⟨i, by rw [hx]; exact Equiv.apply_symm_apply s.perm k⟩
    · simp only [_root_.finSumFinEquiv_apply_right] at hx
      exact ⟨j, by rw [hx]; exact Equiv.apply_symm_apply s.perm k⟩

theorem rightPositions_eq_compl (s : Shuffle p q) :
    s.rightPositions =
      Set.powersetCard.compl (by simp [Nat.add_comm]) s.leftPositions := by
  apply SetLike.ext
  intro k
  rw [mem_rightPositions_iff_not_mem_leftPositions,
    Set.powersetCard.mem_compl]

def ofLeftPositions (s : Set.powersetCard (Fin (p + q)) p) :
    Shuffle p q :=
  have hs : s.val.card = p := Set.powersetCard.card_eq s
  have hsc : s.valᶜ.card = q := by
    have hcompl : s.valᶜ.card =
        Fintype.card (Fin (p + q)) - s.val.card :=
      Finset.card_compl s.val
    rw [hcompl, hs, Fintype.card_fin]
    omega
  ⟨(_root_.finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)).symm.trans
    (finSumEquivOfFinset hs hsc),
    ⟨by
      simp only [Equiv.trans_apply,
        _root_.finSumFinEquiv_symm_apply_castAdd]
      exact (s.val.orderEmbOfFin hs).strictMono,
    by
      simp only [Equiv.trans_apply,
        _root_.finSumFinEquiv_symm_apply_natAdd]
      exact (s.valᶜ.orderEmbOfFin hsc).strictMono⟩⟩

@[simp]
theorem leftPositions_ofLeftPositions
    (s : Set.powersetCard (Fin (p + q)) p) :
    leftPositions (ofLeftPositions s) = s := by
  have hs : s.val.card = p := Set.powersetCard.card_eq s
  apply Subtype.ext
  unfold leftPositions
  rw [Set.powersetCard.val_ofFinEmb]
  simp_rw [ofLeftPositions, Equiv.trans_apply,
    _root_.finSumFinEquiv_symm_apply_castAdd, finSumEquivOfFinset_inl]
  exact Finset.map_orderEmbOfFin_univ s.val hs

@[simp]
theorem ofLeftPositions_leftPositions (s : Shuffle p q) :
    ofLeftPositions (leftPositions s) = s := by
  cases s with
  | mk σ hσ =>
    have hs : (leftPositions ⟨σ, hσ⟩).val.card = p :=
      Set.powersetCard.card_eq _
    have hsc : (leftPositions ⟨σ, hσ⟩).valᶜ.card = q := by
      have hcompl : (leftPositions ⟨σ, hσ⟩).valᶜ.card =
          Fintype.card (Fin (p + q)) -
            (leftPositions ⟨σ, hσ⟩).val.card :=
        Finset.card_compl _
      rw [hcompl, hs, Fintype.card_fin]
      omega
    have hleft : (fun i : Fin p => σ (Fin.castAdd q i)) =
        (leftPositions ⟨σ, hσ⟩).val.orderEmbOfFin hs := by
      apply Finset.orderEmbOfFin_unique hs
      · intro i
        change σ (Fin.castAdd q i) ∈ leftPositions ⟨σ, hσ⟩
        rw [mem_leftPositions_iff]
        exact ⟨i, rfl⟩
      · exact hσ.1
    have hright : (fun j : Fin q => σ (Fin.natAdd p j)) =
        (leftPositions ⟨σ, hσ⟩).valᶜ.orderEmbOfFin hsc := by
      apply Finset.orderEmbOfFin_unique hsc
      · intro j
        rw [Finset.mem_compl]
        change σ (Fin.natAdd p j) ∉ leftPositions ⟨σ, hσ⟩
        have hmem : σ (Fin.natAdd p j) ∈
            (⟨σ, hσ⟩ : Shuffle p q).rightPositions := by
          rw [mem_rightPositions_iff]
          exact ⟨j, rfl⟩
        exact (mem_rightPositions_iff_not_mem_leftPositions _ _).mp hmem
      · exact hσ.2
    have hperm : (ofLeftPositions (leftPositions ⟨σ, hσ⟩)).perm = σ := by
      apply Equiv.ext
      intro x
      obtain ⟨y, rfl⟩ :=
        (_root_.finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)).surjective x
      rcases y with i | j
      · change (ofLeftPositions (leftPositions ⟨σ, hσ⟩)).perm
            (Fin.castAdd q i) = σ (Fin.castAdd q i)
        have h1 : (ofLeftPositions (leftPositions ⟨σ, hσ⟩)).perm
            (Fin.castAdd q i) =
            (leftPositions ⟨σ, hσ⟩).val.orderEmbOfFin hs i := by
          simp only [ofLeftPositions, Equiv.trans_apply,
            _root_.finSumFinEquiv_symm_apply_castAdd,
            finSumEquivOfFinset_inl]
        have h2 : σ (Fin.castAdd q i) =
            (leftPositions ⟨σ, hσ⟩).val.orderEmbOfFin hs i := by
          simp only [← hleft]
        rw [h1, h2]
      · change (ofLeftPositions (leftPositions ⟨σ, hσ⟩)).perm
            (Fin.natAdd p j) = σ (Fin.natAdd p j)
        have h1 : (ofLeftPositions (leftPositions ⟨σ, hσ⟩)).perm
            (Fin.natAdd p j) =
            (leftPositions ⟨σ, hσ⟩).valᶜ.orderEmbOfFin hsc j := by
          simp only [ofLeftPositions, Equiv.trans_apply,
            _root_.finSumFinEquiv_symm_apply_natAdd,
            finSumEquivOfFinset_inr]
        have h2 : σ (Fin.natAdd p j) =
            (leftPositions ⟨σ, hσ⟩).valᶜ.orderEmbOfFin hsc j := by
          simp only [← hright]
        rw [h1, h2]
    cases hof : ofLeftPositions (leftPositions ⟨σ, hσ⟩) with
    | mk τ hτ =>
      have hp : τ = σ := by simpa [hof] using hperm
      subst τ
      rfl

def equivLeftPositions :
    Shuffle p q ≃ Set.powersetCard (Fin (p + q)) p where
  toFun := leftPositions
  invFun := ofLeftPositions
  left_inv := ofLeftPositions_leftPositions
  right_inv := leftPositions_ofLeftPositions

def ofRightPositions (s : Set.powersetCard (Fin (p + q)) q) : Shuffle p q :=
  ofLeftPositions (Set.powersetCard.compl (by simp) s)

@[simp]
theorem rightPositions_ofRightPositions
    (s : Set.powersetCard (Fin (p + q)) q) :
    (ofRightPositions s).rightPositions = s := by
  rw [rightPositions_eq_compl, ofRightPositions,
    leftPositions_ofLeftPositions]
  apply Subtype.ext
  simp only [Set.powersetCard.coe_compl, compl_compl]

@[simp]
theorem ofRightPositions_rightPositions (s : Shuffle p q) :
    ofRightPositions s.rightPositions = s := by
  calc
    ofRightPositions s.rightPositions =
        ofLeftPositions s.leftPositions := by
      unfold ofRightPositions
      apply congrArg ofLeftPositions
      rw [rightPositions_eq_compl]
      apply Subtype.ext
      simp only [Set.powersetCard.coe_compl, compl_compl]
    _ = s := ofLeftPositions_leftPositions s

def equivRightPositions : Shuffle p q ≃ Set.powersetCard (Fin (p + q)) q where
  toFun := rightPositions
  invFun := ofRightPositions
  left_inv := ofRightPositions_rightPositions
  right_inv := rightPositions_ofRightPositions

end Shuffle

end AlgebraicTopology.EilenbergZilber
