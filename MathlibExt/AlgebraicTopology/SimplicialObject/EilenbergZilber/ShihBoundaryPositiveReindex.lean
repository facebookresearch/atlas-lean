/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryPositivePartition

/-!
# Canonical coordinates for the residual positive Shih boundary

This file is purely combinatorial.  It reindexes the transition and active
upper strata and the left and right lower strata without mentioning a target
category.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlgebraicTopology.EilenbergZilber

/-- An active upper coordinate is a Shih index together with a local face of
its shuffle block. -/
def ShihUpperActiveData (n : ℕ) :=
  Σ i : ShihIndex (n + 1), Fin (i.p + 1 + i.q + 1)

noncomputable instance (n : ℕ) : Fintype (ShihUpperActiveData n) := by
  unfold ShihUpperActiveData
  infer_instance

/-- A lower left coordinate is a Shih index together with an interior left
insertion. -/
def ShihLowerLeftData (n : ℕ) :=
  Σ i : ShihIndex n, {a : Fin (i.p + 3) // 0 < a.val ∧ a.val < i.p + 2}

noncomputable instance (n : ℕ) : Fintype (ShihLowerLeftData n) := by
  unfold ShihLowerLeftData
  infer_instance

/-- A lower right coordinate is a Shih index together with a positive right
insertion. -/
def ShihLowerRightData (n : ℕ) :=
  Σ i : ShihIndex n, {b : Fin (i.q + 2) // 0 < b.val}

noncomputable instance (n : ℕ) : Fintype (ShihLowerRightData n) := by
  unfold ShihLowerRightData
  infer_instance

/-- Transition residuals are exactly degree-`n` Shih indices, with one extra
inactive prefix vertex. -/
def shihUpperPositiveTransitionEquiv (n : ℕ) :
    ShihUpperPositiveTransitionIndex n ≃ ShihIndex n where
  toFun z := z.val.val.1.lowerPrefix (by
    have ht := z.property
    change z.val.val.2.val + 2 = z.val.val.1.gap at ht
    omega)
  invFun i := by
    let k : Fin (n + 2) := ⟨i.gap - 1, by
      have hg := i.gap_pos
      have hs := i.p_add_q_add_gap
      omega⟩
    refine ⟨⟨⟨i.raisePrefix, k⟩, ?_⟩, ?_⟩
    · change ¬k.val + 2 < i.raisePrefix.gap
      have hg := i.gap_pos
      rw [i.gap_raisePrefix]
      simp only [k]
      omega
    · change k.val + 2 = i.raisePrefix.gap
      have hg := i.gap_pos
      rw [i.gap_raisePrefix]
      simp only [k]
      omega
  left_inv z := by
    rcases z with ⟨⟨⟨i, k⟩, hr⟩, ht⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change ((i.lowerPrefix _).gap - 1) = k.val
      have hgt : 1 < i.gap := by
        change k.val + 2 = i.gap at ht
        omega
      have hg := i.gap_lowerPrefix hgt
      change k.val + 2 = i.gap at ht
      omega
  right_inv i := by
    rfl

/-- Active residuals are exactly an upper Shih index and a local active face. -/
def shihUpperPositiveActiveEquiv (n : ℕ) :
    ShihUpperPositiveActiveIndex n ≃ ShihUpperActiveData n where
  toFun z := ⟨z.val.val.1, z.localFace⟩
  invFun z := by
    let k : Fin (n + 2) := ⟨z.1.gap + z.2.val - 1, by
      have hg := z.1.gap_pos
      have hs := z.1.p_add_q_add_gap
      have hr := z.2.isLt
      omega⟩
    refine ⟨⟨⟨z.1, k⟩, ?_⟩, ?_⟩
    · change ¬k.val + 2 < z.1.gap
      have hg := z.1.gap_pos
      simp only [k]
      omega
    · change z.1.gap ≤ k.val + 1
      have hg := z.1.gap_pos
      simp only [k]
      omega
  left_inv z := by
    rcases z with ⟨⟨⟨i, k⟩, hr⟩, ha⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp only [ShihUpperPositiveActiveIndex.localFace]
      change i.gap + (k.val + 1 - i.gap) - 1 = k.val
      change i.gap ≤ k.val + 1 at ha
      omega
  right_inv z := by
    rcases z with ⟨i, r⟩
    change (⟨i, _⟩ : ShihUpperActiveData n) = ⟨i, r⟩
    congr 1
    apply Fin.ext
    simp only [ShihUpperPositiveActiveIndex.localFace]
    change i.gap + r.val - 1 + 1 - i.gap = r.val
    have hg := i.gap_pos
    omega

/-- Lower left residuals are exactly interior inserted-left data. -/
def shihLowerPositiveLeftEquiv (n : ℕ) :
    ShihLowerPositiveLeftIndex n ≃ ShihLowerLeftData n where
  toFun z := ⟨z.val.val.1,
    ⟨z.insertion, z.insertion_pos, z.insertion_lt_last⟩⟩
  invFun z := by
    let k : Fin (n + 1) := ⟨z.1.gap - 1 + z.2.val.val - 1, by
      have hs := z.1.p_add_q_add_gap
      have ha := z.2.val.isLt
      omega⟩
    refine ⟨⟨⟨z.1, k⟩, ?_⟩, ?_⟩
    · change ¬k.val + 1 < z.1.gap
      have hg := z.1.gap_pos
      have ha := z.2.property.1
      simp only [k]
      omega
    · change k.succ.val ≤ z.1.gap + z.1.p
      have hg := z.1.gap_pos
      have ha := z.2.property.2
      simp only [Fin.val_succ, k]
      omega
  left_inv z := by
    rcases z with ⟨⟨⟨i, k⟩, hr⟩, hl⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp only [ShihLowerPositiveLeftIndex.insertion]
      change i.gap - 1 + (k.val + 1 - (i.gap - 1)) - 1 = k.val
      change ¬k.val + 1 < i.gap at hr
      omega
  right_inv z := by
    rcases z with ⟨i, a⟩
    change (⟨i, _⟩ : ShihLowerLeftData n) = ⟨i, a⟩
    congr 1
    apply Subtype.ext
    apply Fin.ext
    simp only [ShihLowerPositiveLeftIndex.insertion]
    change i.gap - 1 + a.val - 1 + 1 - (i.gap - 1) = a.val
    have hg := i.gap_pos
    have ha := a.property.1
    omega

/-- Lower right residuals are exactly positive inserted-right data. -/
def shihLowerPositiveRightEquiv (n : ℕ) :
    ShihLowerPositiveRightIndex n ≃ ShihLowerRightData n where
  toFun z := ⟨z.val.val.1, ⟨z.insertion, z.insertion_pos⟩⟩
  invFun z := by
    let k : Fin (n + 1) := ⟨z.1.gap + z.1.p + z.2.val.val - 1, by
      have hs := z.1.p_add_q_add_gap
      have hb := z.2.val.isLt
      omega⟩
    refine ⟨⟨⟨z.1, k⟩, ?_⟩, ?_⟩
    · change ¬k.val + 1 < z.1.gap
      have hb := z.2.property
      simp only [k]
      omega
    · change z.1.gap + z.1.p < k.succ.val
      have hb := z.2.property
      simp only [Fin.val_succ, k]
      omega
  left_inv z := by
    rcases z with ⟨⟨⟨i, k⟩, hr⟩, hright⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp only [ShihLowerPositiveRightIndex.insertion]
      change i.gap + i.p + (k.val + 1 - (i.gap + i.p)) - 1 = k.val
      change i.gap + i.p < k.val + 1 at hright
      omega
  right_inv z := by
    rcases z with ⟨i, b⟩
    change (⟨i, _⟩ : ShihLowerRightData n) = ⟨i, b⟩
    congr 1
    apply Subtype.ext
    apply Fin.ext
    simp only [ShihLowerPositiveRightIndex.insertion]
    change i.gap + i.p + b.val - 1 + 1 - (i.gap + i.p) = b.val
    have hb := b.property
    omega

end AlgebraicTopology.EilenbergZilber
