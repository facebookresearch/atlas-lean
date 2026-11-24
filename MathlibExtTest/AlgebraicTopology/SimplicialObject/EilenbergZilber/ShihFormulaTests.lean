/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihFormulaRecursion

/-!
# Focused clients for the explicit Shih homotopy formula

These checks evaluate the explicit Eilenberg--Mac Lane homotopy `shihComponent` of
González-Díaz and Real in the lowest degrees. In degree `0` the index type is empty and the
component vanishes. In degree `1` there is exactly one index, with gap `1` and sign `1`. Its
first- and second-factor operators are the distinct degeneracies `σ 0` and `σ 1`, so the
component is the single nonzero term `s₀ ⊗ s₁`. The degree-raising recursion `ShihIndex.succ`
is checked on that index: it flips the sign and adds the initial fixed vertex to both
operators.
-/

@[expose] public section

namespace AlgebraicTopology.EilenbergZilber.ShihFormulaTests

open CategoryTheory MonoidalCategory Simplicial

/-- The unique `(1, 0)`-shuffle. -/
def shuffle₁₀ : Shuffle 1 0 :=
  ⟨1, Subsingleton.strictMono _, Subsingleton.strictMono _⟩

/-- The unique Shih index in degree `1`: `p = 0`, `q = 0`. -/
def i₁ : ShihIndex 1 :=
  ⟨0, ⟨0, by simp⟩, shuffle₁₀⟩

/-- In degree `0` there is no Shih index. -/
instance : IsEmpty (ShihIndex 0) :=
  ⟨fun i ↦ i.p.elim0⟩

/-- Every Shih index in degree `1` is `i₁`. -/
theorem eq_i₁ (i : ShihIndex 1) : i = i₁ := by
  rcases i with ⟨p, q, s⟩
  obtain rfl : p = 0 := Subsingleton.elim _ _
  obtain rfl : q = ⟨0, by simp⟩ := Fin.ext (by have := q.isLt; simp at this; omega)
  obtain rfl : s = shuffle₁₀ := Shuffle.ext (Equiv.ext fun x ↦ Fin.ext (by
    have h₁ := (s.perm x).isLt
    have h₂ := (shuffle₁₀.perm x).isLt
    simp at h₁ h₂
    omega))
  rfl

instance : Unique (ShihIndex 1) := ⟨⟨i₁⟩, eq_i₁⟩

example : Fintype.card (ShihIndex 0) = 0 := Fintype.card_eq_zero
example : Fintype.card (ShihIndex 1) = 1 := Fintype.card_unique

theorem i₁_gap : i₁.gap = 1 := rfl

theorem i₁_sign : i₁.sign = 1 := by
  rw [ShihIndex.sign, i₁_gap]
  change (-1 : ℤ) ^ (1 + 1) * shuffleSignZ shuffle₁₀ = 1
  simp [shuffleSignZ, shuffleSign, shuffle₁₀]

/-- The only left position of the `(1, 0)`-shuffle lies below every positive bound. -/
theorem card_filter_leftPositions (k : ℕ) (hk : 1 ≤ k) :
    (shuffle₁₀.leftPositions.val.filter fun x ↦ x.val < k).card = 1 := by
  rw [Finset.filter_true_of_mem fun x _ ↦ lt_of_lt_of_le x.isLt hk]
  exact shuffle₁₀.leftPositions.property

/-- The `(1, 0)`-shuffle has no right positions. -/
theorem card_filter_rightPositions (k : ℕ) :
    (shuffle₁₀.rightPositions.val.filter fun x ↦ x.val < k).card = 0 :=
  Nat.le_zero.mp
    ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      shuffle₁₀.rightPositions.property)

theorem shuffle₁₀_leftHom_zero : shuffle₁₀.leftHom.toOrderHom 0 = 0 :=
  Fin.ext (by rw [Shuffle.leftHom_val_eq_card_filter_leftPositions]; simp)

theorem shuffle₁₀_leftHom_one : (shuffle₁₀.leftHom.toOrderHom 1).val = 1 := by
  rw [Shuffle.leftHom_val_eq_card_filter_leftPositions]
  exact card_filter_leftPositions 1 le_rfl

/-- The first-factor operator of the degree-`1` index is the degeneracy `σ 0`. -/
theorem i₁_leftHom : i₁.leftHom = SimplexCategory.σ 0 := by
  ext k
  fin_cases k
  · rfl
  · simp [ShihIndex.leftHom, ShihIndex.gap, ShihIndex.suffixInput, SimplexCategory.σ, i₁,
      Fin.predAbove]
    exact shuffle₁₀_leftHom_zero
  · simp [ShihIndex.leftHom, ShihIndex.gap, ShihIndex.suffixInput, SimplexCategory.σ, i₁,
      Fin.predAbove]
    exact shuffle₁₀_leftHom_one

/-- The second-factor operator of the degree-`1` index is the degeneracy `σ 1`. -/
theorem i₁_rightHom : i₁.rightHom = SimplexCategory.σ 1 := by
  ext k
  fin_cases k
  · rfl
  · simp [ShihIndex.rightHom, ShihIndex.gap, ShihIndex.suffixInput, SimplexCategory.σ, i₁,
      Fin.predAbove]
  · simp [ShihIndex.rightHom, ShihIndex.gap, ShihIndex.suffixInput, SimplexCategory.σ, i₁,
      Fin.predAbove]

/-- The two factors receive different operators: the formula is not symmetric. -/
theorem i₁_leftHom_ne_rightHom : i₁.leftHom ≠ i₁.rightHom := by
  rw [i₁_leftHom, i₁_rightHom]
  intro h
  have := congrArg (fun f : ⦋2⦌ ⟶ ⦋1⦌ ↦ (f.toOrderHom 1).val) h
  simp [SimplexCategory.σ, Fin.predAbove] at this

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]

/-- The degree-`0` component of the Shih homotopy vanishes. -/
theorem shihComponent_zero (X Y : SimplicialObject C) : shihComponent X Y 0 = 0 := by
  simp [shihComponent]

/-- The degree-`1` component of the Shih homotopy is `s₀ ⊗ s₁`. -/
theorem shihComponent_one (X Y : SimplicialObject C) :
    shihComponent X Y 1 =
      X.map (SimplexCategory.σ 0).op ⊗ₘ Y.map (SimplexCategory.σ 1).op := by
  rw [shihComponent, Fintype.sum_unique]
  change shihSummand X Y i₁ = _
  rw [shihSummand, i₁_sign, i₁_leftHom, i₁_rightHom, one_smul]

/-- Naturality of the degree-`1` component, read through the explicit formula. -/
example {X X' Y Y' : SimplicialObject C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (X.map (SimplexCategory.σ 0).op ⊗ₘ Y.map (SimplexCategory.σ 1).op) ≫
        (f.app (Opposite.op ⦋1 + 1⦌) ⊗ₘ g.app (Opposite.op ⦋1 + 1⦌)) =
      (f.app (Opposite.op ⦋1⦌) ⊗ₘ g.app (Opposite.op ⦋1⦌)) ≫
        (X'.map (SimplexCategory.σ 0).op ⊗ₘ Y'.map (SimplexCategory.σ 1).op) := by
  simpa only [shihComponent_one] using shihComponent_naturality f g 1

/-- Raising the degree adds one to the gap and flips the sign. -/
example : i₁.succ.gap = 2 ∧ i₁.succ.sign = -1 := by
  simp [i₁_gap, i₁_sign]

/-- Raising the degree derives both operators: they become `σ 1` and `σ 2`. -/
example : i₁.succ.leftHom = derivedSimplexHom (SimplexCategory.σ 0) ∧
    i₁.succ.rightHom = derivedSimplexHom (SimplexCategory.σ 1) := by
  simp [i₁_leftHom, i₁_rightHom]

/-- The raised index has gap greater than one, so lowering it returns `i₁`. -/
example : i₁.succ.pred i₁.succ_gap_gt_one = i₁ := eq_i₁ _

/-- The summand of the raised index is the negative derived summand. -/
example (X Y : SimplicialObject C) :
    shihSummand X Y i₁.succ =
      -(X.map (derivedSimplexHom (SimplexCategory.σ 0)).op ⊗ₘ
        Y.map (derivedSimplexHom (SimplexCategory.σ 1)).op) := by
  rw [shihSummand_succ, derivedShihSummand, i₁_sign, i₁_leftHom, i₁_rightHom, one_smul]

end AlgebraicTopology.EilenbergZilber.ShihFormulaTests
