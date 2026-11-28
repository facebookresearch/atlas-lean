/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.Shuffle
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleCrossing
import Mathlib.Data.Fintype.Fin

/-!
# Unit shuffles

This file identifies the unique shuffles with one empty block and computes
their simplicial maps, signs, summands, and bidegree shuffle maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Simplicial

namespace AlgebraicTopology.EilenbergZilber

namespace Shuffle

variable {p q : ℕ}

def leftUnitShuffle (q : ℕ) : Shuffle 0 q where
  perm := Equiv.refl _
  isShuffle := by
    constructor
    · intro i
      exact Fin.elim0 i
    · simpa using Fin.strictMono_natAdd (m := q) 0

def rightUnitShuffle (p : ℕ) : Shuffle p 0 where
  perm := Equiv.refl _
  isShuffle := by
    constructor
    · intro i j hij
      exact Fin.strictMono_castAdd 0 hij
    · intro i
      exact Fin.elim0 i

theorem subsingleton_left_zero (q : ℕ) : Subsingleton (Shuffle 0 q) := by
  constructor
  intro s t
  apply equivLeftPositions.injective
  apply Subtype.ext
  change s.leftPositions.val = t.leftPositions.val
  rw [Finset.card_eq_zero.mp (Set.powersetCard.card_eq s.leftPositions)]
  rw [Finset.card_eq_zero.mp (Set.powersetCard.card_eq t.leftPositions)]

theorem subsingleton_right_zero (p : ℕ) : Subsingleton (Shuffle p 0) := by
  constructor
  intro s t
  apply equivLeftPositions.injective
  apply Subtype.ext
  change s.leftPositions.val = t.leftPositions.val
  have hs : s.leftPositions.val = Finset.univ := by
    apply s.leftPositions.val.card_eq_iff_eq_univ.mp
    simp only [Set.powersetCard.card_eq, Fintype.card_fin, Nat.add_zero]
  have ht : t.leftPositions.val = Finset.univ := by
    apply t.leftPositions.val.card_eq_iff_eq_univ.mp
    simp only [Set.powersetCard.card_eq, Fintype.card_fin, Nat.add_zero]
  rw [hs, ht]

theorem eq_leftUnitShuffle (s : Shuffle 0 q) : s = leftUnitShuffle q :=
  (subsingleton_left_zero q).elim _ _

theorem eq_rightUnitShuffle (s : Shuffle p 0) : s = rightUnitShuffle p :=
  (subsingleton_right_zero p).elim _ _

@[simp]
theorem leftUnitShuffle_leftHom (q : ℕ) :
    (leftUnitShuffle q).leftHom =
      eqToHom (by simp : ⦋0 + q⦌ = ⦋q⦌) ≫ SimplexCategory.const ⦋q⦌ ⦋0⦌ 0 := by
  ext i
  simp [leftHom, leftUnitShuffle]

@[simp]
theorem leftUnitShuffle_rightHom (q : ℕ) :
    (leftUnitShuffle q).rightHom =
      eqToHom (by simp : ⦋0 + q⦌ = ⦋q⦌) := by
  have hpos : (leftUnitShuffle q).rightPositions.val = Finset.univ := by
    apply (leftUnitShuffle q).rightPositions.val.card_eq_iff_eq_univ.mp
    simp only [Set.powersetCard.card_eq, Fintype.card_fin, Nat.zero_add]
  ext k
  have hle : k.val ≤ 0 + q := Nat.le_of_lt_succ k.isLt
  rw [rightHom_val_eq_card_filter_rightPositions, hpos,
    Fin.card_filter_val_lt, min_eq_right hle]
  simp

@[simp]
theorem rightUnitShuffle_leftHom (p : ℕ) :
    (rightUnitShuffle p).leftHom =
      eqToHom (by simp : ⦋p + 0⦌ = ⦋p⦌) := by
  have hpos : (rightUnitShuffle p).leftPositions.val = Finset.univ := by
    apply (rightUnitShuffle p).leftPositions.val.card_eq_iff_eq_univ.mp
    simp only [Set.powersetCard.card_eq, Fintype.card_fin, Nat.add_zero]
  ext k
  have hle : k.val ≤ p + 0 := Nat.le_of_lt_succ k.isLt
  rw [leftHom_val_eq_card_filter_leftPositions, hpos,
    Fin.card_filter_val_lt, min_eq_right hle]
  simp

@[simp]
theorem rightUnitShuffle_rightHom (p : ℕ) :
    (rightUnitShuffle p).rightHom =
      eqToHom (by simp : ⦋p + 0⦌ = ⦋p⦌) ≫ SimplexCategory.const ⦋p⦌ ⦋0⦌ 0 := by
  ext i
  simp [rightHom, rightUnitShuffle]

@[simp]
theorem leftUnitShuffle_sign (q : ℕ) : shuffleSignZ (leftUnitShuffle q) = 1 := by
  simp [shuffleSignZ, shuffleSign, leftUnitShuffle]

@[simp]
theorem rightUnitShuffle_sign (p : ℕ) : shuffleSignZ (rightUnitShuffle p) = 1 := by
  simp [shuffleSignZ, shuffleSign, rightUnitShuffle]

noncomputable local instance leftZeroUnique (q : ℕ) : Unique (Shuffle 0 q) where
  default := leftUnitShuffle q
  uniq := fun s => eq_leftUnitShuffle s

noncomputable local instance rightZeroUnique (p : ℕ) : Unique (Shuffle p 0) where
  default := rightUnitShuffle p
  uniq := fun s => eq_rightUnitShuffle s

end Shuffle

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]

theorem shuffleBidegree_left_zero_eq_summand (X Y : SimplicialObject C) (q : ℕ) :
    shuffleBidegree X Y 0 q = shuffleSummand X Y (Shuffle.leftUnitShuffle q) := by
  let _ := Shuffle.leftZeroUnique q
  rw [shuffleBidegree, Fintype.sum_unique]
  rw [Shuffle.eq_leftUnitShuffle (q := q) (default : Shuffle 0 q)]

theorem shuffleBidegree_right_zero_eq_summand (X Y : SimplicialObject C) (p : ℕ) :
    shuffleBidegree X Y p 0 = shuffleSummand X Y (Shuffle.rightUnitShuffle p) := by
  let _ := Shuffle.rightZeroUnique p
  rw [shuffleBidegree, Fintype.sum_unique]
  rw [Shuffle.eq_rightUnitShuffle (p := p) (default : Shuffle p 0)]

theorem shuffleSummand_leftUnitShuffle (X : SimplicialObject C) (q : ℕ) :
    shuffleSummand (𝟙_ (SimplicialObject C)) X (Shuffle.leftUnitShuffle q) =
      (𝟙 (𝟙_ C) ⊗ₘ X.map
        (eqToHom (by simp : ⦋0 + q⦌ = ⦋q⦌)).op) := by
  simp [shuffleSummand, Shuffle.leftUnitShuffle_leftHom,
    Shuffle.leftUnitShuffle_rightHom]

theorem shuffleSummand_rightUnitShuffle (X : SimplicialObject C) (p : ℕ) :
    shuffleSummand X (𝟙_ (SimplicialObject C)) (Shuffle.rightUnitShuffle p) =
      (X.map (eqToHom (by simp : ⦋p + 0⦌ = ⦋p⦌)).op ⊗ₘ 𝟙 (𝟙_ C)) := by
  simp [shuffleSummand, Shuffle.rightUnitShuffle_leftHom,
    Shuffle.rightUnitShuffle_rightHom]

theorem shuffleBidegree_left_unit (X : SimplicialObject C) (q : ℕ) :
    shuffleBidegree (𝟙_ (SimplicialObject C)) X 0 q =
      (𝟙 (𝟙_ C) ⊗ₘ X.map
        (eqToHom (by simp : ⦋0 + q⦌ = ⦋q⦌)).op) := by
  rw [shuffleBidegree_left_zero_eq_summand, shuffleSummand_leftUnitShuffle]

theorem shuffleBidegree_right_unit (X : SimplicialObject C) (p : ℕ) :
    shuffleBidegree X (𝟙_ (SimplicialObject C)) p 0 =
      (X.map (eqToHom (by simp : ⦋p + 0⦌ = ⦋p⦌)).op ⊗ₘ 𝟙 (𝟙_ C)) := by
  rw [shuffleBidegree_right_zero_eq_summand, shuffleSummand_rightUnitShuffle]

end AlgebraicTopology.EilenbergZilber
