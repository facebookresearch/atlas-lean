/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Copyright (c) 2026. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.Basic
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShufflePosition

@[expose] public section

noncomputable section

open CategoryTheory

open scoped BigOperators MonoidalCategory Simplicial

namespace AlgebraicTopology.EilenbergZilber

universe v u

namespace Shuffle

@[ext]
theorem ext {p q : ℕ} {s t : Shuffle p q}
    (h : s.perm = t.perm) : s = t := by
  cases s
  cases t
  subst h
  rfl

instance (p q : ℕ) : Finite (Shuffle p q) :=
  Finite.of_injective Shuffle.perm (fun _ _ h ↦ ext h)

noncomputable instance (p q : ℕ) : Fintype (Shuffle p q) :=
  Fintype.ofFinite _

def leftHom {p q : ℕ} (s : Shuffle p q) : ⦋p + q⦌ ⟶ ⦋p⦌ :=
  SimplexCategory.mkHom
    { toFun := fun k =>
        ⟨(s.leftPositions.val.filter fun x => x.val < k.val).card, by
          apply Nat.lt_succ_of_le
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
            s.leftPositions.property⟩
      monotone' := by
        intro a b hab
        change (s.leftPositions.val.filter fun x => x.val < a.val).card ≤
          (s.leftPositions.val.filter fun x => x.val < b.val).card
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, lt_of_lt_of_le hx.2 (Fin.le_iff_val_le_val.mp hab)⟩ }

def rightHom {p q : ℕ} (s : Shuffle p q) : ⦋p + q⦌ ⟶ ⦋q⦌ :=
  SimplexCategory.mkHom
    { toFun := fun k =>
        ⟨(s.rightPositions.val.filter fun x => x.val < k.val).card, by
          apply Nat.lt_succ_of_le
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
            s.rightPositions.property⟩
      monotone' := by
        intro a b hab
        change (s.rightPositions.val.filter fun x => x.val < a.val).card ≤
          (s.rightPositions.val.filter fun x => x.val < b.val).card
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, lt_of_lt_of_le hx.2 (Fin.le_iff_val_le_val.mp hab)⟩ }

theorem leftHom_val_eq_card_filter_leftPositions {p q : ℕ}
    (s : Shuffle p q) (k : Fin (p + q + 1)) :
    (s.leftHom.toOrderHom k).val =
      (s.leftPositions.val.filter (fun x ↦ x.val < k.val)).card :=
  rfl

theorem rightHom_val_eq_card_filter_rightPositions {p q : ℕ}
    (s : Shuffle p q) (k : Fin (p + q + 1)) :
    (s.rightHom.toOrderHom k).val =
      (s.rightPositions.val.filter (fun x ↦ x.val < k.val)).card :=
  rfl

end Shuffle

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]

noncomputable def shuffleSummand (X Y : SimplicialObject C)
    {p q : ℕ} (s : Shuffle p q) :
    X.obj (Opposite.op ⦋p⦌) ⊗ Y.obj (Opposite.op ⦋q⦌) ⟶
      (X ⊗ Y).obj (Opposite.op ⦋p + q⦌) :=
  shuffleSignZ s • (X.map s.leftHom.op ⊗ₘ Y.map s.rightHom.op)

noncomputable def shuffleBidegree (X Y : SimplicialObject C) (p q : ℕ) :
    X.obj (Opposite.op ⦋p⦌) ⊗ Y.obj (Opposite.op ⦋q⦌) ⟶
      (X ⊗ Y).obj (Opposite.op ⦋p + q⦌) :=
  ∑ s : Shuffle p q, shuffleSummand X Y s

@[reassoc]
theorem shuffleSummand_naturality {X X₂ Y Y₂ : SimplicialObject C}
    (f : X ⟶ X₂) (g : Y ⟶ Y₂) {p q : ℕ} (s : Shuffle p q) :
    shuffleSummand X Y s ≫ (f ⊗ₘ g).app (Opposite.op ⦋p + q⦌) =
      (f.app (Opposite.op ⦋p⦌) ⊗ₘ g.app (Opposite.op ⦋q⦌)) ≫
        shuffleSummand X₂ Y₂ s := by
  simp only [shuffleSummand, Monoidal.tensorObj_obj, Monoidal.tensorHom_app]
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom]
  rw [f.naturality, g.naturality]

@[reassoc]
theorem shuffleBidegree_naturality {X X₂ Y Y₂ : SimplicialObject C}
    (f : X ⟶ X₂) (g : Y ⟶ Y₂) (p q : ℕ) :
    shuffleBidegree X Y p q ≫ (f ⊗ₘ g).app (Opposite.op ⦋p + q⦌) =
      (f.app (Opposite.op ⦋p⦌) ⊗ₘ g.app (Opposite.op ⦋q⦌)) ≫
        shuffleBidegree X₂ Y₂ p q := by
  simp only [shuffleBidegree, Preadditive.sum_comp, Preadditive.comp_sum]
  exact Finset.sum_congr rfl fun s _ => shuffleSummand_naturality f g s

end AlgebraicTopology.EilenbergZilber
