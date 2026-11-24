/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory

/-!
# The alternating face map complex of a semisimplicial object

We define semisimplicial objects as contravariant functors from the native
`SemiSimplexCategory`, construct their face maps, and prove the face identities.
For a semisimplicial object in a preadditive category, we then construct the
chain complex whose differential is the alternating sum of its faces.

The proof that the differential squares to zero is adapted from the native
Mathlib construction for simplicial objects in
`Mathlib.AlgebraicTopology.AlternatingFaceMapComplex`.
-/

@[expose] public section

open Opposite
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Preadditive

open scoped Simplicial

noncomputable section

universe v u

namespace SemiSimplexCategory

/-- The `i`-th face map from `⦋n⦌ₛ` to `⦋n+1⦌ₛ`. -/
def δ {n : ℕ} (i : Fin (n + 2)) : ⦋n⦌ₛ ⟶ ⦋n + 1⦌ₛ :=
  homEquiv.symm (Fin.succAboveOrderEmb i)

@[simp]
theorem toSimplexCategory_map_δ {n : ℕ} (i : Fin (n + 2)) :
    toSimplexCategory.map (δ i) = SimplexCategory.δ i :=
  rfl

/-- The generic semisimplicial face identity. -/
theorem δ_comp_δ {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j) :
    δ i ≫ δ j.succ = δ j ≫ δ i.castSucc := by
  apply toSimplexCategory.map_injective
  simpa only [Functor.map_comp, toSimplexCategory_map_δ, toSimplexCategory_obj] using
    SimplexCategory.δ_comp_δ h

/-- A form of the semisimplicial face identity adapted to alternating sums. -/
theorem δ_comp_δ'' {n : ℕ} {i : Fin (n + 3)} {j : Fin (n + 2)}
    (h : i ≤ Fin.castSucc j) :
    δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp h) j.is_lt)) ≫
        δ j.succ =
      δ j ≫ δ i := by
  apply toSimplexCategory.map_injective
  simpa only [Functor.map_comp, toSimplexCategory_map_δ, toSimplexCategory_obj] using
    SimplexCategory.δ_comp_δ'' h

end SemiSimplexCategory

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- The category of semisimplicial objects valued in `C`. -/
abbrev SemiSimplicialObject :=
  SemiSimplexCategoryᵒᵖ ⥤ C

namespace SemiSimplicialObject

set_option quotPrecheck false in
/-- `X _⦋n⦌ₛ` denotes the degree-`n` term of a semisimplicial object. -/
scoped[Simplicial]
  notation3:1000 X " _⦋" n "⦌ₛ" =>
    (X : CategoryTheory.SemiSimplicialObject _).obj
      (Opposite.op (SemiSimplexCategory.mk n))

variable {C}

@[ext]
theorem hom_ext {X Y : SemiSimplicialObject C} (f g : X ⟶ Y)
    (h : ∀ n : SemiSimplexCategoryᵒᵖ, f.app n = g.app n) : f = g :=
  NatTrans.ext (by ext; apply h)

variable (X : SemiSimplicialObject C)

/-- The `i`-th face map of a semisimplicial object. -/
def δ {n : ℕ} (i : Fin (n + 2)) : X _⦋n + 1⦌ₛ ⟶ X _⦋n⦌ₛ :=
  X.map (SemiSimplexCategory.δ i).op

theorem δ_def {n : ℕ} (i : Fin (n + 2)) :
    X.δ i = X.map (SemiSimplexCategory.δ i).op :=
  rfl

/-- The generic face identity for a semisimplicial object. -/
@[reassoc]
theorem δ_comp_δ {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j) :
    X.δ j.succ ≫ X.δ i = X.δ i.castSucc ≫ X.δ j := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SemiSimplexCategory.δ_comp_δ h]

/-- A form of the face identity adapted to alternating sums. -/
@[reassoc]
theorem δ_comp_δ'' {n : ℕ} {i : Fin (n + 3)} {j : Fin (n + 2)}
    (h : i ≤ Fin.castSucc j) :
    X.δ j.succ ≫
        X.δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp h) j.is_lt)) =
      X.δ i ≫ X.δ j := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SemiSimplexCategory.δ_comp_δ'' h]

end SemiSimplicialObject

end CategoryTheory

namespace AlgebraicTopology

namespace SemiSimplicialAlternatingFaceMapComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (X Y : SemiSimplicialObject C)

/-- The alternating sum of the face maps in adjacent degrees. -/
@[simp]
def objD (n : ℕ) : X _⦋n + 1⦌ₛ ⟶ X _⦋n⦌ₛ :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.δ i

/-- The alternating face differential squares to zero.

This proof follows Mathlib's native simplicial alternating-face proof: expand
the composite as a double sum and pair the two regions by `(i, j) ↦ (j, i+1)`.
Only the semisimplicial face identity is used. -/
theorem d_squared (n : ℕ) : objD X (n + 1) ≫ objD X n = 0 := by
  dsimp
  simp only [comp_sum, sum_comp, ← Finset.sum_product']
  let P := Fin (n + 2) × Fin (n + 3)
  let S : Finset P := {ij : P | (ij.2 : ℕ) ≤ (ij.1 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.1)),
      ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    lia
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using! congr_arg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using!
        congr_arg Fin.castSucc (congr_arg Prod.fst h)⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred <| ?_, Fin.castSucc i'), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij'
    · simpa [S] using! Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    dsimp
    simp only [zsmul_comp, comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, pow_add, pow_one, mul_neg, neg_neg, mul_one]
      apply mul_comm
    · dsimp [φ]
      rw [SemiSimplicialObject.δ_comp_δ'' X (by simpa [S] using! hij)]

/-- The alternating face map complex of a semisimplicial object. -/
@[implicit_reducible]
def obj : ChainComplex C ℕ :=
  ChainComplex.of (fun n => X _⦋n⦌ₛ) (objD X) (d_squared X)

@[simp]
theorem obj_X (X : SemiSimplicialObject C) (n : ℕ) :
    (obj X).X n = X _⦋n⦌ₛ :=
  rfl

@[simp]
theorem obj_d (X : SemiSimplicialObject C) (n : ℕ) :
    (obj X).d (n + 1) n = objD X n := by
  simp [obj]

variable {X Y}

/-- A morphism of semisimplicial objects induces a chain map. -/
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  ChainComplex.ofHom (fun n => f.app (op ⦋n⦌ₛ)) fun n => by
    simp only [obj, ChainComplex.of_d, objD, Int.reduceNeg]
    rw [comp_sum, sum_comp]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [comp_zsmul, zsmul_comp]
    congr 1
    symm
    apply f.naturality

@[simp]
theorem map_f (f : X ⟶ Y) (n : ℕ) :
    (map f).f n = f.app (op ⦋n⦌ₛ) :=
  rfl

end SemiSimplicialAlternatingFaceMapComplex

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- The alternating face map complex functor for semisimplicial objects. -/
@[implicit_reducible]
def semiSimplicialAlternatingFaceMapComplex :
    SemiSimplicialObject C ⥤ ChainComplex C ℕ where
  obj := SemiSimplicialAlternatingFaceMapComplex.obj
  map f := SemiSimplicialAlternatingFaceMapComplex.map f

variable {C}

@[simp]
theorem semiSimplicialAlternatingFaceMapComplex_obj_X
    (X : SemiSimplicialObject C) (n : ℕ) :
    ((semiSimplicialAlternatingFaceMapComplex C).obj X).X n = X _⦋n⦌ₛ :=
  rfl

@[simp]
theorem semiSimplicialAlternatingFaceMapComplex_obj_d
    (X : SemiSimplicialObject C) (n : ℕ) :
    ((semiSimplicialAlternatingFaceMapComplex C).obj X).d (n + 1) n =
      SemiSimplicialAlternatingFaceMapComplex.objD X n := by
  simp [semiSimplicialAlternatingFaceMapComplex]

@[simp]
theorem semiSimplicialAlternatingFaceMapComplex_map_f
    {X Y : SemiSimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    ((semiSimplicialAlternatingFaceMapComplex C).map f).f n =
      f.app (op ⦋n⦌ₛ) :=
  rfl

instance : (semiSimplicialAlternatingFaceMapComplex C).Additive where

end AlgebraicTopology
