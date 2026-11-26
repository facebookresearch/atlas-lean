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
# Alternating-face complexes of semisimplicial objects

A semisimplicial object in a category C is a contravariant functor from the category of finite
nonempty ordinals and order-preserving injections. The injection omitting vertex i gives a
face δ_i : X_(n+1) → X_n. These faces obey δ_(j+1) ≫ δ_i = δ_i ≫ δ_j for i ≤ j, with the
indicated finite-index casts.

When C is preadditive, the alternating sum d_(n+1,n) = ∑ i : Fin (n + 2), (−1)^i δ_i defines a
chain complex indexed by ℕ. The face identities imply d_(n+2,n+1) ≫ d_(n+1,n) = 0.
Semisimplicial maps act by their degree components, giving an additive functor to chain
complexes.

See Weibel, *An Introduction to Homological Algebra*, Chapter 8.
-/

-- The differential-square proof follows Mathlib's simplicial alternating-face construction.

@[expose] public section

open Opposite
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Preadditive

open scoped Simplicial

noncomputable section

universe v u

namespace SemiSimplexCategory

/-- For n : ℕ and i : Fin (n + 2), the face δ i : ⦋n⦌ₛ ⟶ ⦋n + 1⦌ₛ is the order-preserving
injection whose image omits vertex i. Under the ordinal hom equivalence it is
Fin.succAboveOrderEmb i. -/
def δ {n : ℕ} (i : Fin (n + 2)) : ⦋n⦌ₛ ⟶ ⦋n + 1⦌ₛ :=
  homEquiv.symm (Fin.succAboveOrderEmb i)

@[simp]
theorem toSimplexCategory_map_δ {n : ℕ} (i : Fin (n + 2)) :
    toSimplexCategory.map (δ i) = SimplexCategory.δ i :=
  rfl

/-- For n : ℕ and i, j : Fin (n + 2) with i ≤ j, the semisimplex face injections satisfy δ i ≫ δ
j.succ = δ j ≫ δ i.castSucc. Both composites are injections ⦋n⦌ₛ ⟶ ⦋n + 2⦌ₛ omitting the same
two vertices. -/
theorem δ_comp_δ {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j) :
    δ i ≫ δ j.succ = δ j ≫ δ i.castSucc := by
  apply toSimplexCategory.map_injective
  simpa only [Functor.map_comp, toSimplexCategory_map_δ, toSimplexCategory_obj] using
    SimplexCategory.δ_comp_δ h

/-- Let n : ℕ, i : Fin (n + 3) and j : Fin (n + 2), with i ≤ Fin.castSucc j. Casting i to Fin (n +
2) using this bound gives δ (i.castLT _) ≫ δ j.succ = δ j ≫ δ i as semisimplex injections ⦋n⦌ₛ
⟶ ⦋n + 2⦌ₛ. -/
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

/-- For a category C, a semisimplicial object is a functor SemiSimplexCategoryᵒᵖ ⥤ C. Its degree-n
term is its value on the opposite ordinal with n + 1 vertices, and its morphisms are natural
transformations. -/
abbrev SemiSimplicialObject :=
  SemiSimplexCategoryᵒᵖ ⥤ C

namespace SemiSimplicialObject

set_option quotPrecheck false in
/- X _⦋n⦌ₛ denotes X evaluated at the opposite ordinal with n + 1 vertices. -/
scoped[Simplicial]
  notation3:1000 X " _⦋" n "⦌ₛ" =>
    (X : CategoryTheory.SemiSimplicialObject _).obj
      (Opposite.op (SemiSimplexCategory.mk n))

variable {C}

/-- For semisimplicial objects X and Y in a category C, two morphisms f, g : X ⟶ Y are equal if
f.app q = g.app q for every q : SemiSimplexCategoryᵒᵖ. Thus equality of all degree components
determines the natural transformation. -/
@[ext]
theorem hom_ext {X Y : SemiSimplicialObject C} (f g : X ⟶ Y)
    (h : ∀ n : SemiSimplexCategoryᵒᵖ, f.app n = g.app n) : f = g :=
  NatTrans.ext (by ext; apply h)

variable (X : SemiSimplicialObject C)

/-- For a semisimplicial object X in a category C, n : ℕ and i : Fin (n + 2), the face X.δ i :
X_(n+1) ⟶ X_n is X.map (SemiSimplexCategory.δ i).op, the image of the injection omitting
vertex i. -/
def δ {n : ℕ} (i : Fin (n + 2)) : X _⦋n + 1⦌ₛ ⟶ X _⦋n⦌ₛ :=
  X.map (SemiSimplexCategory.δ i).op

theorem δ_def {n : ℕ} (i : Fin (n + 2)) :
    X.δ i = X.map (SemiSimplexCategory.δ i).op :=
  rfl

/-- For a semisimplicial object X in a category C, n : ℕ and i, j : Fin (n + 2) with i ≤ j, one
has X.δ j.succ ≫ X.δ i = X.δ i.castSucc ≫ X.δ j. These are morphisms X_(n+2) ⟶ X_n; the order
reverses that of the injection-category face relation. -/
@[reassoc]
theorem δ_comp_δ {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j) :
    X.δ j.succ ≫ X.δ i = X.δ i.castSucc ≫ X.δ j := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SemiSimplexCategory.δ_comp_δ h]

/-- For a semisimplicial object X in a category C, let i : Fin (n + 3) and j : Fin (n + 2) satisfy
i ≤ Fin.castSucc j. Then X.δ j.succ ≫ X.δ (i.castLT _) = X.δ i ≫ X.δ j as morphisms X_(n+2) ⟶
X_n, where the cast to Fin (n + 2) uses the stated bound. -/
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

/-- For a semisimplicial object X in a preadditive category C and n : ℕ, define objD X n : X_(n+1)
⟶ X_n by ∑ i : Fin (n + 2), (−1 : ℤ)^i • X.δ i. The integer scalar multiplication is that of
the additive group of morphisms. -/
@[simp]
def objD (n : ℕ) : X _⦋n + 1⦌ₛ ⟶ X _⦋n⦌ₛ :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.δ i

/-- For a semisimplicial object X in a preadditive category C and every n : ℕ, the alternating
boundaries satisfy objD X (n + 1) ≫ objD X n = 0 as a morphism X_(n+2) ⟶ X_n. Here objD X n =
∑ i : Fin (n + 2), (−1)^i • X.δ i. -/
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

/-- For a semisimplicial object X in a preadditive category C, define the chain complex of shape
down ℕ with term X_n in degree n and differential d_(n+1,n) = ∑ i : Fin (n + 2), (−1)^i • X.δ
i. Its other differentials vanish, and the semisimplicial face identities make successive
boundaries compose to zero. -/
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

/-- For semisimplicial objects X and Y in a preadditive category C, a morphism f : X ⟶ Y induces a
chain map obj X ⟶ obj Y. Its degree-n component is f.app (op ⦋n⦌ₛ); naturality of f with each
face makes it commute with the alternating boundaries. -/
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

/-- For a preadditive category C, the alternating-face construction is a functor
SemiSimplicialObject C ⥤ ChainComplex C ℕ. It sends X to the complex with terms X_n and
boundaries ∑ i : Fin (n + 2), (−1)^i • X.δ i, and sends each natural transformation to the
chain map with its degree components. -/
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
