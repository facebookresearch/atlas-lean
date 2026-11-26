/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.TotalComplex

/-!
# The first column maps to the total of a nonnegative bicomplex

For a bicomplex B of shape (down ℕ, down ℕ) in a preadditive category, assume that its total
complex exists. The coprojections B_(0,n) → Tot(B)_n assemble into a chain map from the first
column B.X 0 to Tot(B).

The horizontal differential out of column zero is zero, and the sign on the vertical
differential in that column is (−1)^0 = 1. The first-column map is natural in bicomplex
morphisms. If all such bicomplexes have totals, these maps form a natural transformation from
first-column evaluation to totalization.
-/

@[expose] public section
noncomputable section

open CategoryTheory Category Limits

namespace HomologicalComplex₂

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]

local notation "c" => ComplexShape.down ℕ

section Object

variable (B : HomologicalComplex₂ C c c) [B.HasTotal c]

/-- In a preadditive category C, let B be a bicomplex of shape (down ℕ, down ℕ) whose total
complex for down ℕ exists. For n : ℕ, the total coprojections satisfy ι_(0,n+1) ≫ d_Tot(n+1,n)
= d_(B.X 0)(n+1,n) ≫ ι_(0,n). The horizontal contribution vanishes and the vertical
totalization sign in column zero is 1. -/
@[reassoc]
lemma ιTotal_firstColumn_d (n : ℕ) :
    B.ιTotal c 0 (n + 1) (n + 1) (Nat.zero_add (n + 1)) ≫
        (B.total c).d (n + 1) n =
      (B.X 0).d (n + 1) n ≫ B.ιTotal c 0 n n (Nat.zero_add n) := by
  have hε : ComplexShape.ε₂ c c c (0, n + 1) = 1 := rfl
  change B.ιTotal c 0 (n + 1) (n + 1) (Nat.zero_add (n + 1)) ≫
    (B.D₁ c (n + 1) n + B.D₂ c (n + 1) n) = _
  rw [Preadditive.comp_add, B.ι_D₁, B.ι_D₂,
    B.d₁_eq_zero c 0 (n + 1) n (by simp [ComplexShape.down_Rel]), zero_add,
    B.d₂_eq c 0 (show (c).Rel (n + 1) n from rfl) n (Nat.zero_add n),
    hε, one_smul]

/-- In a preadditive category C, let B be a bicomplex of shape (down ℕ, down ℕ) whose total
complex for down ℕ exists. Define firstColumnTotalInclusion B : B.X 0 ⟶ B.total (down ℕ) to
have degree-n component B.ιTotal (down ℕ) 0 n n (Nat.zero_add n), the total coprojection from
bidegree (0, n). -/
def firstColumnTotalInclusion : B.X 0 ⟶ B.total c :=
  ChainComplex.ofHom (fun n => B.ιTotal c 0 n n (Nat.zero_add n))
    (fun n => ιTotal_firstColumn_d B n)

/-- In a preadditive category C, let B be a bicomplex of shape (down ℕ, down ℕ) whose total
complex for down ℕ exists. For every n : ℕ, (firstColumnTotalInclusion B).f n equals B.ιTotal
(down ℕ) 0 n n (Nat.zero_add n). -/
lemma firstColumnTotalInclusion_f (n : ℕ) :
    (firstColumnTotalInclusion B).f n = B.ιTotal c 0 n n (Nat.zero_add n) := rfl

end Object

/-- In a preadditive category C, let φ : B ⟶ B' be a map of bicomplexes of shape (down ℕ, down ℕ),
and assume both total complexes exist. Then firstColumnTotalInclusion B ≫ total.map φ (down ℕ)
= φ.f 0 ≫ firstColumnTotalInclusion B' as chain maps B.X 0 ⟶ Tot(B'). -/
@[reassoc]
lemma firstColumnTotalInclusion_naturality
    {B B' : HomologicalComplex₂ C c c} [B.HasTotal c] [B'.HasTotal c] (φ : B ⟶ B') :
    firstColumnTotalInclusion B ≫ total.map φ c =
      φ.f 0 ≫ firstColumnTotalInclusion B' := by
  apply HomologicalComplex.hom_ext
  intro n
  change B.ιTotal c 0 n n (Nat.zero_add n) ≫ (total.map φ c).f n =
    (φ.f 0).f n ≫ B'.ιTotal c 0 n n (Nat.zero_add n)
  exact ιTotal_map B B' φ c 0 n n (Nat.zero_add n)

section Functor

variable [∀ B : HomologicalComplex₂ C c c, B.HasTotal c]

/-- Let C be preadditive and assume every bicomplex of shape (down ℕ, down ℕ) has a total complex
of shape down ℕ. The first-column total inclusions define a natural transformation from
HomologicalComplex.eval (ChainComplex C ℕ) (down ℕ) 0 to the total functor, with component B.X
0 ⟶ Tot(B) at B. -/
def firstColumnTotalNatTrans :
    HomologicalComplex.eval (ChainComplex C ℕ) c 0 ⟶ totalFunctor C c c c where
  app B := firstColumnTotalInclusion B
  naturality _ _ φ := (firstColumnTotalInclusion_naturality φ).symm

/-- Let C be preadditive and assume every bicomplex of shape (down ℕ, down ℕ) has its down-ℕ
total. For every such B, the component of firstColumnTotalNatTrans at B is
firstColumnTotalInclusion B, whose degree-n map is the coprojection from B_(0,n) to Tot(B)_n. -/
lemma firstColumnTotalNatTrans_app (B : HomologicalComplex₂ C c c) :
    (firstColumnTotalNatTrans (C := C)).app B = firstColumnTotalInclusion B := rfl

end Functor

end HomologicalComplex₂
