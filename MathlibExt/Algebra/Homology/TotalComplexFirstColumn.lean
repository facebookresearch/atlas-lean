/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.TotalComplex

/-!
# The first column of a natural bicomplex maps to its total complex

The horizontal differential leaving column zero vanishes by the complex
shape. The vertical totalization sign on that column is one. Thus its actual
coprojections assemble into a chain map, natural in the original bicomplex.
The object construction needs only its total complex to exist.
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

/-- On the first column, the actual total differential is its vertical differential. -/
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

/-- The native first-column coprojections form a chain map to the total complex. -/
def firstColumnTotalInclusion : B.X 0 ⟶ B.total c :=
  ChainComplex.ofHom (fun n => B.ιTotal c 0 n n (Nat.zero_add n))
    (fun n => ιTotal_firstColumn_d B n)

/-- Every component is the original total coprojection of the first column. -/
lemma firstColumnTotalInclusion_f (n : ℕ) :
    (firstColumnTotalInclusion B).f n = B.ιTotal c 0 n n (Nat.zero_add n) := rfl

end Object

/-- An original bicomplex map commutes with the canonical first-column inclusion. -/
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

/-- The first-column inclusions form a natural transformation whenever the total functor exists. -/
def firstColumnTotalNatTrans :
    HomologicalComplex.eval (ChainComplex C ℕ) c 0 ⟶ totalFunctor C c c c where
  app B := firstColumnTotalInclusion B
  naturality _ _ φ := (firstColumnTotalInclusion_naturality φ).symm

/-- The functorial comparison uses the same objectwise canonical chain map. -/
lemma firstColumnTotalNatTrans_app (B : HomologicalComplex₂ C c c) :
    (firstColumnTotalNatTrans (C := C)).app B = firstColumnTotalInclusion B := rfl

end Functor

end HomologicalComplex₂
