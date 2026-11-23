/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
See NOTICE in the repository root for the original Mathlib attribution.
-/

module

-- BACKPORT: Point-simplex unitor APIs from Mathlib PR #42435,
-- head `e09070f786c9fc0a688e6239d71230b618b045ff`,
-- `Mathlib/AlgebraicTopology/SimplicialSet/Monoidal.lean`,
-- blob `e66f43d9ce20ad5311ee1c898a58da4639a5d7e9`.
-- Current-pin comparison and removal conditions: `BACKPORTS.md`.

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Cartesian unitors at the point simplex

The point simplex gives explicit left and right Cartesian unitors on every simplicial set. Their
projection, naturality and endpoint equations retain the chosen point, the original maps and
both interval faces. These twelve point-simplex helpers extend the pinned Cartesian monoidal
structure.

The compatibility scope against Mathlib 4.35.0 (`56a005855ea17e0b0958f73ec801ae140b0a1679`) and
its removal conditions are recorded in `BACKPORTS.md`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits Simplicial
open scoped Simplicial

namespace SSet

namespace stdSimplex

variable (X Y : SSet.{u})

/-- The isomorphism `Δ[0] ⊗ X ≅ X`. -/
def leftUnitor : Δ[0] ⊗ X ≅ X where
  hom := snd _ _
  inv := lift (isTerminalObj₀.from _) (𝟙 X)

@[reassoc]
lemma _root_.SSet.ι₀_stdSimplex_zero :
    ι₀ = stdSimplex.δ 1 ≫ (stdSimplex.leftUnitor Δ[1]).inv := by
  ext : 1
  all_goals exact yonedaEquiv.injective (by ext i; fin_cases i; rfl)

@[reassoc]
lemma _root_.SSet.ι₁_stdSimplex_zero :
    ι₁ = stdSimplex.δ 0 ≫ (stdSimplex.leftUnitor Δ[1]).inv := by
  ext : 1
  all_goals exact yonedaEquiv.injective (by ext i; fin_cases i; rfl)

/-- The isomorphism `X ⊗ Δ[0] ≅ X`. -/
def rightUnitor : X ⊗ Δ[0] ≅ X where
  hom := fst _ _
  inv := lift (𝟙 X) (isTerminalObj₀.from _)

@[reassoc (attr := simp)]
lemma rightUnitor_inv_fst : (rightUnitor X).inv ≫ fst _ _ = 𝟙 _ := rfl

@[reassoc (attr := simp)]
lemma fst_rightUnitor_inv : fst _ _ ≫ (rightUnitor X).inv = 𝟙 _ := by
  rw [← cancel_epi (rightUnitor X).inv,
    rightUnitor_inv_fst_assoc, Category.comp_id]

variable {X} in
@[reassoc (attr := simp)]
lemma rightUnitor_inv_naturality (f : X ⟶ Y) :
    (rightUnitor X).inv ≫ f ▷ _ = f ≫ (rightUnitor Y).inv := rfl

variable {X} in
@[reassoc (attr := simp)]
lemma rightUnitor_hom_naturality (f : X ⟶ Y) :
    f ▷ _ ≫  (rightUnitor Y).hom = (rightUnitor X).hom ≫ f := rfl

@[reassoc (attr := simp)]
lemma rightUnitor_inv_map_δ_zero :
    (stdSimplex.rightUnitor X).inv ≫ X ◁ stdSimplex.δ 0 =
      ι₁ := rfl

@[reassoc (attr := simp)]
lemma rightUnitor_inv_map_δ_one :
    (stdSimplex.rightUnitor X).inv ≫ X ◁ stdSimplex.δ 1 =
      ι₀ := rfl

@[reassoc (attr := simp)]
lemma rightUnitor_hom_ι₀ :
    (stdSimplex.rightUnitor X).hom ≫ ι₀ = X ◁ stdSimplex.δ 1 := by
  rw [← rightUnitor_inv_map_δ_one, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
lemma rightUnitor_hom_ι₁ :
    (stdSimplex.rightUnitor X).hom ≫ ι₁ = X ◁ stdSimplex.δ 0 := by
  rw [← rightUnitor_inv_map_δ_zero, Iso.hom_inv_id_assoc]

end stdSimplex

end SSet
