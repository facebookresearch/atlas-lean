/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanAugmentation

/-! Original diagonal augmentation on all weighted simplices and compatible cocones. -/

public section

open CategoryTheory Limits Opposite Simplicial

universe uJ vJ

namespace MathlibExtTest.CommonBKDiagonalAugmentation

variable {J : Type uJ} [Category.{vJ} J]
variable {D E : J ⥤ SSet.{max uJ vJ}} {Z Z' : SSet.{max uJ vJ}}

/-- The actual map is the original diagonal augmentation and constant comparison. -/
theorem original_diagonal (τ : D ⟶ (Functor.const J).obj Z) :
    SSet.bkAugmentation τ =
      SSet.simplicialDiagonalFunctor.map (SSet.wbarAugmentation τ) ≫
        (SSet.diagonalConstIso Z).hom := rfl

/-- Every diagonal degree retains the original coproduct-descended cocone map. -/
theorem all_degrees (τ : D ⟶ (Functor.const J).obj Z) (n : ℕ) :
    (SSet.bkAugmentation τ).app (op ⦋n⦌) =
      (StrictOrdinaryWeightedBar.wbarDesc (CategoryBar.replUnit J) D n
        (fun p => τ.app p.1.left)).app (op ⦋n⦌) :=
  SSet.bkAugmentation_app_mk τ n

/-- The actual weighted simplex goes to the original cocone at its left endpoint. -/
theorem weighted_simplex (τ : D ⟶ (Functor.const J).obj Z) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
    (x : (D.obj p.1.left).obj (op ⦋n⦌)) :
    (SSet.bkAugmentation τ).app (op ⦋n⦌)
        ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) x) =
      (τ.app p.1.left).app (op ⦋n⦌) x :=
  ConcreteCategory.congr_hom (SSet.bkAugmentation_app_mk_ι τ n p) x

/-- The full augmentation naturality retains the original map of compatible cocones. -/
theorem compatible_cocones (α : D ⟶ E)
    (τ : D ⟶ (Functor.const J).obj Z) (τ' : E ⟶ (Functor.const J).obj Z')
    (f : Z ⟶ Z') (h : ∀ j, α.app j ≫ τ'.app j = τ.app j ≫ f) :
    SSet.bkHocolimMap α ≫ SSet.bkAugmentation τ' = SSet.bkAugmentation τ ≫ f :=
  SSet.bkAugmentation_naturality α τ τ' f h

/-- Every original diagonal face commutes with the target's actual face map. -/
theorem face (τ : D ⟶ (Functor.const J).obj Z) (n : ℕ) (i : Fin (n + 2)) :
    (SSet.bkHocolim D).map (SimplexCategory.δ i).op ≫
        (SSet.bkAugmentation τ).app (op ⦋n⦌) =
      (SSet.bkAugmentation τ).app (op ⦋n + 1⦌) ≫ Z.map (SimplexCategory.δ i).op :=
  (SSet.bkAugmentation τ).naturality (SimplexCategory.δ i).op

/-- Every original diagonal degeneracy commutes with the target's actual degeneracy. -/
theorem degeneracy (τ : D ⟶ (Functor.const J).obj Z) (n : ℕ) (i : Fin (n + 1)) :
    (SSet.bkHocolim D).map (SimplexCategory.σ i).op ≫
        (SSet.bkAugmentation τ).app (op ⦋n + 1⦌) =
      (SSet.bkAugmentation τ).app (op ⦋n⦌) ≫ Z.map (SimplexCategory.σ i).op :=
  (SSet.bkAugmentation τ).naturality (SimplexCategory.σ i).op

end MathlibExtTest.CommonBKDiagonalAugmentation

namespace MathlibExtTest.CommonBKDiagonalAugmentationCategory0

variable {J : Type uJ} [Category.{0} J] {D : J ⥤ SSet.{uJ}} {Z : SSet.{uJ}}

/-- Degree zero and the historical Hom-zero universe use the same original weighted map. -/
theorem weighted_zero (τ : D ⟶ (Functor.const J).obj Z)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) 0)
    (x : (D.obj p.1.left).obj (op ⦋0⦌)) :
    (SSet.bkAugmentation τ).app (op ⦋0⦌)
        ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D 0 p).app (op ⦋0⦌) x) =
      (τ.app p.1.left).app (op ⦋0⦌) x :=
  MathlibExtTest.CommonBKDiagonalAugmentation.weighted_simplex τ 0 p x

end MathlibExtTest.CommonBKDiagonalAugmentationCategory0
