/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.ModelCategory.NaiveFibrationDeformation
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalAnodyneSystem

/-!
# Public consumers of the naive dual-deformation criterion
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra

universe w v u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.NaiveFibrationDeformation

section GenericReverse

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C]
variable (P : Precylinder (𝟭 C)) [P.IsExact.{w}] (An : MorphismProperty C)
variable [P.IsAnodyneSystem.{w} An] {A B X Y : C}

/-- The public reverse API fills an arbitrary supplied mono square, with
both diagonal equations and no initial, terminal or codomain-fibrancy premise. -/
theorem genericSquare (p : X ⟶ Y) (hp : An.rlp p) (D : P.DualDeformationData p)
    (i : A ⟶ B) [Mono i] (a : A ⟶ X) (b : B ⟶ Y) (sq : CommSq a i p b) :
    ∃ l : B ⟶ X, i ≫ l = a ∧ l ≫ p = b := by
  have hip : HasLiftingProperty i p := D.mem_rlp_monomorphisms hp i (by infer_instance)
  have : sq.HasLift := hip.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end GenericReverse

open SSet SSet.joyalInterval

/-- The forward iff supplies the actual finite-J homotopy, its two
endpoints, and its entire over-base equation, for arbitrary source and base. -/
theorem finiteJForward {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : auxiliaryNaiveFibrations p)
    (ht : (MorphismProperty.monomorphisms SSet).rlp p) :
    ∃ (s : Y ⟶ X) (H : joyalInterval ⊗ X ⟶ X),
      s ≫ p = 𝟙 Y ∧ (productPrecylinder.app X).i₀ ≫ H = 𝟙 X ∧
        (productPrecylinder.app X).i₁ ≫ H = p ≫ s ∧
          H ≫ p = (productPrecylinder.app X).π ≫ p := by
  obtain ⟨D⟩ :=
    (Precylinder.IsAnodyneSystem.naiveFibration_mem_rlp_monomorphisms_iff_nonempty_dualDeformationData
      productPrecylinder auxiliaryAnodyneExtensions p hp).mp ht
  exact ⟨D.section_, D.homotopy.h, D.section_comp, D.homotopy.h₀,
    D.homotopy.h₁, D.over_base⟩

/-- The reverse iff yields an actual strict diagonal in every supplied
finite-J mono square; neither simplicial endpoint is assumed fibrant. -/
theorem finiteJReverse {A B X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : auxiliaryNaiveFibrations p) (D : productPrecylinder.DualDeformationData p)
    (i : A ⟶ B) [Mono i] (a : A ⟶ X) (b : B ⟶ Y) (sq : CommSq a i p b) :
    ∃ l : B ⟶ X, i ≫ l = a ∧ l ≫ p = b := by
  have ht :=
    (Precylinder.IsAnodyneSystem.naiveFibration_mem_rlp_monomorphisms_iff_nonempty_dualDeformationData
      productPrecylinder auxiliaryAnodyneExtensions p hp).mpr ⟨D⟩
  have hip : HasLiftingProperty i p := ht i (by infer_instance)
  have : sq.HasLift := hip.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end MathlibExtTest.AlgebraicTopology.ModelCategory.NaiveFibrationDeformation
