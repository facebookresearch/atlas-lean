/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Factorization
import Mathlib.CategoryTheory.Discrete.Basic

/-!# Same-cardinal whole projective factorization data clients -/
set_option autoImplicit false
noncomputable section
universe w uD vD uM vM
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
namespace MathlibExtTest.FunctorProjectiveFactorization
variable {D : Type uD} [Category.{vD} D] {M : Type uM} [Category.{vM} M]
  [ModelCategory M] {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} D] [LocallySmall.{w} D] (d : CofibrantGenerationData M κ)

example : letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
    FunctorialFactorizationData (cofibrations (D ⥤ M)) (trivialFibrations (D ⥤ M)) :=
  FunctorProjective.cofibrantFactorizationData d

example : letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
    FunctorialFactorizationData (trivialCofibrations (D ⥤ M)) (fibrations (D ⥤ M)) :=
  FunctorProjective.fibrantFactorizationData d

example (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
    letI : (FunctorProjective.freeGenerators (D := D) d d.I).IsCardinalForSmallObjectArgument κ :=
      FunctorProjective.freeI_eligible (D := D) d
    (FunctorProjective.cofibrantFactorizationData d).Z.obj f =
      SmallObject.obj (FunctorProjective.freeGenerators (D := D) d d.I) κ f.hom :=
  FunctorProjective.cofibrantFactorizationData_obj d f

example {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) :
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
    letI : (FunctorProjective.freeGenerators (D := D) d d.J).IsCardinalForSmallObjectArgument κ :=
      FunctorProjective.freeJ_eligible (D := D) d
    (FunctorProjective.fibrantFactorizationData d).Z.map φ =
      SmallObject.objMap (FunctorProjective.freeGenerators (D := D) d d.J) κ φ :=
  FunctorProjective.fibrantFactorizationData_map d φ

example (f : Arrow (D ⥤ M)) (x : D) :
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
    ((FunctorProjective.cofibrantFactorizationData d).i.app f).app x ≫
      ((FunctorProjective.cofibrantFactorizationData d).p.app f).app x = f.hom.app x := by
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
  exact NatTrans.congr_app ((FunctorProjective.cofibrantFactorizationData d).fac_app) x

example {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) (x : D) :
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
    φ.left.app x ≫ ((FunctorProjective.fibrantFactorizationData d).i.app g).app x =
      ((FunctorProjective.fibrantFactorizationData d).i.app f).app x ≫
        ((FunctorProjective.fibrantFactorizationData d).Z.map φ).app x := by
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
  exact NatTrans.congr_app ((FunctorProjective.fibrantFactorizationData d).i.naturality φ) x

example {f g h : Arrow (D ⥤ M)} (φ : f ⟶ g) (ψ : g ⟶ h) :
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
    (FunctorProjective.cofibrantFactorizationData d).Z.map (φ ≫ ψ) =
      (FunctorProjective.cofibrantFactorizationData d).Z.map φ ≫
        (FunctorProjective.cofibrantFactorizationData d).Z.map ψ := by
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
  exact (FunctorProjective.cofibrantFactorizationData d).Z.map_comp φ ψ

example (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
    (FunctorProjective.fibrantFactorizationData d).Z.map (𝟙 f) =
      𝟙 ((FunctorProjective.fibrantFactorizationData d).Z.obj f) := by
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
  exact (FunctorProjective.fibrantFactorizationData d).Z.map_id f

example (f : Arrow (Discrete ℕ ⥤ M)) (n : ℕ) :
    letI : ModelCategory (Discrete ℕ ⥤ M) :=
      FunctorProjective.modelCategory.{w} (J := Discrete ℕ) d
    ((FunctorProjective.fibrantFactorizationData d).i.app f).app ⟨n⟩ ≫
      ((FunctorProjective.fibrantFactorizationData d).p.app f).app ⟨n⟩ = f.hom.app ⟨n⟩ := by
  let _ : ModelCategory (Discrete ℕ ⥤ M) :=
    FunctorProjective.modelCategory.{w} (J := Discrete ℕ) d
  exact NatTrans.congr_app ((FunctorProjective.fibrantFactorizationData d).fac_app) (Discrete.mk n)


example : letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
    IsWeakFactorizationSystem (cofibrations (D ⥤ M)) (trivialFibrations (D ⥤ M)) := by
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
  infer_instance

example : letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
    IsWeakFactorizationSystem (trivialCofibrations (D ⥤ M)) (fibrations (D ⥤ M)) := by
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
  infer_instance

example (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
    cofibrations (D ⥤ M) ((FunctorProjective.cofibrantFactorizationData d).i.app f) ∧
      trivialFibrations (D ⥤ M) ((FunctorProjective.cofibrantFactorizationData d).p.app f) := by
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
  exact ⟨(FunctorProjective.cofibrantFactorizationData d).hi f,
    (FunctorProjective.cofibrantFactorizationData d).hp f⟩

example {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) (x : D) :
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
    ((FunctorProjective.cofibrantFactorizationData d).Z.map φ).app x ≫
      ((FunctorProjective.cofibrantFactorizationData d).p.app g).app x =
        ((FunctorProjective.cofibrantFactorizationData d).p.app f).app x ≫ φ.right.app x :=
  FunctorProjective.cofibrantFactorizationData_p_naturality_app d φ x

example (f : Arrow (D ⥤ M)) (x : D) :
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
    ((FunctorProjective.fibrantFactorizationData d).i.app f).app x ≫
      ((FunctorProjective.fibrantFactorizationData d).p.app f).app x = f.hom.app x :=
  FunctorProjective.fibrantFactorizationData_fac_app d f x

example : letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
    HasFunctorialFactorization (cofibrations (D ⥤ M)) (trivialFibrations (D ⥤ M)) ∧
      HasFunctorialFactorization (trivialCofibrations (D ⥤ M)) (fibrations (D ⥤ M)) :=
  FunctorProjective.functorialFactorizations d

end MathlibExtTest.FunctorProjectiveFactorization
