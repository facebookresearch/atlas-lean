/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.NormalizedHomologyComparison

@[expose] public section

set_option autoImplicit false

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.NormalizedHomologyComparison

universe w v u

open CategoryTheory Limits HomologicalComplex Simplicial

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

theorem normalizedChainComplex_d_component_client (R : C) (X : SSet.{w})
    (n : ℕ) (x : X _⦋n + 1⦌) :
    X.ιNormalizedChainComplex (R := R) x ≫
        (X.normalizedChainComplex R).d (n + 1) n =
      ∑ i : Fin (n + 2),
        (-1) ^ i.val • X.ιNormalizedChainComplex (R := R) (X.δ i x) :=
  X.ιNormalizedChainComplex_d x
theorem normalizedChainComplex_d_squared_zero_client (R : C) (X : SSet.{w})
    (n : ℕ) :
    (X.normalizedChainComplex R).d (n + 2) (n + 1) ≫
        (X.normalizedChainComplex R).d (n + 1) n = 0 :=
  HomologicalComplex.d_comp_d _ _ _ _
theorem normalizedChainComplexFunctor_map_id_client (R : C) :
    (SSet.normalizedChainComplexFunctor (C := C)).map (𝟙 R) =
      𝟙 ((SSet.normalizedChainComplexFunctor (C := C)).obj R) :=
  (SSet.normalizedChainComplexFunctor (C := C)).map_id R

theorem normalizedChainComplexFunctor_map_comp_client {R S T : C}
    (f : R ⟶ S) (g : S ⟶ T) :
    (SSet.normalizedChainComplexFunctor (C := C)).map (f ≫ g) =
      (SSet.normalizedChainComplexFunctor (C := C)).map f ≫
        (SSet.normalizedChainComplexFunctor (C := C)).map g :=
  (SSet.normalizedChainComplexFunctor (C := C)).map_comp f g

theorem normalizedChainComplexFunctor_map_app_client {R S : C} (f : R ⟶ S)
    (X : SSet.{w}) :
    ((SSet.normalizedChainComplexFunctor (C := C)).map f).app X =
      X.fromNormalizedChainComplex (C := C) R ≫
        ((SSet.chainComplexFunctor C).map f).app X ≫
          X.toNormalizedChainComplex (C := C) S :=
  SSet.normalizedChainComplexFunctor_map_app (C := C) f X

theorem chainComplexFunctor_map_app_PInfty_client {R S : C} (f : R ⟶ S)
    (X : SSet.{w}) :
    ((SSet.chainComplexFunctor C).map f).app X ≫
        (AlgebraicTopology.DoldKan.PInfty : X.chainComplex S ⟶ X.chainComplex S) =
      (AlgebraicTopology.DoldKan.PInfty : X.chainComplex R ⟶ X.chainComplex R) ≫
        ((SSet.chainComplexFunctor C).map f).app X :=
  SSet.chainComplexFunctor_map_app_PInfty (C := C) f X

variable [CategoryWithHomology C]

noncomputable def homologyIso_fromNormalizedChainComplex_client (X : SSet.{w})
    (R : C) (n : ℕ) :
    (X.normalizedChainComplex (C := C) R).homology n ≅
      (X.chainComplex (C := C) R).homology n :=
  SSet.homologyIso_fromNormalizedChainComplex (C := C) X R n

theorem homologyIso_fromNormalizedChainComplex_hom_client (X : SSet.{w})
    (R : C) (n : ℕ) :
    (SSet.homologyIso_fromNormalizedChainComplex (C := C) X R n).hom =
      HomologicalComplex.homologyMap (X.fromNormalizedChainComplex (C := C) R) n :=
  SSet.homologyIso_fromNormalizedChainComplex_hom (C := C) X R n

theorem homologyNatIso_fromNormalizedChainComplex_hom_app_client
    (R : C) (n : ℕ) (X : SSet.{w}) :
    (SSet.homologyNatIso_fromNormalizedChainComplex (C := C) R n).hom.app X =
      HomologicalComplex.homologyMap (X.fromNormalizedChainComplex (C := C) R) n :=
  SSet.homologyNatIso_fromNormalizedChainComplex_hom_app (C := C) R n X

theorem homologyNatIso_fromNormalizedChainComplex_naturality_client
    (R : C) (n : ℕ) {X Y : SSet.{w}} (f : X ⟶ Y) :
    (SSet.normalizedChainComplexFunctorObj (C := C) R ⋙
        HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).map f ≫
      (SSet.homologyNatIso_fromNormalizedChainComplex (C := C) R n).hom.app Y =
    (SSet.homologyNatIso_fromNormalizedChainComplex (C := C) R n).hom.app X ≫
      ((SSet.chainComplexFunctor C).obj R ⋙
        HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).map f :=
  (SSet.homologyNatIso_fromNormalizedChainComplex (C := C) R n).hom.naturality f

end MathlibExtTest.AlgebraicTopology.SimplicialSet.NormalizedHomologyComparison
