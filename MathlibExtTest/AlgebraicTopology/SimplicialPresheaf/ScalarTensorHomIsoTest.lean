/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.ScalarTensorHomIso

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open scoped MonoidalClosed Simplicial

namespace ScalarTensorHomIsoTest

open SimplicialPresheaf

variable {D : Type w} [Category.{v} D]

private theorem originalAssociatorComponents (K R : SSet.{u})
    (A : SimplicialPresheaf.{u} D) (d : Dᵒᵖ) :
    (((scalarTensorAssociator K A).hom.app R).app d = (α_ (A.obj d) K R).hom) ∧
    (((scalarTensorAssociator K A).inv.app R).app d = (α_ (A.obj d) K R).inv) :=
  ⟨scalarTensorAssociator_hom_app K R A d, scalarTensorAssociator_inv_app K R A d⟩

private theorem originalSiteNaturality (K R : SSet.{u}) (A : SimplicialPresheaf.{u} D)
    {d e : Dᵒᵖ} (g : d ⟶ e) :
    ((((scalarTensor.obj ((scalarTensor.obj A).obj K)).obj R).map g) ≫
        ((scalarTensorAssociator K A).hom.app R).app e =
      ((scalarTensorAssociator K A).hom.app R).app d ≫
        ((scalarTensor.obj A).obj (K ⊗ R)).map g) :=
  ((scalarTensorAssociator K A).hom.app R).naturality g

private theorem actualScalarSourceCoherence (K R : SSet.{u})
    {A A' : SimplicialPresheaf.{u} D} (a : A' ⟶ A) :
    (scalarTensor.map ((scalarTensor.map a).app K)).app R ≫
        (scalarTensorAssociator K A).hom.app R =
      (scalarTensorAssociator K A').hom.app R ≫ (scalarTensor.map a).app (K ⊗ R) :=
  scalarTensorAssociator_source K a R

variable [Small.{u} D] [LocallySmall.{u} D]

private theorem bothOriginalTranspositions (K R : SSet.{u})
    (A Z : SimplicialPresheaf.{u} D)
    (b : R ⟶ innerHom ((scalarTensor.obj A).obj K) Z)
    (c : R ⟶ (ihom K).obj (innerHom A Z)) :
    (b ≫ (scalarTensorHomIso K A).hom.app Z =
      curry (scalarTensorHomEquiv A (K ⊗ R) Z
        ((scalarTensorAssociator K A).inv.app R ≫
          (scalarTensorHomEquiv ((scalarTensor.obj A).obj K) R Z).symm b))) ∧
    (c ≫ (scalarTensorHomIso K A).inv.app Z =
      scalarTensorHomEquiv ((scalarTensor.obj A).obj K) R Z
        ((scalarTensorAssociator K A).hom.app R ≫
          (scalarTensorHomEquiv A (K ⊗ R) Z).symm (uncurry c))) :=
  ⟨scalarTensorHomIso_characteristic K A Z R b,
    scalarTensorHomIso_inverse_characteristic K A Z R c⟩

private theorem originalEndProjection (K R : SSet.{u})
    (A Z : SimplicialPresheaf.{u} D)
    (b : R ⟶ innerHom ((scalarTensor.obj A).obj K) Z) (d : Dᵒᵖ) :
    uncurry (b ≫ (scalarTensorHomIso K A).hom.app Z) ≫ innerHomπ A Z d =
      curry ((α_ (A.obj d) K R).inv ≫
        ((scalarTensorHomEquiv ((scalarTensor.obj A).obj K) R Z).symm b).app d) :=
  scalarTensorHomIso_end_π K A Z R b d

private theorem bothNativeIdentities (K : SSet.{u}) (A Z : SimplicialPresheaf.{u} D) :
    ((scalarTensorHomIso K A).hom.app Z ≫ (scalarTensorHomIso K A).inv.app Z = 𝟙 _) ∧
    ((scalarTensorHomIso K A).inv.app Z ≫ (scalarTensorHomIso K A).hom.app Z = 𝟙 _) :=
  ⟨(scalarTensorHomIso K A).hom_inv_id_app Z, (scalarTensorHomIso K A).inv_hom_id_app Z⟩

private theorem allOriginalMaps {K L : SSet.{u}} (k : K ⟶ L)
    {A A' Z Z' : SimplicialPresheaf.{u} D} (a : A' ⟶ A) (g : Z ⟶ Z') :
    (innerHomPre ((scalarTensor.obj A).map k) Z ≫ (scalarTensorHomIso K A).hom.app Z =
      (scalarTensorHomIso L A).hom.app Z ≫ (pre k).app (innerHom A Z)) ∧
    (innerHomPre ((scalarTensor.map a).app K) Z ≫ (scalarTensorHomIso K A').hom.app Z =
      (scalarTensorHomIso K A).hom.app Z ≫ (ihom K).map (innerHomPre a Z)) ∧
    (innerHomPost ((scalarTensor.obj A).obj K) g ≫ (scalarTensorHomIso K A).hom.app Z' =
      (scalarTensorHomIso K A).hom.app Z ≫ (ihom K).map (innerHomPost A g)) :=
  ⟨scalarTensorHomIso_naturality_scalar k A Z, scalarTensorHomIso_naturality_source K a Z,
    scalarTensorHomIso_naturality_target K A g⟩

end ScalarTensorHomIsoTest
