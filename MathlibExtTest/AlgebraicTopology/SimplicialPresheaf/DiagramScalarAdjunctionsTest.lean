/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.DiagramScalarAdjunctions

/-! # Ordinary original coefficient-presheaf free/cofree comparison clients -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u vD wD vJ wJ

open CategoryTheory CategoryTheory.Limits Opposite SimplicialPresheaf
open SimplicialPresheaf.LocalizationDiagram

variable {D : Type wD} [Category.{vD} D] [LocallySmall.{u} D]
  {J : Type wJ} [Category.{vJ} J]

/-- An original e→d label gives the same original free summand, in presheaf coefficients. -/
private theorem diagramScalarClient1 (d e : D) (h : e ⟶ d) (A : SimplicialPresheaf.{u} J) :
    freeInclusion (J := J) d e h A ≫ (freeObjectIso (J := J) d e A).hom =
      Sigma.ι (fun _ : op d ⟶ op e => A) h.op :=
  freeInclusion_hom (J := J) d e h A

/-- Cofree products use original d→e labels and the same original projection. -/
private theorem diagramScalarClient2 (d e : D) (h : d ⟶ e) (Z : SimplicialPresheaf.{u} J) :
    (cofreeObjectIso (J := J) d e Z).inv ≫ cofreeProjection (J := J) d e h Z =
      Pi.π (fun _ : op e ⟶ op d => Z) h.op := by
  simp only [cofreeProjection, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Free tensor comparison preserves the source coefficient map and A×K product order. -/
private theorem diagramScalarClient3 (d : D) {A B : SimplicialPresheaf.{u} J} (a : A ⟶ B) (K : SSet.{u}) :
    (free (J := J) d).map ((scalarTensor.map a).app K) ≫
        (freeTensorIso (J := J) d B).hom.app K =
      (freeTensorIso (J := J) d A).hom.app K ≫
        (scalarTensor.map ((free (J := J) d).map a)).app K :=
  freeTensorIso_source (J := J) d a K

variable [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J]

/-- The original coefficient precomposition source is at B and target at A. -/
private theorem diagramScalarClient4 (d : D) {A B : SimplicialPresheaf.{u} J} (a : A ⟶ B)
    (Z : SimplicialPresheaf.{u} (D × J)) :
    (freePrecompArrowIso (J := J) d a Z).hom.left = (freeHomIso (J := J) d B Z).hom ∧
      (freePrecompArrowIso (J := J) d a Z).hom.right = (freeHomIso (J := J) d A Z).hom ∧
      (freePrecompArrowIso (J := J) d a Z).inv.left = (freeHomIso (J := J) d B Z).inv ∧
      (freePrecompArrowIso (J := J) d a Z).inv.right = (freeHomIso (J := J) d A Z).inv :=
  freePrecompArrowIso_laws (J := J) d a Z

/-- All four cofree Arrow legs use the original flat source arrow. -/
private theorem diagramScalarClient5 (d : D) {A B : SimplicialPresheaf.{u} (D × J)} (a : A ⟶ B)
    (Z : SimplicialPresheaf.{u} J) :
    (cofreePrecompArrowIso (J := J) d a Z).hom.left = (cofreeHomIso (J := J) d B Z).hom ∧
      (cofreePrecompArrowIso (J := J) d a Z).hom.right = (cofreeHomIso (J := J) d A Z).hom ∧
      (cofreePrecompArrowIso (J := J) d a Z).inv.left = (cofreeHomIso (J := J) d B Z).inv ∧
      (cofreePrecompArrowIso (J := J) d a Z).inv.right = (cofreeHomIso (J := J) d A Z).inv :=
  cofreePrecompArrowIso_laws (J := J) d a Z

/-- Both whole native Arrow squares have left≫target equal to source≫right. -/
private theorem diagramScalarClient6 (d : D) {A B : SimplicialPresheaf.{u} J} (a : A ⟶ B)
    (Z : SimplicialPresheaf.{u} (D × J)) :
    (freePrecompArrowIso (J := J) d a Z).hom.left ≫
        innerHomPre a ((evaluation (J := J) d).obj Z) =
      innerHomPre ((free (J := J) d).map a) Z ≫
        (freePrecompArrowIso (J := J) d a Z).hom.right :=
  (freePrecompArrowIso (J := J) d a Z).hom.w

/-- The cofree forward characteristic uses the ordinary inverse Hom equivalence. -/
private theorem diagramScalarClient7 (d : D) (A : SimplicialPresheaf.{u} (D × J)) (K : SSet.{u})
    (Z : SimplicialPresheaf.{u} J) (g : K ⟶ innerHom A ((cofree (J := J) d).obj Z)) :
    g ≫ (cofreeHomIso (J := J) d A Z).hom =
      scalarTensorHomEquiv ((evaluation (J := J) d).obj A) K Z
        ((evaluationTensorIso (J := J) d A).inv.app K ≫
          ((cofreeAdjunction (J := J) d).homEquiv _ Z).symm
            ((scalarTensorHomEquiv A K ((cofree (J := J) d).obj Z)).symm g)) :=
  cofreeHomIso_hom_characteristic (J := J) d A K Z g

/-- Every original D-parameter arrow is retained by the free end source naturality. -/
private theorem diagramScalarClient8 {d e : D} (t : d ⟶ e) (A : SimplicialPresheaf.{u} J)
    (Z : SimplicialPresheaf.{u} (D × J)) :
    innerHomPre (freeIndexMap (J := J) t A) Z ≫ (freeHomIso (J := J) d A Z).hom =
      (freeHomIso (J := J) e A Z).hom ≫
        innerHomPost A ((evaluationRestriction (J := J) t).app Z) :=
  freeHomIso_index (J := J) t A Z

/-- Both complete original end isomorphisms retain their actual full inverse maps. -/
private theorem diagramScalarClient9 (d : D) (A Z : SimplicialPresheaf.{u} J) (X : SimplicialPresheaf.{u} (D × J)) :
    (freeHomIso (J := J) d A X).hom ≫ (freeHomIso (J := J) d A X).inv = 𝟙 _ ∧
    (freeHomIso (J := J) d A X).inv ≫ (freeHomIso (J := J) d A X).hom = 𝟙 _ ∧
    (cofreeHomIso (J := J) d X Z).hom ≫ (cofreeHomIso (J := J) d X Z).inv = 𝟙 _ ∧
    (cofreeHomIso (J := J) d X Z).inv ≫ (cofreeHomIso (J := J) d X Z).hom = 𝟙 _ :=
  mappingEndIso_roundtrips (J := J) d A Z X
