/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SmallLimits
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ProductSymmetry
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterBifunctors
import MathlibExt.CategoryTheory.Adjunction.CopointedOver

/-!
# Actual marked cotensors over the supplied base

The scalar action already uses the product with the maximally marked
parameter and the original source projection. Its right adjoint is the
native marked internal Hom pulled back along the transpose of that same
projection. This retains every original mark and fixed-base equation,
without a fibrancy or model hypothesis.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace SSet.Marked

/-- The native second product projection is the original scalar-action copoint. -/
def parameterCopoint (K : SSet.{u}) : prodLeft (max K) ⟶ 𝟭 Marked.{u} where
  app X := prodSnd (max K) X
  naturality _ _ _ := Hom.ext rfl

/-- Fixing the actual scalar parameter gives the original marked slice action. -/
def overScalarTensor (Z : Marked.{u}) (K : SSet.{u}) : Over Z ⥤ Over Z :=
  Adjunction.copointedOverLeft (parameterCopoint K) Z

/-- The native tensor object retains the original product and whole base projection. -/
@[simp]
theorem overScalarTensor_obj (Z : Marked.{u}) (K : SSet.{u}) (X : Over Z) :
    (overScalarTensor Z K).obj X = overParameter Z X K := rfl

/-- The fixed-parameter action retains the same original marked source map. -/
@[simp]
theorem overScalarTensor_map_left {Z : Marked.{u}} (K : SSet.{u})
    {X Y : Over Z} (f : X ⟶ Y) :
    ((overScalarTensor Z K).map f).left = prodMap (𝟙 (max K)) f.left := rfl

/-- The actual fixed-base cotensor is the original right-adjoint image pulled back along the transposed projection. -/
def overCotensor (Z : Marked.{u}) (K : SSet.{u}) : Over Z ⥤ Over Z :=
  (leftProductAdjunction (max K)).copointedOverRight (parameterCopoint K) Z

/-- The same whole tensor maps and native cotensor pullback form the adjunction in the original marked slice. -/
def overScalarTensorAdjunction (Z : Marked.{u}) (K : SSet.{u}) :
    overScalarTensor Z K ⊣ overCotensor Z K :=
  (leftProductAdjunction (max K)).copointedOver (parameterCopoint K) Z

/-- Its full marked carrier is the actual pullback of the internal-Hom base map and the original transposed
  projection. -/
@[simp]
theorem overCotensor_obj_left (Z : Marked.{u}) (K : SSet.{u}) (Y : Over Z) :
    ((overCotensor Z K).obj Y).left =
      pullback (internalHomPost (max K) Y.hom)
        ((leftProductAdjunction (max K)).homEquiv Z Z (prodSnd (max K) Z)) := rfl

/-- The original fixed-scalar slice action preserves the same native colimits. -/
theorem overScalarTensor_preservesColimits (Z : Marked.{u}) (K : SSet.{u}) :
    PreservesColimitsOfSize.{u, u} (overScalarTensor Z K) :=
  (overScalarTensorAdjunction Z K).leftAdjoint_preservesColimits

/-- The actual cotensor represents scalar maps into the original relative marked mapping complex. -/
def overCotensorHomEquiv (Z : Marked.{u}) (K : SSet.{u}) (X Y : Over Z) :
    (X ⟶ (overCotensor Z K).obj Y) ≃
      (K ⟶ (overMappingFunctor .maximal Z Y).obj (op X)) :=
  ((overScalarTensorAdjunction Z K).homEquiv X Y).symm.trans
    ((overParameterAdjunction Z X).homEquiv K Y)

/-- Target naturality in the opposite slice retains actual source precomposition of the relative mapping complex. -/
theorem overCotensorHomEquiv_natural {Z : Marked.{u}} (K : SSet.{u})
    {X X' : Over Z} (Y : Over Z) (f : X' ⟶ X)
    (g : X ⟶ (overCotensor Z K).obj Y) :
    overCotensorHomEquiv Z K X' Y (f ≫ g) =
      overCotensorHomEquiv Z K X Y g ≫ (overMappingFunctor .maximal Z Y).map f.op := by
  change (overParameterAdjunction Z X').homEquiv K Y
      (((overScalarTensorAdjunction Z K).homEquiv X' Y).symm (f ≫ g)) = _
  rw [(overScalarTensorAdjunction Z K).homEquiv_naturality_left_symm]
  exact (overParameterAdjunction₂ Z).homEquiv_naturality_one f
    (((overScalarTensorAdjunction Z K).homEquiv X Y).symm g)

/-- Opposite over-maps transpose to the original scalar maps into the same relative mapping complex. -/
def overCotensorOppHomEquiv (Z : Marked.{u}) (Y : Over Z) (K : SSet.{u})
    (X : (Over Z)ᵒᵖ) :
    (op ((overCotensor Z K).obj Y) ⟶ X) ≃
      (K ⟶ (overMappingFunctor .maximal Z Y).obj X) :=
  (CategoryTheory.opEquiv _ _).trans (overCotensorHomEquiv Z K X.unop Y)

private theorem overCotensorOppHomEquiv_natural (Z : Marked.{u}) (Y : Over Z)
    (K : SSet.{u}) (X X' : (Over Z)ᵒᵖ) (f : X ⟶ X')
    (g : op ((overCotensor Z K).obj Y) ⟶ X) :
    overCotensorOppHomEquiv Z Y K X' (g ≫ f) =
      overCotensorOppHomEquiv Z Y K X g ≫ (overMappingFunctor .maximal Z Y).map f :=
  overCotensorHomEquiv_natural K Y f.unop g.unop

/-- The same actual cotensor objects, viewed oppositely, give the left adjoint of the original contravariant
  mapping functor. -/
def overCotensorLeft (Z : Marked.{u}) (Y : Over Z) : SSet.{u} ⥤ (Over Z)ᵒᵖ :=
  Adjunction.leftAdjointOfEquiv (overCotensorOppHomEquiv Z Y)
    (overCotensorOppHomEquiv_natural Z Y)

/-- Original scalar maps and original relative marked maps have this genuine opposite adjunction. -/
def overCotensorMappingAdjunction (Z : Marked.{u}) (Y : Over Z) :
    overCotensorLeft Z Y ⊣ overMappingFunctor .maximal Z Y :=
  Adjunction.adjunctionOfEquivLeft (overCotensorOppHomEquiv Z Y)
    (overCotensorOppHomEquiv_natural Z Y)

end SSet.Marked
