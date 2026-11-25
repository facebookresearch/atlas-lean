/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.Product.Basic
public import MathlibExt.Analysis.CStarAlgebra.Module.Unitary

/-!
# Unitary equivalences of binary C-star-module products

The constructions in this file use the genuine coefficient-inner-product
product. They provide coordinatewise, symmetry and associativity unitaries
needed to transport source structures without asserting literal equality of
different product carriers.
-/

@[expose] public section

noncomputable section

namespace CStarModule.UnitaryEquiv

universe uB uE uF uE' uF' uG

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [SMul Bᵐᵒᵖ E'] [CStarModule Bᵐᵒᵖ E']
variable {F' : Type uF'} [NormedAddCommGroup F'] [NormedSpace ℂ F']
  [SMul Bᵐᵒᵖ F'] [CStarModule Bᵐᵒᵖ F']
variable {G : Type uG} [NormedAddCommGroup G] [NormedSpace ℂ G]
  [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]

/-- Let B be a possibly nonunital complex C-star algebra and let the factors be normed right
C-star modules over B, with their coefficient-valued inner products. Two unitary module
equivalences induce a unitary equivalence of the Hilbert-module products by applying them
coordinatewise. -/
def prodCongr (U : UnitaryEquiv B E E') (V : UnitaryEquiv B F F') :
    UnitaryEquiv B (CStarModule.Product B E F)
      (CStarModule.Product B E' F') where
  toAdjointable :=
    CStarModule.AdjointableOperator.prodMap
      U.toAdjointable V.toAdjointable
  adjoint_comp_self := by
    rw [CStarModule.AdjointableOperator.prodMap_adjointOperator,
      CStarModule.AdjointableOperator.prodMap_comp,
      U.adjoint_comp_self, V.adjoint_comp_self,
      CStarModule.AdjointableOperator.prodMap_id]
  comp_adjoint_self := by
    rw [CStarModule.AdjointableOperator.prodMap_adjointOperator,
      CStarModule.AdjointableOperator.prodMap_comp,
      U.comp_adjoint_self, V.comp_adjoint_self,
      CStarModule.AdjointableOperator.prodMap_id]

@[simp]
theorem prodCongr_apply (U : UnitaryEquiv B E E')
    (V : UnitaryEquiv B F F') (x : CStarModule.Product B E F) :
    prodCongr U V x =
      ((U x.1, V x.2) : CStarModule.Product B E' F') :=
  CStarModule.AdjointableOperator.prodMap_apply _ _ _

/-- Let B be a possibly nonunital complex C-star algebra and let the factors be normed right
C-star modules over B, with their coefficient-valued inner products. The coordinate
interchange map on the two-factor Hilbert-module product is adjointable and is its own
adjoint. -/
@[no_expose]
def prodCommOperator :
    CStarModule.AdjointableOperator B (CStarModule.Product B E F)
      (CStarModule.Product B F E) :=
  (CStarModule.Product.inl (B := B) (E := F) (F := E)).comp
      (CStarModule.Product.snd (B := B) (E := E) (F := F)) +
    (CStarModule.Product.inr (B := B) (E := F) (F := E)).comp
      (CStarModule.Product.fst (B := B) (E := E) (F := F))

/-- Let B be a possibly nonunital complex C-star algebra and let the factors be normed right
C-star modules over B, with their coefficient-valued inner products. Interchanging the two
factors is a unitary equivalence of the Hilbert-module products. -/
def prodComm :
    UnitaryEquiv B (CStarModule.Product B E F)
      (CStarModule.Product B F E) where
  toAdjointable := prodCommOperator (B := B) (E := E) (F := F)
  adjoint_comp_self := by
    ext x
    simp only [CStarModule.AdjointableOperator.comp_apply,
      CStarModule.AdjointableOperator.adjointOperator_apply,
      CStarModule.AdjointableOperator.id_apply]
    apply (WithCStarModule.equiv Bᵐᵒᵖ (E × F)).injective
    apply Prod.ext
    · change 0 + (0 + x.1) = x.1
      simp
    · change (x.2 + 0) + 0 = x.2
      simp
  comp_adjoint_self := by
    ext x
    simp only [CStarModule.AdjointableOperator.comp_apply,
      CStarModule.AdjointableOperator.adjointOperator_apply,
      CStarModule.AdjointableOperator.id_apply]
    apply (WithCStarModule.equiv Bᵐᵒᵖ (F × E)).injective
    apply Prod.ext
    · change (x.1 + 0) + 0 = x.1
      simp
    · change 0 + (0 + x.2) = x.2
      simp

@[simp]
theorem prodComm_apply (x : CStarModule.Product B E F) :
    prodComm (B := B) (E := E) (F := F) x =
      ((x.2, x.1) : CStarModule.Product B F E) := by
  change (x.2, 0) + (0, x.1) = (x.2, x.1)
  ext <;> simp

/-- Let B be a possibly nonunital complex C-star algebra and let the factors be normed right
C-star modules over B, with their coefficient-valued inner products. Reassociation of a three-
factor Hilbert-module product is adjointable, with the reverse reassociation as adjoint. -/
@[no_expose]
def prodAssocOperator :
    CStarModule.AdjointableOperator B
      (CStarModule.Product B (CStarModule.Product B E F) G)
      (CStarModule.Product B E (CStarModule.Product B F G)) :=
  let sourceEF := CStarModule.Product.fst
    (B := B) (E := CStarModule.Product B E F) (F := G)
  let eCoord := (CStarModule.Product.fst (B := B) (E := E) (F := F)).comp sourceEF
  let fCoord := (CStarModule.Product.snd (B := B) (E := E) (F := F)).comp sourceEF
  let gCoord := CStarModule.Product.snd
    (B := B) (E := CStarModule.Product B E F) (F := G)
  let fg :=
    (CStarModule.Product.inl (B := B) (E := F) (F := G)).comp fCoord +
      (CStarModule.Product.inr (B := B) (E := F) (F := G)).comp gCoord
  (CStarModule.Product.inl
      (B := B) (E := E) (F := CStarModule.Product B F G)).comp eCoord +
    (CStarModule.Product.inr
      (B := B) (E := E) (F := CStarModule.Product B F G)).comp fg

/-- Let B be a possibly nonunital complex C-star algebra and let the factors be normed right
C-star modules over B, with their coefficient-valued inner products. Reassociation gives a
unitary equivalence between the two bracketings of a three-factor Hilbert-module product. -/
def prodAssoc :
    UnitaryEquiv B
      (CStarModule.Product B (CStarModule.Product B E F) G)
      (CStarModule.Product B E (CStarModule.Product B F G)) where
  toAdjointable := prodAssocOperator (B := B) (E := E) (F := F) (G := G)
  adjoint_comp_self := by
    ext x
    simp only [CStarModule.AdjointableOperator.comp_apply,
      CStarModule.AdjointableOperator.adjointOperator_apply,
      CStarModule.AdjointableOperator.id_apply]
    apply (WithCStarModule.equiv Bᵐᵒᵖ
      (CStarModule.Product B E F × G)).injective
    apply Prod.ext
    · apply (WithCStarModule.equiv Bᵐᵒᵖ (E × F)).injective
      apply Prod.ext
      · change (x.1.1 + 0) + (0 + 0) = x.1.1
        simp
      · change 0 + ((0 + (x.1.2 + 0)) + 0) = x.1.2
        simp
    · change 0 + (0 + (0 + (0 + x.2))) = x.2
      simp
  comp_adjoint_self := by
    ext x
    simp only [CStarModule.AdjointableOperator.comp_apply,
      CStarModule.AdjointableOperator.adjointOperator_apply,
      CStarModule.AdjointableOperator.id_apply]
    apply (WithCStarModule.equiv Bᵐᵒᵖ
      (E × CStarModule.Product B F G)).injective
    apply Prod.ext
    · change (x.1 + (0 + 0)) + 0 = x.1
      simp
    · apply (WithCStarModule.equiv Bᵐᵒᵖ (F × G)).injective
      apply Prod.ext
      · change 0 + ((0 + (x.2.1 + 0)) + 0) = x.2.1
        simp
      · change 0 + (0 + (0 + (0 + x.2.2))) = x.2.2
        simp

@[simp]
theorem prodAssoc_apply
    (x : CStarModule.Product B (CStarModule.Product B E F) G) :
    prodAssoc (B := B) (E := E) (F := F) (G := G) x =
      ((x.1.1, (x.1.2, x.2)) :
        CStarModule.Product B E (CStarModule.Product B F G)) := by
  change (x.1.1, 0) + (0, (x.1.2, 0) + (0, x.2)) =
    (x.1.1, (x.1.2, x.2))
  ext <;> simp

end CStarModule.UnitaryEquiv
