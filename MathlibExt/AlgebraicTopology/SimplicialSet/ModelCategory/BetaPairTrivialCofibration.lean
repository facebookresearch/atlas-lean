/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Actual beta-pair weakness from TCof product stability; no RawW0 Kan or Unit9 WE premise.
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.CartesianMonoidalModel
import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Products of simplicial trivial cofibrations

Trivial cofibrations of simplicial sets are preserved by products with a fixed
factor, using the Cartesian monoidal structure and the product braiding. In
particular, the product of a trivial cofibration with itself is a realization
weak equivalence, and its two projection equations are recorded.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory MonoidalClosed
open scoped MonoidalCategory SSet.modelCategoryQuillen

namespace SSet

/-- The original categorical product arrow is exactly the tensor-left arrow
under the two native tensor-to-product comparison isomorphisms. -/
def tensorLeftProductArrowIso (K : SSet.{u}) {X Y : SSet.{u}} (f : X ⟶ Y) :
    Arrow.mk ((tensorLeft K).map f) ≅ Arrow.mk (prod.map (𝟙 K) f) :=
  Arrow.isoMk ((CartesianMonoidalCategory.tensorLeftIsoProd K).app X)
    ((CartesianMonoidalCategory.tensorLeftIsoProd K).app Y)
    ((CartesianMonoidalCategory.tensorLeftIsoProd K).hom.naturality f).symm

/-- Actual tensor-left Quillen preservation yields product TCof without Kan factors. -/
theorem trivialCofibration_prodMap_id_left
    (K : SSet.{u}) {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : trivialCofibrations SSet.{u} f) :
    trivialCofibrations SSet.{u} (prod.map (𝟙 K) f) := by
  let : CategoryTheory.Adjunction.IsQuillenAdjunction (ihom.adjunction K) :=
    ihomAdjunction_isQuillenAdjunction_of_isCofibrant K
  have tensorTCof : trivialCofibrations SSet.{u} ((tensorLeft K).map f) :=
    (inferInstance : CategoryTheory.Adjunction.IsQuillenAdjunction
      (ihom.adjunction K)).preservesTrivialCofibrations f hf
  exact ((trivialCofibrations SSet.{u}).arrow_mk_iso_iff
    (tensorLeftProductArrowIso K f)).mp tensorTCof

/-- The exact original product braiding preserves both factor arrows. -/
def rightProductArrowIso {X Y : SSet.{u}} (f : X ⟶ Y) (K : SSet.{u}) :
    Arrow.mk (prod.map (𝟙 K) f) ≅ Arrow.mk (prod.map f (𝟙 K)) :=
  Arrow.isoMk (prod.braiding K X) (prod.braiding K Y)
    (by
      change (prod.braiding K X).hom ≫ prod.map f (𝟙 K) =
        prod.map (𝟙 K) f ≫ (prod.braiding K Y).hom
      exact (braid_natural (𝟙 K) f).symm)

/-- Right product TCof follows from the native braiding, with no fibrancy premise. -/
theorem trivialCofibration_prodMap_id_right
    {X Y : SSet.{u}} (f : X ⟶ Y) (K : SSet.{u})
    (hf : trivialCofibrations SSet.{u} f) :
    trivialCofibrations SSet.{u} (prod.map f (𝟙 K)) :=
  ((trivialCofibrations SSet.{u}).arrow_mk_iso_iff
    (rightProductArrowIso f K)).mp (trivialCofibration_prodMap_id_left K f hf)

/-- Both original factors preserve TCof; this is the literal product map. -/
theorem trivialCofibration_prodMap
    {X Y A B : SSet.{u}} (f : X ⟶ Y) (g : A ⟶ B)
    (hf : trivialCofibrations SSet.{u} f)
    (hg : trivialCofibrations SSet.{u} g) :
    trivialCofibrations SSet.{u} (prod.map f g) := by
  have left := trivialCofibration_prodMap_id_right f A hf
  have right := trivialCofibration_prodMap_id_left Y g hg
  have composite := (trivialCofibrations SSet.{u}).comp_mem _ _ left right
  have fac : prod.map f (𝟙 A) ≫ prod.map (𝟙 Y) g = prod.map f g := by
    simpa only [Category.comp_id, Category.id_comp] using prod.map_map f (𝟙 A) (𝟙 Y) g
  rwa [fac] at composite

/-- The baseline beta product is weak because beta itself is a genuine TCof. -/
theorem betaPair_realizationWeak
    {R H : SSet.{u}} (β : R ⟶ H)
    (hβ : trivialCofibrations SSet.{u} β) :
    realizationWeakEquivalences (prod.map β β) :=
  (weakEquivalence_iff _).mp
    ((mem_trivialCofibrations_iff _).mp (trivialCofibration_prodMap β β hβ hβ)).2

/-- The actual first projection of the weak beta-pair base map. -/
@[reassoc]
theorem betaPair_fst {R H : SSet.{u}} (β : R ⟶ H) :
    prod.map β β ≫ (prod.fst : H ⨯ H ⟶ H) =
      (prod.fst : R ⨯ R ⟶ R) ≫ β :=
  prod.map_fst _ _

/-- The same second projection is retained in the original order. -/
@[reassoc]
theorem betaPair_snd {R H : SSet.{u}} (β : R ⟶ H) :
    prod.map β β ≫ (prod.snd : H ⨯ H ⟶ H) =
      (prod.snd : R ⨯ R ⟶ R) ≫ β :=
  prod.map_snd _ _

end SSet
