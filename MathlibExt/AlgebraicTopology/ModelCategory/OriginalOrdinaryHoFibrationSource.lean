/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.OriginalOrdinaryHoArrowSource
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedArrowFactorizations

/-!
# Original J-factorization representatives of all ordinary-Ho arrows

The original Q/R representative is factored by the original fixed-cardinal
J factory. Its right map is a fibration over the same original fibrant R
target. The inverse of the actual weak left leg is retained in the full
source comparison. Every complete Ho arrow is recovered by a whole Arrow
Iso, without a fibration representative or weak comparison as input.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w u v
open CategoryTheory HomotopicalAlgebra

namespace HomotopicalAlgebra.OriginalOrdinaryHoFibrationSource

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ)

local notation "H" => toHomotopyCategory C

/-- The entire factor record is the same original J algorithm on the actual Q/R representative. -/
def factor {X Y : HomotopyCategory C} (f : X ⟶ Y) :
    MorphismProperty.MapFactorizationData (trivialCofibrations C) (fibrations C)
      (OriginalOrdinaryHoArrowSource.representative g f) :=
  (GeneratedArrowFactorizations.fibrant g).factorizationData
    (OriginalOrdinaryHoArrowSource.representative g f)

/-- The actual source object is the original J middle object. -/
def sourceObject {X Y : HomotopyCategory C} (f : X ⟶ Y) : C := (factor g f).Z

/-- The complete actual fibration keeps the original R target. -/
def projection {X Y : HomotopyCategory C} (f : X ⟶ Y) :
    sourceObject g f ⟶ OriginalOrdinaryHoArrowSource.targetObject g Y := (factor g f).p

/-- Original J generation earns the entire right-factor fibration. -/
theorem projection_fibration {X Y : HomotopyCategory C} (f : X ⟶ Y) :
    Fibration (projection g f) :=
  (fibration_iff _).mpr (factor g f).hp

/-- The original left J leg is both a cofibration and weak, with no added source assertion. -/
theorem left_trivialCofibration {X Y : HomotopyCategory C} (f : X ⟶ Y) :
    trivialCofibrations C (factor g f).i := (factor g f).hi

/-- The full source comparison retains the inverse actual weak J leg and original Q/preimage Iso. -/
def sourceIso {X Y : HomotopyCategory C} (f : X ⟶ Y) : (H).obj (sourceObject g f) ≅ X := by
  let : IsIso ((H).map (factor g f).i) :=
    Localization.inverts (H) (weakEquivalences C) _ (left_trivialCofibration g f).2
  exact (asIso ((H).map (factor g f).i)).symm ≪≫ OriginalOrdinaryHoArrowSource.sourceIso g X

/-- Both original factor maps reconstruct the same complete original representative. -/
theorem factor_fac {X Y : HomotopyCategory C} (f : X ⟶ Y) :
    (factor g f).i ≫ projection g f = OriginalOrdinaryHoArrowSource.representative g f :=
  (factor g f).fac

/-- The full J-fibration square retains the entire original caller Ho function. -/
theorem projection_square {X Y : HomotopyCategory C} (f : X ⟶ Y) :
    (H).map (projection g f) ≫ (OriginalOrdinaryHoArrowSource.targetIso g Y).hom =
      (sourceIso g f).hom ≫ f := by
  let : IsIso ((H).map (factor g f).i) :=
    Localization.inverts (H) (weakEquivalences C) _ (left_trivialCofibration g f).2
  apply (cancel_epi ((H).map (factor g f).i)).mp
  unfold sourceIso
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv]
  rw [← Category.assoc, ← Functor.map_comp, factor_fac,
    OriginalOrdinaryHoArrowSource.representative_fac]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, IsIso.hom_inv_id_assoc]

/-- Every complete caller Ho arrow is the same whole Arrow Iso of an actual original J fibration. -/
def fibrationArrowIso {X Y : HomotopyCategory C} (f : X ⟶ Y) :
    Arrow.mk ((H).map (projection g f)) ≅ Arrow.mk f :=
  Arrow.isoMk' ((H).map (projection g f)) f (sourceIso g f)
    (OriginalOrdinaryHoArrowSource.targetIso g Y) (projection_square g f).symm

end HomotopicalAlgebra.OriginalOrdinaryHoFibrationSource
