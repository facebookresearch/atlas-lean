/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.OriginalSmithModel
import MathlibExt.AlgebraicTopology.ModelCategory.InjectiveDiagramEvaluation
import MathlibExt.AlgebraicTopology.ModelCategory.Proper

/-!
# Properness of the actual original injective model

The source is HTT, author version April 9, 2017, Remark A.2.8.4,
printed page 832/PDF page 850. Original free coefficient-J maps give the
actual component lifting tests; evaluation uses the same original diagram
pushouts and pullbacks. All original index objects, Hom labels and roots
remain unchanged.
-/

set_option autoImplicit false
noncomputable section

universe w uD vD uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.Presentable.HomPowerAccessibility

namespace HomotopicalAlgebra.FunctorInjective

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {kappa : Cardinal.{w}} [Fact kappa.IsRegular]
  [OrderBot kappa.ord.ToType] (d : CofibrantGenerationData C kappa)
  (kappaLP : Cardinal.{w}) [Fact kappaLP.IsRegular]
  [IsCardinalLocallyPresentable C kappaLP] (s : Functor.EssentialIndexData.{w} D C)

/-- Every actual constructed injective fibration is a coefficient fibration at every
original index object. No objectwise-fibration dictionary is supplied. -/
theorem originalInjectiveModel_fibrations_le_objectwise :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP s
    fibrations (D ⥤ C) ≤ (fibrations C).functorCategory D := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP s
  let _ : LocallySmall.{w} D := s.locallySmallIndex
  let _ : HasCoproducts.{w} C := d.J_smallObject.hasCoproducts
  rw [originalInjectiveModel_fibrations d kappaLP s]
  exact (injectiveDiagram_rightClasses_le_pointwise D C).1

/-- Original coefficient left properness gives left properness of the actual model. -/
theorem originalInjectiveModel_isLeftProper [IsLeftProper C] :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP s
    IsLeftProper (D ⥤ C) := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP s
  refine { weakEquivalences_isStableUnderCobaseChangeAgainst_cofibrations := ?_ }
  constructor
  intro A B i hi
  constructor
  intro X Y j f' f sq hf
  rw [originalInjectiveModel_cofibrations d kappaLP s] at hi
  rw [originalSmithModel_weakEquivalences d kappaLP s] at hf ⊢
  intro a
  let _ : Cofibration (((evaluation D C).obj a).map i) := by
    change Cofibration (i.app a)
    exact (cofibration_iff _).mpr (hi a)
  let _ : WeakEquivalence (((evaluation D C).obj a).map f) := by
    change WeakEquivalence (f.app a)
    exact (weakEquivalence_iff _).mpr (hf a)
  exact (weakEquivalence_iff _).mp
    (IsLeftProper.weakEquivalence_of_isPushout (sq.map ((evaluation D C).obj a)))

/-- Original coefficient right properness gives right properness using the derived
component fibration tests and the same original pullback square. -/
theorem originalInjectiveModel_isRightProper [IsRightProper C] :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP s
    IsRightProper (D ⥤ C) := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP s
  let _ : HasPullbacks C := hasPullbacks C kappaLP
  refine { weakEquivalences_isStableUnderBaseChangeAgainst_fibrations := ?_ }
  constructor
  intro X Y p hp
  constructor
  intro Z W f' g' g sq hg
  have hpC := originalInjectiveModel_fibrations_le_objectwise d kappaLP s p hp
  rw [originalSmithModel_weakEquivalences d kappaLP s] at hg ⊢
  intro a
  let _ : Fibration (((evaluation D C).obj a).map p) := by
    change Fibration (p.app a)
    exact (fibration_iff _).mpr (hpC a)
  let _ : WeakEquivalence (((evaluation D C).obj a).map g) := by
    change WeakEquivalence (g.app a)
    exact (weakEquivalence_iff _).mpr (hg a)
  exact (weakEquivalence_iff _).mp
    (IsRightProper.weakEquivalence_of_isPullback (sq.map ((evaluation D C).obj a)))

/-- Both original coefficient properness implications hold independently on the same
constructed original functor-category model. -/
theorem originalInjectiveModel_properness :
    (IsLeftProper C →
      letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP s
      IsLeftProper (D ⥤ C)) ∧
    (IsRightProper C →
      letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP s
      IsRightProper (D ⥤ C)) := by
  constructor
  · intro h
    let _ : IsLeftProper C := h
    exact originalInjectiveModel_isLeftProper d kappaLP s
  · intro h
    let _ : IsRightProper C := h
    exact originalInjectiveModel_isRightProper d kappaLP s

end HomotopicalAlgebra.FunctorInjective
