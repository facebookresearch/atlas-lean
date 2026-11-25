/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monad.ReflexiveCocompleteness
public import Mathlib.Tactic.Linter

/-!
# Full variable clients for reflexive monadic cocompleteness

The source, target and diagram object and Hom universes are independent.
Only source colimits and target reflexive coequalizers are supplied. In
particular, target coproducts and pushouts are constructed rather than
assumed. The original free objects, unit section, Beck projections and
arbitrary cocones remain in the colimit readbacks.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v uD vD uJ vJ

open CategoryTheory Limits

namespace CategoryTheory.Monad.ReflexiveCocompleteness.Clients

variable {C : Type u} [Category.{v} C] (T : Monad C)
  {J : Type uJ} [Category.{vJ} J] [HasColimitsOfShape J C]
  [HasReflexiveCoequalizers (Algebra T)] (K : J ⥤ Algebra T)

/-- The full original arbitrary diagram has the constructed colimit universal property. -/
def originalDiagramColimit : IsColimit (colimitCocone T K) := colimitCoconeIsColimit T K

/-- Every original object retains its exact Beck projection and free colimit leg. -/
theorem originalLeg (j : J) :
    FreeCoequalizer.π (K.obj j) ≫ (colimitCocone T K).ι.app j =
      T.free.map (colimit.ι (underlyingDiagram T K) j) ≫ quotientMap T K :=
  presentationLeg_π T K j

omit [HasReflexiveCoequalizers (Algebra T)] in
/-- The actual unit-induced section equalizes the original action relation. -/
theorem originalUpperSection : relationSection T K ≫ upperRelation T K = 𝟙 _ :=
  relationSection_upper T K

omit [HasReflexiveCoequalizers (Algebra T)] in
/-- That same unit-induced section also equalizes the original multiplication relation. -/
theorem originalLowerSection : relationSection T K ≫ lowerRelation T K = 𝟙 _ :=
  relationSection_lower T K

/-- Every original cocone is the composite of its original legs and the unique constructed descent. -/
theorem originalUniversalFactorization (c : Cocone K) (j : J) :
    (colimitCocone T K).ι.app j ≫ (originalDiagramColimit T K).desc c = c.ι.app j :=
  (originalDiagramColimit T K).fac c j

end CategoryTheory.Monad.ReflexiveCocompleteness.Clients

namespace CategoryTheory.Monad.ReflexiveCocompleteness.Clients

variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
  {J : Type uJ} [Category.{vJ} J] [HasColimitsOfShape J C]
  (F : C ⥤ D) (U : D ⥤ C) (adj : F ⊣ U)
  [(comparison adj).IsEquivalence] [HasReflexiveCoequalizers D]

include F U adj in
/-- The exact original adjunction supplies colimits of an arbitrary diagram shape on the actual target. -/
theorem originalTargetColimits : HasColimitsOfShape J D :=
  hasColimitsOfShapeOfAdjunction F U adj

end CategoryTheory.Monad.ReflexiveCocompleteness.Clients

namespace CategoryTheory.Monad.ReflexiveCocompleteness.Clients

variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
  [HasColimitsOfSize.{vJ, uJ} C]
  (F : C ⥤ D) (U : D ⥤ C) (adj : F ⊣ U)
  [(comparison adj).IsEquivalence] [HasReflexiveCoequalizers D]

include F U adj in
/-- Full cocompleteness requires no target arbitrary coproduct, pushout, or colimit outcome. -/
theorem originalTargetCocomplete : HasColimitsOfSize.{vJ, uJ} D :=
  hasColimitsOfSizeOfAdjunction F U adj

end CategoryTheory.Monad.ReflexiveCocompleteness.Clients

#print axioms CategoryTheory.Monad.ReflexiveCocompleteness.relationSection_upper
#print axioms CategoryTheory.Monad.ReflexiveCocompleteness.relationSection_lower
#print axioms CategoryTheory.Monad.ReflexiveCocompleteness.colimitCoconeIsColimit
#print axioms CategoryTheory.Monad.ReflexiveCocompleteness.hasColimitsOfShape
#print axioms CategoryTheory.Monad.ReflexiveCocompleteness.hasColimitsOfSize
#print axioms CategoryTheory.Monad.ReflexiveCocompleteness.hasColimitsOfShapeOfMonadic
#print axioms CategoryTheory.Monad.ReflexiveCocompleteness.hasColimitsOfSizeOfMonadic
#print axioms CategoryTheory.Monad.ReflexiveCocompleteness.hasColimitsOfShapeOfAdjunction
#print axioms CategoryTheory.Monad.ReflexiveCocompleteness.hasColimitsOfSizeOfAdjunction

#lint only unusedArguments in MathlibExt.CategoryTheory.Monad.ReflexiveCocompleteness
