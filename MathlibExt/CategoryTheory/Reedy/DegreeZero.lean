/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Reedy.FactorizationCorners
public import MathlibExt.AlgebraicTopology.ModelCategory.FramingCoefficientFactory
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Exact original endpoints in the least Reedy degree

Both original boundary categories at a least-degree object are empty. The actual
coefficient arrow is therefore Arrow-isomorphic to the original component arrow.
Identity normalization of the original coefficient factory fixes the corresponding
whole source or target endpoint, including its original natural factor map.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uJ vJ uD uC vC

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.ReedyStructure.StageFactory

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] [OrderBot D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPushouts C] [HasPullbacks C]
  {X Y : J ⥤ C} (f : X ⟶ Y)
  (L : MapFactorizationData (⊤ : MorphismProperty (r.Below (⊥ : D) ⥤ C)) ⊤
    (Functor.whiskerLeft (r.belowObjects (⊥ : D)).ι f))

omit [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPushouts C] [HasPullbacks C] in
/-- The original least-degree latching comparison is between actual initial objects. -/
theorem latchingI_isIso_at_bot (j : J) (hj : r.degree j = ⊥) :
    IsIso (latchingI r f L j hj) := by
  let _ : IsEmpty (r.Latching j) := ⟨fun a ↦ by
    have ha := a.property
    change r.degree (r.latchingSource a) < r.degree j at ha
    rw [hj] at ha
    exact not_lt_bot ha⟩
  exact isIso_of_isInitial
    (isColimitEquivIsInitialOfIsEmpty C (colimit.cocone (r.latchingDiagram X j))
      (colimit.isColimit _))
    (isColimitEquivIsInitialOfIsEmpty C (colimit.cocone (r.lowerLatchingDiagram L.Z j hj))
      (colimit.isColimit _)) _

omit [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPushouts C] [HasPullbacks C] in
/-- The original least-degree matching comparison is between actual terminal objects. -/
theorem matchingP_isIso_at_bot (j : J) (hj : r.degree j = ⊥) :
    IsIso (matchingP r f L j hj) := by
  let _ : IsEmpty (r.Matching j) := ⟨fun a ↦ by
    have ha := a.property
    change r.degree (r.matchingTarget a) < r.degree j at ha
    rw [hj] at ha
    exact not_lt_bot ha⟩
  exact isIso_of_isTerminal
    (isLimitEquivIsTerminalOfIsEmpty C (limit.cone (r.lowerMatchingDiagram L.Z j hj))
      (limit.isLimit _))
    (isLimitEquivIsTerminalOfIsEmpty C (limit.cone (r.matchingDiagram Y j))
      (limit.isLimit _)) _

/-- The whole actual least-degree coefficient arrow retains the original component arrow. -/
def coefficientArrowIsoAtBot (j : J) (hj : r.degree j = ⊥) :
    Arrow.mk (coefficientMap r f L j hj) ≅ Arrow.mk (f.app j) := by
  letI := latchingI_isIso_at_bot r f L j hj
  letI := matchingP_isIso_at_bot r f L j hj
  let i := pushout.inl (ReedyStructure.latchingMap r X j) (latchingI r f L j hj)
  let p := pullback.snd (matchingP r f L j hj) (ReedyStructure.matchingMap r Y j)
  letI : IsIso i := by dsimp only [i]; infer_instance
  letI : IsIso p := by dsimp only [p]; infer_instance
  exact Arrow.isoMk' (coefficientMap r f L j hj) (f.app j) (asIso i).symm (asIso p) (by
    change inv i ≫ f.app j = coefficientMap r f L j hj ≫ p
    apply (cancel_epi i).1
    rw [IsIso.hom_inv_id_assoc]
    exact (coefficientMap_inl_snd r f L j hj).symm)

/-- The whole coefficient Arrow comparison retains its original inverse source injection. -/
theorem coefficientArrowIso_at_bot_hom_left (j : J) (hj : r.degree j = ⊥) :
    (coefficientArrowIsoAtBot r f L j hj).hom.left =
      @inv C _ _ _
        (pushout.inl (ReedyStructure.latchingMap r X j) (latchingI r f L j hj))
        (by let _ := latchingI_isIso_at_bot r f L j hj; infer_instance) := rfl

/-- The same whole coefficient Arrow comparison retains its original target projection. -/
theorem coefficientArrowIso_at_bot_hom_right (j : J) (hj : r.degree j = ⊥) :
    (coefficientArrowIsoAtBot r f L j hj).hom.right =
      pullback.snd (matchingP r f L j hj) (ReedyStructure.matchingMap r Y j) := rfl

/-- An original least-degree component isomorphism makes its actual coefficient an isomorphism. -/
theorem coefficientMap_isIso_at_bot (j : J) (hj : r.degree j = ⊥) [IsIso (f.app j)] :
    IsIso (coefficientMap r f L j hj) :=
  ((isomorphisms C).arrow_mk_iso_iff (coefficientArrowIsoAtBot r f L j hj)).mpr
    (inferInstance : IsIso (f.app j))

section TargetNormalization

variable {P Q : MorphismProperty C} [P.ContainsIdentities] [P.RespectsIso]
  [Q.ContainsIdentities] (F : FactorizationData P Q)

/-- Target identity normalization keeps the actual original target at the least degree. -/
theorem normalizedTarget_nextP_isIso_at_bot (j : J) (hj : r.degree j = ⊥)
    [IsIso (f.app j)] :
    IsIso ((nextPrefix r f L (FactorizationData.normalizeTarget F)).p.app
      (⟨j, hj.le⟩ : r.Through (⊥ : D))) := by
  let _ := matchingP_isIso_at_bot r f L j hj
  let _ := coefficientMap_isIso_at_bot r f L j hj
  rw [StageCornerMaps.nextP_new r f L (FactorizationData.normalizeTarget F)
    (⟨j, hj.le⟩ : r.Through (⊥ : D)) hj, newP]
  infer_instance

end TargetNormalization

section SourceNormalization

variable {P Q : MorphismProperty C} [P.ContainsIdentities] [Q.ContainsIdentities]
  [Q.RespectsIso] (F : FactorizationData P Q)

/-- Source identity normalization keeps the actual original source at the least degree. -/
theorem normalizedSource_nextI_isIso_at_bot (j : J) (hj : r.degree j = ⊥)
    [IsIso (f.app j)] :
    IsIso ((nextPrefix r f L (FactorizationData.normalizeSource F)).i.app
      (⟨j, hj.le⟩ : r.Through (⊥ : D))) := by
  let _ := latchingI_isIso_at_bot r f L j hj
  let _ := coefficientMap_isIso_at_bot r f L j hj
  rw [StageCornerMaps.nextI_new r f L (FactorizationData.normalizeSource F)
    (⟨j, hj.le⟩ : r.Through (⊥ : D)) hj, newI]
  infer_instance

end SourceNormalization

end CategoryTheory.ReedyStructure.StageFactory

namespace CategoryTheory.ReedyStructure.DegreeFactorization

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] [OrderBot D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPushouts C] [HasPullbacks C]
  {X Y : J ⥤ C} (f : X ⟶ Y)

/-- The complete normalized global factor keeps its original right endpoint at the least degree. -/
theorem normalizedTarget_factor_p_isIso_at_bot {P Q : MorphismProperty C}
    [P.ContainsIdentities] [P.RespectsIso] [Q.ContainsIdentities]
    (F : FactorizationData P Q) (j : J) (hj : r.degree j = ⊥) [IsIso (f.app j)] :
    IsIso ((factor r f (FactorizationData.normalizeTarget F)).p.app j) := by
  change IsIso (PrefixGluing.coefficient
    (factor r f (FactorizationData.normalizeTarget F)) j).p
  rw [factor_coefficient r f (FactorizationData.normalizeTarget F) j (⊥ : D) hj.le,
    prefixAt_eq_nextPrefix]
  exact StageFactory.normalizedTarget_nextP_isIso_at_bot r f
    (lowerAt r f (FactorizationData.normalizeTarget F) (⊥ : D)) F j hj

/-- The complete normalized global factor keeps its original left endpoint at the least degree. -/
theorem normalizedSource_factor_i_isIso_at_bot {P Q : MorphismProperty C}
    [P.ContainsIdentities] [Q.ContainsIdentities] [Q.RespectsIso]
    (F : FactorizationData P Q) (j : J) (hj : r.degree j = ⊥) [IsIso (f.app j)] :
    IsIso ((factor r f (FactorizationData.normalizeSource F)).i.app j) := by
  change IsIso (PrefixGluing.coefficient
    (factor r f (FactorizationData.normalizeSource F)) j).i
  rw [factor_coefficient r f (FactorizationData.normalizeSource F) j (⊥ : D) hj.le,
    prefixAt_eq_nextPrefix]
  exact StageFactory.normalizedSource_nextI_isIso_at_bot r f
    (lowerAt r f (FactorizationData.normalizeSource F) (⊥ : D)) F j hj

end CategoryTheory.ReedyStructure.DegreeFactorization
