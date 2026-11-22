/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningCofibrations
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterMonomorphisms

/-!
# Actual original mixed marked face and scalar parameter cells

The whole original marked parameter pushout retains both original side
images, all inherited marks and the same base map. Native straightening
preserves its actual full enriched colimit and both unchanged side maps.
Every original mono parameter and marked mono source therefore give
the genuine projective left class on the same native mixed corner.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory coefficientMarkedModelCategory

/-- Actual native straightening preserves the same original whole marked parameter pushout as a genuine full
enriched colimit, with its original pushout point and maps retained. -/
def nativeStraighteningParameterPushoutIsColimit (B : SSet.{u}) {A D : SSet.{u}}
    {X Y : Over (max B)} (a : A ⟶ D) (i : X ⟶ Y) :
    IsColimit ((nativeStraightening B).mapCocone
      (PushoutCocone.mk (overParameterPushout a i).inl (overParameterPushout a i).inr
        (overParameterPushout a i).isPushout.w)) := by
  let T := nativeStraightening B
  let _ : PreservesColimitsOfSize.{0, 0} T := (nativeStraighteningAdjunction B).leftAdjoint_preservesColimits
  exact isColimitOfPreserves T (overParameterPushout a i).isPushout.isColimit

/-- The same original parameter-side map retains exactly its original native straightened mixed-cell attaching
composite. -/
theorem nativeStraightening_parameterPushout_inl (B : SSet.{u}) {A D : SSet.{u}}
    {X Y : Over (max B)} (a : A ⟶ D) (i : X ⟶ Y) :
    (nativeStraightening B).map (overParameterPushout a i).inl ≫
        (nativeStraightening B).map (overParameterPushoutProduct a i) =
      (nativeStraightening B).map ((overParameterFunctor (max B) Y).map a) :=
  ((nativeStraightening B).map_comp (overParameterPushout a i).inl (overParameterPushoutProduct a i)).symm.trans
    (congrArg (nativeStraightening B).map (overParameterPushout a i).inl_ι)

/-- The same original marked-source side map retains exactly its whole original native straightened mixed-cell
attaching composite. -/
theorem nativeStraightening_parameterPushout_inr (B : SSet.{u}) {A D : SSet.{u}}
    {X Y : Over (max B)} (a : A ⟶ D) (i : X ⟶ Y) :
    (nativeStraightening B).map (overParameterPushout a i).inr ≫
        (nativeStraightening B).map (overParameterPushoutProduct a i) =
      (nativeStraightening B).map ((overParameterBifunctor (max B)).map i |>.app D) :=
  ((nativeStraightening B).map_comp (overParameterPushout a i).inr (overParameterPushoutProduct a i)).symm.trans
    (congrArg (nativeStraightening B).map (overParameterPushout a i).inr_ι)

/-- Every whole original marked mono source and monic original scalar parameter give the genuine projective left
class on the same actual native straightened parameter corner, with no Kan condition on the scalar or base. -/
theorem nativeStraightening_parameterCell_projectiveLeft (B : SSet.{u}) {A D : SSet.{u}}
    {X Y : Over (max B)} (a : A ⟶ D) (i : X ⟶ Y) [Mono a] [Mono i] :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos).rlp.llp
      ((nativeStraightening B).map (overParameterPushoutProduct a i)) := by
  have : Mono (overParameterPushoutProduct a i) := overParameterPushoutProduct_mono a i
  exact nativeStraightening_mono_projectiveLeft B (overParameterPushoutProduct a i)

/-- The same whole original native mixed marked parameter cell is a cofibration in the actual original coherent
diagram model. -/
theorem nativeStraightening_parameterCell_cofibration (B : SSet.{u}) {A D : SSet.{u}}
    {X Y : Over (max B)} (a : A ⟶ D) (i : X ⟶ Y) [Mono a] [Mono i] :
    let _ := coherentDiagramModelCategory B
    Cofibration ((nativeStraightening B).map (overParameterPushoutProduct a i)) := by
  let _ := coherentDiagramModelCategory B
  rw [cofibration_iff, coherentDiagramModel_cofibrations B]
  exact nativeStraightening_parameterCell_projectiveLeft B a i

/-- Every actual marked evaluation coefficient of the same original native mixed parameter cell is genuinely
cofibrant as its original whole coefficient map. -/
theorem nativeStraightening_parameterCell_evaluation_cofibration (B : SSet.{u}) {A D : SSet.{u}}
    {X Y : Over (max B)} (a : A ⟶ D) (i : X ⟶ Y) [Mono a] [Mono i] (x : (realization B)ᵒᵖ) :
    cofibrations Marked.{u} (((nativeStraightening B).map (overParameterPushoutProduct a i)).app x) :=
  coherentDiagram_projectiveLeft_evaluation_cofibration B
    ((nativeStraightening B).map (overParameterPushoutProduct a i))
      (nativeStraightening_parameterCell_projectiveLeft B a i) x

end SSet.Marked
