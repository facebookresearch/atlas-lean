/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanSourceWeakEquivalenceCommonUniverse
public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHomotopyInvarianceUniverses
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanTotalHomotopyNatural
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceHomotopyInvariance

/-!
# Genuine right-comma Quillen A in the actual native common universe

The existing original comma source-total augmentation is weak for the
independent native object and Hom levels. Objectwise actual comma-to-point
weakness gives the SAME target-total weakness. The full original native
cylinder and two-out-of-three yield the original full nerve map weak.
-/

@[expose] public section


noncomputable section
universe u v w
open CategoryTheory MorphismProperty
namespace SSet
variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

/-- The SAME original native target-total map is weak from all actual original comma-to-point components. -/
lemma rightCommaTotalToTarget_weak_commonUniverse
    (F : C ⥤ D)
    (hPoint : ∀ d : D, realizationWeakEquivalences ((rightCommaToPoint.{u, v, w} F).app d)) :
    realizationWeakEquivalences (rightCommaTotalToTarget.{u, v, w} F) := by
  let η := rightCommaToPoint.{u, v, w} F
  have hTotal : realizationWeakEquivalences (bkHocolimMap η) :=
    bkHocolimMap_weak_universes η hPoint
  have hComparison : realizationWeakEquivalences (bkPointIsoNerve.{u, max v w} D).hom :=
    realizationWeakEquivalences.of_isIso (bkPointIsoNerve.{u, max v w} D).hom
  exact realizationWeakEquivalences.comp_mem (bkHocolimMap η)
    (bkPointIsoNerve.{u, max v w} D).hom hTotal hComparison

/-- The full original native comma-total source route is weak from the SAME actual all-comma hypothesis. -/
lemma rightCommaTotalSourceRoute_weak_commonUniverse
    (F : C ⥤ D)
    (hPoint : ∀ d : D, realizationWeakEquivalences ((rightCommaToPoint.{u, v, w} F).app d)) :
    realizationWeakEquivalences
      (rightCommaTotalToSource.{u, v, w} F ≫ nerveMapCommonHom.{u, w, v} F) := by
  have hTarget : realizationWeakEquivalences (rightCommaTotalToTarget.{u, v, w} F) :=
    rightCommaTotalToTarget_weak_commonUniverse F hPoint
  exact (realizationWeakEquivalences_iff_of_homotopy (rightCommaTotalHomotopy.{u, v, w} F)).mpr hTarget

/-- Genuine native common-universe Quillen A from weakness of EVERY actual original right comma nerve. -/
theorem nerveMapCommonHom_weak_of_rightComma
    (F : C ⥤ D)
    (hPoint : ∀ d : D, realizationWeakEquivalences ((rightCommaToPoint.{u, v, w} F).app d)) :
    realizationWeakEquivalences (nerveMapCommonHom.{u, w, v} F) := by
  have hSource : realizationWeakEquivalences (rightCommaTotalToSource.{u, v, w} F) :=
    rightCommaTotalToSource_mem_realizationWeakEquivalences_commonUniverse.{u, v, w} F
  have hComposite : realizationWeakEquivalences
      (rightCommaTotalToSource.{u, v, w} F ≫ nerveMapCommonHom.{u, w, v} F) :=
    rightCommaTotalSourceRoute_weak_commonUniverse F hPoint
  exact realizationWeakEquivalences.of_precomp (rightCommaTotalToSource.{u, v, w} F)
    (nerveMapCommonHom.{u, w, v} F) hSource hComposite

end SSet
