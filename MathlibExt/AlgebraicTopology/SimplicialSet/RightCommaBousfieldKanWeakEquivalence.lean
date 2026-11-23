/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHomotopyInvariance
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceHomotopyInvariance
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanTotalHomotopyNatural

/-!
# Weak-equivalence adapter for the right-comma BK target map

An objectwise realization weak equivalence from every right-comma nerve to
the point diagram induces a realization weak equivalence on BK totals.  The
canonical point-total comparison is an isomorphism, so their composite is the
already-defined map from the right-comma total to `nerve D`.

This conditional adapter does not prove that comma nerves are contractible
and makes no Quillen-Theorem-A or homotopy-fiber claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory MorphismProperty

namespace SSet

universe u

variable {C D : Type u} [Category.{0} C] [Category.{0} D]

/-- Objectwise realization weak equivalence of the right-comma-to-point map
implies realization weak equivalence of the induced target-total map. -/
theorem rightCommaTotalToTarget_mem_realizationWeakEquivalences
    (F : C ⥤ D)
    (hPoint : ∀ d, realizationWeakEquivalences
      ((rightCommaToPoint F).app d)) :
    realizationWeakEquivalences (rightCommaTotalToTarget F) := by
  have hTotal : realizationWeakEquivalences
      (bkHocolimMap (rightCommaToPoint F)) :=
    bkHocolimMap_mem_realizationWeakEquivalences
      (rightCommaToPoint F) hPoint
  have hComparison : realizationWeakEquivalences
      (bkPointIsoNerve D).hom :=
    realizationWeakEquivalences.of_isIso (bkPointIsoNerve D).hom
  have hComposite : realizationWeakEquivalences
      (bkHocolimMap (rightCommaToPoint F) ≫ (bkPointIsoNerve D).hom) :=
    realizationWeakEquivalences.comp_mem _ _ hTotal hComparison
  change realizationWeakEquivalences
    (bkHocolimMap (rightCommaToPoint F) ≫ (bkPointIsoNerve D).hom)
  exact hComposite

/-- Under the same objectwise hypothesis, the homotopic source route through
the comma projection is also a realization weak equivalence.  This statement
does not cancel `rightCommaTotalToSource F`; no weak-equivalence theorem for
that augmentation is asserted here. -/
theorem rightCommaTotalToSource_comp_nerveMap_mem_realizationWeakEquivalences
    (F : C ⥤ D)
    (hPoint : ∀ d, realizationWeakEquivalences
      ((rightCommaToPoint F).app d)) :
    realizationWeakEquivalences
      (rightCommaTotalToSource F ≫ nerveMap F) := by
  have hTarget : realizationWeakEquivalences
      (rightCommaTotalToTarget F) :=
    rightCommaTotalToTarget_mem_realizationWeakEquivalences F hPoint
  exact (realizationWeakEquivalences_iff_of_homotopy
    (rightCommaTotalHomotopy F)).mpr hTarget

end SSet

end
