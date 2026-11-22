/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.ShiftCotensorAction

/-!
# Unit compatibility of symmetric shifts

Shifting by the tensor unit is related to the unshifted index action through the right
unitor. The file proves the index-label equation and its corresponding equation for the
entire enriched operator action, retaining the sphere coefficient map.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace NativeOmegaRecovery.NativeSymmetricShiftUnit

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal

open PointedCGWH.SymmetricModulePresentation

/-- Every original shifted coefficient label retains the complete chosen index right unitor. -/
theorem label_rightUnitor (a n k : Operad.SmallFinBijGroupoid) (f : a ⊗ n ⟶ k) :
    PointedCGWH.SymmetricShift.label (𝟙_ Operad.SmallFinBijGroupoid) n k a f ≫ (ρ_ k).hom =
      (a ◁ (ρ_ n).hom) ≫ f := by
  simp only [PointedCGWH.SymmetricShift.label, tensorHom_id, Category.assoc]
  rw [rightUnitor_naturality]
  monoidal

/-- The same actual native labelled shift action with all native endpoints explicit. -/
def shiftedArrow (E : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v})
    (r a n k : Operad.SmallFinBijGroupoid) (f : a ⊗ n ⟶ k) :
    PointedCGWH.sphereSequence.{u, v}.functor.obj a ⊗
      E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} (n ⊗ r)) ⟶
        E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} (k ⊗ r)) :=
  reconstructedArrowAction ((PointedCGWH.SymmetricShift.functor.{u, v} r).obj E) a n k f

/-- The original ordinary index action with its actual two native levels explicit. -/
def ordinaryMap (E : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) {n k : Operad.SmallFinBijGroupoid} (f : n ⟶ k) :
    E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n) ⟶
      E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} k) :=
  ((PointedCGWH.symmetricSequenceRestriction.{u, v}).obj E).functor.map f

/-- Every labelled native unit-shift action retains the actual original unitor source and target. -/
theorem arrow_rightUnitor (E : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v})
    (a n k : Operad.SmallFinBijGroupoid) (f : a ⊗ n ⟶ k) :
    shiftedArrow E (𝟙_ Operad.SmallFinBijGroupoid) a n k f ≫ ordinaryMap E (ρ_ k).hom =
      (PointedCGWH.sphereSequence.{u, v}.functor.obj a ◁ ordinaryMap E (ρ_ n).hom) ≫
        reconstructedArrowAction E a n k f := by
  have hShift := NativeOmegaPreparation.NativeSymmetricShiftCotensorAction.shift_arrow
    E (𝟙_ I) a n k f
  have hTarget := reconstructedArrowAction_target E a (n ⊗ (𝟙_ I))
    (k ⊗ (𝟙_ I)) k (PointedCGWH.SymmetricShift.label (𝟙_ I) n k a f) (ρ_ k).hom
  have hLabel := congrArg (reconstructedArrowAction E a (n ⊗ (𝟙_ I)) k)
    (label_rightUnitor a n k f)
  have hInput := reconstructedArrowAction_input E a (n ⊗ (𝟙_ I)) n k (ρ_ n).hom f
  exact (congrArg (fun g => g ≫ ordinaryMap E (ρ_ k).hom) hShift).trans
    (hTarget.trans (hLabel.trans hInput.symm))

end NativeOmegaRecovery.NativeSymmetricShiftUnit
