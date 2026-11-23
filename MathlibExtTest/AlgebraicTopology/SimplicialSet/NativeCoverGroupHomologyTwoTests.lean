/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.NativeCoverGroupHomologyTwo

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

/-- The actual H0 coefficient comparison keeps the original augmentation. -/
example (X : SSet.{u}) [SSet.KanComplex X] (x : X _⦋0⦌)
    (R : AddCommGrpCat.{u}) (j : SingleObj (End (SSet.FundamentalGroupoid.mk x))) :
    (SSet.KanComplex.nativeCoverHomologyZeroCoefficientIso R X x).hom.app j =
      (SSet.KanComplex.nativeCover X x).homology₀ε R :=
  SSet.KanComplex.nativeCoverHomologyZeroCoefficientIso_hom_app R X x j

/-- The literal zero-row target is true Mathlib group H2, with the original
endomorphism group and literal large-universe integral coefficients. -/
example (X : SSet.{u}) [SSet.KanComplex X] (x : X _⦋0⦌) :
    ((SSet.bkHomologySpectralSequence
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
      (SSet.KanComplex.nativeCoverDeckFunctor X x)).page 2).X (2, 0) ≅
        (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u}).obj
          (groupHomology (Rep.trivial (ULift.{u} ℤ)
            (End (SSet.FundamentalGroupoid.mk x)) (ULift.{u} ℤ)) 2) :=
  SSet.KanComplex.nativeCoverSecondPageZeroRowGroupHomologyIso X x 2

/-- The original H1-cover coefficient contributes vanished coinvariants,
without a simply-connected-base assumption. -/
example (X : SSet.{u}) [SSet.KanComplex X] (x : X _⦋0⦌) :
    IsZero (((SSet.bkHomologySpectralSequence
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
      (SSet.KanComplex.nativeCoverDeckFunctor X x)).page 2).X (0, 1)) :=
  SSet.KanComplex.nativeCoverSecondPageOne_isZero X x 0

/-- Original-base H2 is the only vanishing premise of the native group-H2 theorem. -/
example (X : SSet.{u}) [SSet.KanComplex X] [X.IsConnected] (x : X _⦋0⦌)
    (hX : IsZero (X.homology
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) 2)) :
    IsZero (groupHomology (Rep.trivial (ULift.{u} ℤ)
      (End (SSet.FundamentalGroupoid.mk x)) (ULift.{u} ℤ)) 2) :=
  SSet.KanComplex.nativeCoverGroupHomologyTwo_isZero X x hX

end
