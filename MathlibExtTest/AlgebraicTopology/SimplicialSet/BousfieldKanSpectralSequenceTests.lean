/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanSpectralSequence

/-! # Tests for the Bousfield--Kan homology spectral sequence -/

@[expose] public section

open CategoryTheory Limits Opposite
open scoped Simplicial

noncomputable section

universe w

namespace SSet.BousfieldKanSpectralSequenceTests

variable {J : Type w} [Category.{0} J]

example (R : AddCommGrpCat.{w}) (D : J ⥤ SSet.{w}) (n : ℕ) :
    (bkAlternatingTotalComplex AddCommGrpCat.{w} R D).homology n ≅
      (bkHocolimAlternatingComplex R D).homology n :=
  bkTotalHocolimHomologyIso R D n

example (R : AddCommGrpCat.{w}) (D : J ⥤ SSet.{w}) (p q : ℕ) :
    ((bkHomologySpectralSequence R D).page 2).X (p, q) ≅
      CategoryTheory.CategoryHomology.homologyWithCoefficients
        (D ⋙ SSet.homologyFunctor R q) p :=
  bkSecondPageCoefficientHomologyIso R D p q

example (R : AddCommGrpCat.{w}) (D : J ⥤ SSet.{w})
    (r : ℤ) (hr : 1 ≤ r) (p q : ℕ)
    (hlower : (p : ℤ) + 1 ≤ r) (hupper : (q : ℤ) + 2 ≤ r) :
    ((bkHomologySpectralSequence R D).page r).X (p, q) ≅
      bkTotalHomologyGradedPiece R D p q :=
  bkStablePageGradedIso R D r hr p q hlower hupper

end SSet.BousfieldKanSpectralSequenceTests

namespace CategoryTheory.Functor.IsCofibered.BousfieldKanSpectralSequenceTests

variable {S X : Type w} [Category.{0} S] [Category.{0} X]
  {f : X ⥤ S} [f.IsCofibered]

example (R : AddCommGrpCat.{w}) (pDegree qDegree : ℕ) :
    ((SSet.bkHomologySpectralSequence R
      (SSet.rightCommaNerveDiagram f)).page 2).X (pDegree, qDegree) ≅
      fiberHomologyCategoryHomology (p := f) AddCommGrpCat.{w} R
        pDegree qDegree :=
  cofiberedBKSecondPageIso (f := f) R pDegree qDegree

end CategoryTheory.Functor.IsCofibered.BousfieldKanSpectralSequenceTests

end
