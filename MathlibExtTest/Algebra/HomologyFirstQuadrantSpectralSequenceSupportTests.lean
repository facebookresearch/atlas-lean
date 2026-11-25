/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantSpectralSequenceSupport

/-! # Tests for first-quadrant spectral-sequence support -/

@[expose] public section

open CategoryTheory Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantSpectralSequenceSupportTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example {i j : EInt} (h : i ≤ j) :
    Mono (horizontalCompleteFilteredTotalMap K h) :=
  inferInstance

example {i j : EInt} (h : i ≤ j) :
    Mono ((horizontalCompleteFiltrationCochainDiagram K).map (homOfLE h)) :=
  inferInstance

example :
    (horizontalCompleteFiltrationSpectralObject K).HasSpectralSequence
      CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological :=
  inferInstance

example : SpectralSequence C
    (fun r => ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩) 1 :=
  horizontalFirstQuadrantSpectralSequence K

end HomologicalComplex₂.FirstQuadrantSpectralSequenceSupportTests

end
