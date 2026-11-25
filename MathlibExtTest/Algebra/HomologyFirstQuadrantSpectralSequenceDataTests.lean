/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantSpectralSequenceData

/-! # Tests for first-quadrant homological page data -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Abelian.SpectralObject.FirstQuadrantSpectralSequenceDataTests

example : SpectralSequenceDataCore EInt
    (fun r => ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩) 1 :=
  coreE₁FirstQuadrantHomological

example (pq : ℕ × ℕ) :
    coreE₁FirstQuadrantHomological.deg pq = -pq.1 - pq.2 :=
  rfl

example (pq : ℕ × ℕ) :
    coreE₁FirstQuadrantHomological.i₁ pq =
      @WithBotTop.coe ℤ ((pq.1 : ℤ) - 1) :=
  rfl

example (pq : ℕ × ℕ) :
    coreE₁FirstQuadrantHomological.i₂ pq =
      @WithBotTop.coe ℤ (pq.1 : ℤ) :=
  rfl

example : coreE₁FirstQuadrantHomological.HasFirstPageComputation :=
  inferInstance

end CategoryTheory.Abelian.SpectralObject.FirstQuadrantSpectralSequenceDataTests

end
