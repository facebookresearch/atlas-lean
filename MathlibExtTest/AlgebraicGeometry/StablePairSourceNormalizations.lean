/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.StablePairObstructionMaps
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Stable-pair sign and nonreduced-parameter probes

These tests retain the original section sign and exercise an actual
dual-number parameter, with its nonzero square-zero element.
No reducedness or geometric-point restriction is added to reindexing.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.StablePairSourceNormalizations

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open StablePairFamilies StablePairParameterPullbacks CoherentCurveLinearSeries

def dualNumberParameter : Over (Spec (.of ℂ)) :=
  Over.mk (Spec.algebraMap ℂ (TrivSqZeroExt ℂ ℂ))

def epsilon : TrivSqZeroExt ℂ ℂ := TrivSqZeroExt.inr 1

example : epsilon * epsilon = 0 := TrivSqZeroExt.inr_mul_inr ℂ (1 : ℂ) 1

example : epsilon ≠ 0 := by
  intro h
  have h' : (1 : ℂ) = 0 :=
    TrivSqZeroExt.inr_injective (R := ℂ) (by simpa [epsilon] using h)
  exact one_ne_zero h'

def identityPair (X : Over (Spec (.of ℂ))) : RawPair X dualNumberParameter :=
  ⟨structureModule (total X dualNumberParameter),𝟙 _⟩

example (X : Over (Spec (.of ℂ))) :
    zeroInclusion (identityPair X) ≫ (complex (identityPair X)).d 0 1 ≫
      oneProjection (identityPair X) = 𝟙 (structureModule (total X dualNumberParameter)) :=
  complex_differential (identityPair X)

example (X P : Over (Spec (.of ℂ))) (f : dualNumberParameter ⟶ P) (F : RawPair X P) :
    (rawReindex f F).sectionMap =
      LineBundleTaskContracts.pullbackSection (productMap X f) F.sectionMap := rfl

example (X P : Over (Spec (.of ℂ))) (F : RawPair X P) :
    zeroInclusion F ≫ (complex F).d 0 1 ≫ oneProjection F = F.sectionMap :=
  complex_differential F

end MathlibExtTest.AlgebraicGeometry.StablePairSourceNormalizations
