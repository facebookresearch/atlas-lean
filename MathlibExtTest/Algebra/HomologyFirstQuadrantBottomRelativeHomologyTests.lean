/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantBottomRelativeHomology

/-! # Tests for bottom-relative filtration homology -/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.ComposableArrows

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantBottomRelativeHomologyTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (i : EInt) :
    (horizontalBottomStageShortComplex K i).ShortExact :=
  horizontalBottomStageShortComplex_shortExact K i

example (i : EInt) :
    QuasiIso (horizontalBottomMappingConeToStage K i) :=
  horizontalBottomMappingConeToStage_quasiIso K i

example (i : EInt) (n : ℕ) :
    ((horizontalCompleteFiltrationSpectralObject K).H (-(n : ℤ))).obj
        (mk₁ (horizontalBottomToStageMap i)) ≅
      (horizontalCompleteFilteredTotalComplex K i).homology n :=
  horizontalBottomRelativeHomologyStageIso K i n

example {i j : EInt} (h : i ≤ j) (n : ℕ) :
    ((horizontalCompleteFiltrationSpectralObject K).H (-(n : ℤ))).map
        (twoδ₂Toδ₁
          (horizontalBottomToStageMap i)
          (homOfLE h)
          (horizontalBottomToStageMap j)
          (Subsingleton.elim _ _)) ≫
      (horizontalBottomRelativeHomologyStageIso K j n).hom =
    (horizontalBottomRelativeHomologyStageIso K i n).hom ≫
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalMap K h) n :=
  horizontalBottomRelativeHomologyStageIso_naturality K h n

end HomologicalComplex₂.FirstQuadrantBottomRelativeHomologyTests

end
