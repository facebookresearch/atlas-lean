/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageHorizontalCycles

/-! # Tests for horizontal direct-column cycle maps -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantFirstPageHorizontalCyclesTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).cycles
        (-((p + 1 : ℕ) : ℤ) - q) ⟶
      (horizontalDirectColumnCochain K p).cycles (-(p : ℤ) - q) :=
  horizontalDirectColumnHorizontalCyclesMap K p q

example (p q : ℕ) :
    horizontalDirectColumnHorizontalCyclesMap K p q ≫
        (horizontalDirectColumnCochain K p).homologyπ (-(p : ℤ) - q) =
      (horizontalDirectColumnCochain K (p + 1)).homologyπ
          (-((p + 1 : ℕ) : ℤ) - q) ≫
        (horizontalDirectColumnHomologyIso K (p + 1) q).hom ≫
        HomologicalComplex.homologyMap (K.d (p + 1) p) q ≫
        (horizontalDirectColumnHomologyIso K p q).inv :=
  horizontalDirectColumnHorizontalCyclesMap_homologyπ K p q

example (p q : ℕ) :
    horizontalDirectColumnHorizontalCyclesMap K p q ≫
        (horizontalDirectColumnCochain K p).iCycles (-(p : ℤ) - q) =
      ((q + 1 : ℕ) : ℤ).negOnePow •
        ((horizontalDirectColumnCochain K (p + 1)).iCycles
            (-((p + 1 : ℕ) : ℤ) - q) ≫
          (horizontalDirectColumnCochainXIso K (p + 1) q).hom ≫
          (K.d (p + 1) p).f q ≫
          (horizontalDirectColumnCochainXIso K p q).inv) :=
  horizontalDirectColumnHorizontalCyclesMap_iCycles K p q

example (p q : ℕ) :
    (horizontalDirectColumnVerticalCyclesIso K p q).hom ≫
        (K.X p).iCycles q =
      (horizontalDirectColumnCochain K p).iCycles (-(p : ℤ) - q) ≫
        (horizontalDirectColumnCochainXIso K p q).hom :=
  horizontalDirectColumnVerticalCyclesIso_hom_iCycles K p q

end HomologicalComplex₂.FirstQuadrantFirstPageHorizontalCyclesTests

end
