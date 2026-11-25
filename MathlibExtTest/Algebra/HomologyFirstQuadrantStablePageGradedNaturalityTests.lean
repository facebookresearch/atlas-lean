/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Data.ZMod.Basic
public import
  MathlibExt.Algebra.Homology.FirstQuadrantStablePageGradedNaturality

/-! # Tests for stable-page associated-graded naturality -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantStablePageGradedNaturalityTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalStablePageGradedIsoAtIndex_naturality

example (f : K ⟶ L) (p q : ℕ) :
    horizontalStablePageMapOfBicomplex f p q ≫
        (horizontalStablePageGradedIsoAtIndex L p q).hom =
      (horizontalStablePageGradedIsoAtIndex K p q).hom ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex f p q :=
  horizontalStablePageGradedIsoAtIndex_naturality f p q

-- Corner and one-sided zero-index boundaries.
example (f : K ⟶ L) :=
  horizontalStablePageGradedIsoAtIndex_naturality f 0 0

example (f : K ⟶ L) (q : ℕ) :=
  horizontalStablePageGradedIsoAtIndex_naturality f 0 q

example (f : K ⟶ L) (p : ℕ) :=
  horizontalStablePageGradedIsoAtIndex_naturality f p 0

-- At `(1,0)`, the two branches defining the stable maximum are equal.
example (f : K ⟶ L) :=
  horizontalStablePageGradedIsoAtIndex_naturality f 1 0

-- Identity and composite bicomplex maps.
example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :=
  horizontalStablePageGradedIsoAtIndex_naturality (𝟙 K) p q

example (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) :=
  horizontalStablePageGradedIsoAtIndex_naturality (f ≫ g) p q

private abbrev ZeroModuleCat := ModuleCat (ZMod 1)

example
    (K : HomologicalComplex₂ ZeroModuleCat (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :=
  horizontalStablePageGradedIsoAtIndex_naturality (𝟙 K) 0 0

#print axioms horizontalStablePageGradedIsoAtIndex_naturality

end HomologicalComplex₂.FirstQuadrantStablePageGradedNaturalityTests

end
