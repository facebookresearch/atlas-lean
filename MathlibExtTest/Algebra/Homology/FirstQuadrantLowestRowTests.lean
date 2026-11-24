/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.Algebra.Homology.FirstQuadrantLowestRow

open CategoryTheory CategoryTheory.Limits

universe u v

#check HomologicalComplex₂.horizontalLowestRowZeroColumnPageIso
#print axioms HomologicalComplex₂.horizontalLowestRowZeroColumnPageIso
#check HomologicalComplex₂.isZero_horizontalSecondPage_zeroColumn_of_total_acyclic_of_lower_rows
#print axioms HomologicalComplex₂.isZero_horizontalSecondPage_zeroColumn_of_total_acyclic_of_lower_rows

namespace FirstQuadrantLowestRowTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))

example (q : ℕ) (h : (K.total (ComplexShape.down ℕ)).Acyclic)
    (hBelow : ∀ b : ℕ, b < q → ∀ a : ℕ,
      IsZero (((HomologicalComplex₂.horizontalFirstQuadrantSpectralSequence K).page 2).X (a, b))) :
    IsZero (((HomologicalComplex₂.horizontalFirstQuadrantSpectralSequence K).page 2).X (0, q)) :=
  HomologicalComplex₂.isZero_horizontalSecondPage_zeroColumn_of_total_acyclic_of_lower_rows
    K q h hBelow

example (h : (K.total (ComplexShape.down ℕ)).Acyclic) :
    IsZero (((HomologicalComplex₂.horizontalFirstQuadrantSpectralSequence K).page 2).X (0, 0)) :=
  HomologicalComplex₂.isZero_horizontalSecondPage_zeroColumn_of_total_acyclic_of_lower_rows
    K 0 h (fun b hb => False.elim (Nat.not_lt_zero b hb))

end FirstQuadrantLowestRowTests
