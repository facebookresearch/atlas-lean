/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageColumn

/-! # Tests for the first-page vertical-column comparison -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantFirstPageColumnTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p : ℕ) :
    CochainComplex.mappingCone (horizontalFirstPageFiltrationMap K p) ⟶
      horizontalDirectColumnCochain K p :=
  horizontalFirstPageMappingConeToDirectColumn K p

example (p : ℕ) :
    QuasiIso (horizontalFirstPageMappingConeToDirectColumn K p) :=
  horizontalFirstPageMappingConeToDirectColumn_quasiIso K p

example (p : ℕ) :
    horizontalDirectColumnCochain K p ≅
      (K.X p).extend (ComplexShape.embeddingUpIntLE (-(p : ℤ))) :=
  horizontalDirectColumnUntwistIso K p

example (p q : ℕ) :
    horizontalFirstPageRelativeHomology K p q ≅
      (horizontalDirectColumnCochain K p).homology (-(p : ℤ) - q) :=
  horizontalFirstPageRelativeHomologyDirectColumnIso K p q

example (p q : ℕ) :
    (horizontalDirectColumnCochain K p).homology (-(p : ℤ) - q) ≅
      (K.X p).homology q :=
  horizontalDirectColumnHomologyIso K p q

example (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).X (p, q) ≅
      (K.X p).homology q :=
  horizontalFirstPageVerticalHomologyIso K p q

end HomologicalComplex₂.FirstQuadrantFirstPageColumnTests

end
