/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# The unconditional homology diagonal of an actual chain comonoid

Applying the native graded homology functor to the actual chain
comultiplication gives a canonical map into homology of the tensor square.
This construction needs no Künneth theorem, field, or scalar-world equality.
The monoidal structure and comonoid are structures on the input chain
category and object; no homology coalgebra or tensor-coherence data is an
input. The subsequent graded coalgebra transport is a separate construction.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ComonObj

namespace HomologicalComplex.HomologyCoalgebra

variable {A : Type u} [Category.{v} A] [Preadditive A] [CategoryWithHomology A]
  [MonoidalCategory (ChainComplex A ℕ)]


/-- Every actual chain comonoid has a canonical homology diagonal into
homology of its actual tensor square. -/
def canonicalToTensorHomology (C : ChainComplex A ℕ) [ComonObj C] :
    (gradedHomologyFunctor A (ComplexShape.down ℕ)).obj C ⟶ (gradedHomologyFunctor A (ComplexShape.down ℕ)).obj
      (C ⊗ C) := (gradedHomologyFunctor A (ComplexShape.down ℕ)).map Δ[C]

@[simp]
theorem canonicalToTensorHomology_apply (C : ChainComplex A ℕ) [ComonObj C] (n : ℕ) :
    canonicalToTensorHomology C n = homologyMap Δ[C] n := rfl

/-- Naturality follows from the actual input comonoid-morphism equation
and functoriality of native homology. -/
@[reassoc]
theorem canonicalToTensorHomology_naturality (C : ChainComplex A ℕ) [ComonObj C]
    {D : ChainComplex A ℕ} [ComonObj D] (f : C ⟶ D) [IsComonHom f] :
    (gradedHomologyFunctor A (ComplexShape.down ℕ)).map f ≫ canonicalToTensorHomology D =
      canonicalToTensorHomology C ≫ (gradedHomologyFunctor A (ComplexShape.down ℕ)).map (f ⊗ₘ f) := by
  simp only [canonicalToTensorHomology, ← Functor.map_comp, IsComonHom.hom_comul]

/-- The actual left counit gives a canonical retraction of the homology
diagonal, without any Künneth hypothesis. -/
def diagonalRetraction (C : ChainComplex A ℕ) [ComonObj C] : (gradedHomologyFunctor A (ComplexShape.down ℕ)).obj
  (C ⊗ C) ⟶ (gradedHomologyFunctor A (ComplexShape.down ℕ)).obj C :=
  (gradedHomologyFunctor A (ComplexShape.down ℕ)).map (ε[C] ▷ C ≫ (λ_ C).hom)

@[reassoc (attr := simp)]
theorem canonicalToTensorHomology_retraction (C : ChainComplex A ℕ) [ComonObj C] :
    canonicalToTensorHomology C ≫ diagonalRetraction C = 𝟙 ((gradedHomologyFunctor A (ComplexShape.down ℕ)).obj C) := by
  simp only [canonicalToTensorHomology, diagonalRetraction, ← Functor.map_comp,
    ← Category.assoc, ComonObj.counit_comul, Iso.inv_hom_id]
  exact (gradedHomologyFunctor A (ComplexShape.down ℕ)).map_id C

end HomologicalComplex.HomologyCoalgebra
