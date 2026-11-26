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
# The homology diagonal into homology of a chain tensor square

Let A be a preadditive category with chosen homology, and let the category
of nonnegative chain complexes in A carry a monoidal structure.
For a chain comonoid C with comultiplication Δ_C, graded homology gives
δ_C=H(Δ_C):H(C)→H(C⊗C).

This diagonal is natural for chain comonoid morphisms. Its retraction is
the homology map of the left counit composite
C⊗C → 𝟙⊗C → C, so the retraction followed after δ_C is id.
The target is homology of the chain tensor square; no tensor comparison
between H(C⊗C) and H(C)⊗H(C) is required.
The object and morphism worlds of A are independent.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ComonObj

namespace HomologicalComplex.HomologyCoalgebra

variable {A : Type u} [Category.{v} A] [Preadditive A] [CategoryWithHomology A]
  [MonoidalCategory (ChainComplex A ℕ)]


/-- For a preadditive category A with chosen homology and a
monoidal structure on ChainComplex(A,ℕ), a comonoid C has
δ_C:H(C)→H(C⊗C), defined by applying graded homology to Δ_C.
No monoidal structure on graded homology is needed to define this map. -/
def canonicalToTensorHomology (C : ChainComplex A ℕ) [ComonObj C] :
    (gradedHomologyFunctor A (ComplexShape.down ℕ)).obj C ⟶ (gradedHomologyFunctor A (ComplexShape.down ℕ)).obj
      (C ⊗ C) := (gradedHomologyFunctor A (ComplexShape.down ℕ)).map Δ[C]

@[simp]
theorem canonicalToTensorHomology_apply (C : ChainComplex A ℕ) [ComonObj C] (n : ℕ) :
    canonicalToTensorHomology C n = homologyMap Δ[C] n := rfl

/-- For chain comonoids C,D in a monoidal category of
nonnegative complexes over a preadditive category with homology,
a comonoid morphism f:C→D satisfies
δ_D ∘ H(f)=H(f⊗f) ∘ δ_C.
Both diagonals have target homology of the corresponding chain
tensor square. -/
@[reassoc]
theorem canonicalToTensorHomology_naturality (C : ChainComplex A ℕ) [ComonObj C]
    {D : ChainComplex A ℕ} [ComonObj D] (f : C ⟶ D) [IsComonHom f] :
    (gradedHomologyFunctor A (ComplexShape.down ℕ)).map f ≫ canonicalToTensorHomology D =
      canonicalToTensorHomology C ≫ (gradedHomologyFunctor A (ComplexShape.down ℕ)).map (f ⊗ₘ f) := by
  simp only [canonicalToTensorHomology, ← Functor.map_comp, IsComonHom.hom_comul]

/-- For a chain comonoid C over a preadditive category with
homology, the map H(C⊗C)→H(C) is H of the composite
C⊗C → 𝟙⊗C → C, given by ε_C⊗id and the left unitor.
The left counit equation makes it a retraction of H(Δ_C). -/
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
