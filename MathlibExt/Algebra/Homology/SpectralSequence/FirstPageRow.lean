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

public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Integer rows of a cohomological first page

The first-page differential has bidegree `(1, 0)`. Restriction along the
integer-row embedding gives an integer cochain complex with the original
objects, differentials, and maps. Its homology comparison is the native
homological-complex restriction comparison, followed by the spectral
sequence successor isomorphism to the second page.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ComplexShape

/-- The inclusion of one integer row in the first-page bidegree shape. -/
def embeddingUpIntRow (q : ℤ) :
    (ComplexShape.up ℤ).Embedding (ComplexShape.up' (⟨1, 0⟩ : ℤ × ℤ)) :=
  ComplexShape.Embedding.mk' _ _ (fun p => (p, q))
    (fun _ _ h => congrArg (fun z : ℤ × ℤ => z.1) h)
    (by
      intro p p'
      change (p + 1 = p') ↔ (p, q) + (1, 0) = (p', q)
      constructor
      · intro h
        ext <;> dsimp <;> omega
      · intro h
        exact congrArg (fun z : ℤ × ℤ => z.1) h)

instance (q : ℤ) : (embeddingUpIntRow q).IsRelIff := by
  dsimp only [embeddingUpIntRow]
  infer_instance

end ComplexShape

namespace CategoryTheory.SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (S : SpectralSequence C (fun r => ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 1)

/-- The original first-page objects and differential on one integer coefficient row. -/
def firstPageRow (q : ℤ) : CochainComplex C ℤ :=
  (S.page 1).restriction (ComplexShape.embeddingUpIntRow q)

variable {S}
variable {T : SpectralSequence C (fun r => ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 1}

/-- The actual fixed-first-page map restricts to each coefficient row. -/
def firstPageRowMap (φ : S.page 1 ⟶ T.page 1) (q : ℤ) :
    S.firstPageRow q ⟶ T.firstPageRow q :=
  HomologicalComplex.restrictionMap φ (ComplexShape.embeddingUpIntRow q)

@[simp]
theorem firstPageRowMap_id (S : SpectralSequence C
    (fun r => ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 1) (q : ℤ) :
    firstPageRowMap (𝟙 (S.page 1)) q = 𝟙 (S.firstPageRow q) := rfl

@[simp]
theorem firstPageRowMap_comp
    {U : SpectralSequence C (fun r => ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 1}
    (φ : S.page 1 ⟶ T.page 1) (ψ : T.page 1 ⟶ U.page 1) (q : ℤ) :
    firstPageRowMap (φ ≫ ψ) q = firstPageRowMap φ q ≫ firstPageRowMap ψ q := rfl

variable (S)

/-- The row's homology agrees with the actual first-page homology at its bidegree. -/
def firstPageRowHomologyIso (p q : ℤ) :
    (S.firstPageRow q).homology p ≅ (S.page 1).homology (p, q) := by
  have hpRow : (ComplexShape.up ℤ).prev p = p - 1 :=
    (ComplexShape.up ℤ).prev_eq' (by change p - 1 + 1 = p; omega)
  have hnRow : (ComplexShape.up ℤ).next p = p + 1 :=
    (ComplexShape.up ℤ).next_eq' rfl
  have hpPage : (ComplexShape.up' (⟨1, 0⟩ : ℤ × ℤ)).prev (p, q) = (p - 1, q) :=
    (ComplexShape.up' (⟨1, 0⟩ : ℤ × ℤ)).prev_eq' (by
      change (p - 1, q) + (1, 0) = (p, q)
      ext <;> dsimp <;> omega)
  have hnPage : (ComplexShape.up' (⟨1, 0⟩ : ℤ × ℤ)).next (p, q) = (p + 1, q) :=
    (ComplexShape.up' (⟨1, 0⟩ : ℤ × ℤ)).next_eq' (by
      change (p, q) + (1, 0) = (p + 1, q)
      ext <;> dsimp; omega)
  exact (S.page 1).restrictionHomologyIso (ComplexShape.embeddingUpIntRow q)
    (p - 1) p (p + 1) hpRow hnRow rfl rfl rfl hpPage hnPage

/-- The integer row homology is the actual native second page. -/
def firstPageRowSecondPageIso (p q : ℤ) :
    (S.firstPageRow q).homology p ≅ (S.page 2).X (p, q) :=
  S.firstPageRowHomologyIso p q ≪≫ S.iso 1 2 (p, q) rfl (by omega)

end CategoryTheory.SpectralSequence

end
