/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.PartialTotalRow
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Homology coordinates of signed rows

Multiplication by ε(p)^q in chain degree q removes the constant
vertical differential sign ε(p). Combined with the extension homology
comparison, this identifies total-row homology with homology of the
original bicomplex row.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

section SignedRow

variable {C : Type u} [Category.{v} C] [Preadditive C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- The signed `p`th row is canonically isomorphic to the original row by
multiplication with `ε(p)^q` in chain degree `q`. -/
noncomputable def signedRowIso (p : ℕ) : B.signedRow p ≅ B.X p :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => ((ComplexShape.down ℕ).ε p) ^ q • Iso.refl _)
    (fun i j hij => by
      change j + 1 = i at hij
      subst i
      change
        (((ComplexShape.down ℕ).ε p) ^ (j + 1) • 𝟙 _) ≫
            (B.X p).d (j + 1) j =
          ((ComplexShape.down ℕ).ε p • (B.X p).d (j + 1) j) ≫
            (((ComplexShape.down ℕ).ε p) ^ j • 𝟙 _)
      simp only [Linear.units_smul_comp, Linear.comp_units_smul,
        Category.id_comp, Category.comp_id, smul_smul, pow_succ])

/-- Forward component of the signed-row isomorphism. -/
@[simp]
theorem signedRowIso_hom_f (p q : ℕ) :
    (B.signedRowIso p).hom.f q =
      ((ComplexShape.down ℕ).ε p) ^ q • 𝟙 ((B.X p).X q) := by
  rfl

/-- Inverse component of the signed-row isomorphism. -/
@[simp]
theorem signedRowIso_inv_f (p q : ℕ) :
    (B.signedRowIso p).inv.f q =
      (((ComplexShape.down ℕ).ε p) ^ q)⁻¹ • 𝟙 ((B.X p).X q) := by
  rfl

end SignedRow

section Homology

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- Homology of the signed row placed in total degree is canonically the
homology of the original bicomplex row. -/
noncomputable def totalRowHomologyIso (p q : ℕ) :
    (B.totalRow p).homology (p + q) ≅ (B.X p).homology q := by
  let e := ComplexShape.embeddingDown'Add 1 p
  change ((B.signedRow p).extend e).homology (p + q) ≅
    (B.X p).homology q
  exact (B.signedRow p).extendHomologyIso e (by
      change q + p = p + q
      omega) ≪≫
    HomologicalComplex.homologyMapIso (B.signedRowIso p) q

/-- Homology of the signed `p`th row in a chosen total degree `n=p+q`. -/
noncomputable def totalRowHomologyIsoAt
    (p q n : ℕ) (h : p + q = n) :
    (B.totalRow p).homology n ≅ (B.X p).homology q := by
  let e := ComplexShape.embeddingDown'Add 1 p
  change ((B.signedRow p).extend e).homology n ≅
    (B.X p).homology q
  exact (B.signedRow p).extendHomologyIso e (by
      change q + p = n
      omega) ≪≫
    HomologicalComplex.homologyMapIso (B.signedRowIso p) q

end Homology

end HomologicalComplex₂

end
