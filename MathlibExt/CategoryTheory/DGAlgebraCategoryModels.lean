/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.Homology.DGAlgebras

/-!
# Actual DG algebras and one-object DG categories

A native cochain monoid gives a genuine one-object DG category. Conversely
the actual Hom complex of an object is a cochain monoid, in the native
enriched composition order. Its identity and multiplication are the
source eId and eComp, not freely chosen DG algebra maps.

The generic cochain endomorphism composition convention is given by
DGSource.dgComp_linearHomComplex, including the source Koszul sign.
References: Keller, Deriving DG categories, §1; Toën,
arXiv:math/0408337v7, §2. All proofs below use the native enriched/monoid
axioms and source cochain enrichment.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DGAlgebraCategoryModels

open _root_.CategoryTheory MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.Algebra.Homology

universe u v

variable {k : Type u} [CommRing k]

/-- The actual one-object cochain enrichment of a DG algebra. Composition is the product in the
native order, `a ≫ b = a * b`. Consequently a DG presheaf on this category (for instance a
`DGQuasiFunctorModels.RightModule`) satisfies `M (a * b) = M a ∘ M b`: it is a *left* `A`-module.
Conventional right `A`-modules are presheaves on the category of the opposite DG algebra (with the
Koszul sign on homogeneous elements). -/
@[instance_reducible]
def algebraEnrichment (A : DGAlgebra k) : DGCategory k (PUnit.{u + 1}) where
  Hom _ _ := A.X
  id _ := MonObj.one (X := A.X)
  comp _ _ _ := MonObj.mul (X := A.X)
  id_comp _ _ := by
    simp only [MonObj.one_mul, Iso.inv_hom_id]
  comp_id _ _ := by
    simp only [MonObj.mul_one, Iso.inv_hom_id]
  assoc _ _ _ _ := by
    rw [MonObj.mul_assoc]
    simp only [Iso.inv_hom_id_assoc]

/-- Bundle the actual one-object DG category, retaining its full algebra Hom complex. -/
def algebraCategory (A : DGAlgebra k) : DGCat k :=
  letI := algebraEnrichment A
  DGCat.of k (PUnit.{u + 1})

/-- The actual enriched endomorphism algebra at an object. -/
def endomorphismAlgebra {C : Type v} [DGCategory k C] (x : C) : DGAlgebra k := by
  letI : MonObj (dgHomComplex k x x) :=
    { one := eId (Cochains k) x
      mul := eComp (Cochains k) x x x
      one_mul := by
        apply (cancel_epi (λ_ (dgHomComplex k x x)).inv).mp
        simpa only [Category.assoc, Iso.inv_hom_id] using!
          (EnrichedCategory.id_comp (V := Cochains k) x x)
      mul_one := by
        apply (cancel_epi (ρ_ (dgHomComplex k x x)).inv).mp
        simpa only [Category.assoc, Iso.inv_hom_id] using!
          (EnrichedCategory.comp_id (V := Cochains k) x x)
      mul_assoc := by
        apply (cancel_epi (α_ (dgHomComplex k x x)
          (dgHomComplex k x x) (dgHomComplex k x x)).inv).mp
        simpa only [Category.assoc, Iso.inv_hom_id_assoc] using!
          (EnrichedCategory.assoc (V := Cochains k) x x x x) }
  exact Mon.mk (dgHomComplex k x x)

/-- Multiplication of actual homogeneous elements through the native
tensor summand, with the specified total degree. -/
def multiplyHomogeneous (A : DGAlgebra k) {p q r : ℤ}
    (a : A.X.X p) (b : A.X.X q) (h : p + q = r) : A.X.X r :=
  ((HomologicalComplex.ιTensorObj A.X A.X p q r h) ≫
    (MonObj.mul (X := A.X)).f r).hom (TensorProduct.tmul k a b)

/-- Endomorphism multiplication is the source enriched DG composition,
including its documented cochain factor-order sign. -/
theorem endomorphism_multiply {C : Type v} [DGCategory k C] (x : C)
    {p q r : ℤ} (a : DGHom k p x x) (b : DGHom k q x x) (h : p + q = r) :
    multiplyHomogeneous (endomorphismAlgebra x) a b h = dgComp k a b h := by
  rw [← dgCompMap_tmul k h a b, dgCompMap_def]
  rfl

end MathlibExt.CategoryTheory.DGAlgebraCategoryModels
