/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/FullSubcategory.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import MathlibExt.CategoryTheory.DGSource.DGFunctor

/-!
# Full differential graded subcategories

Restricting the objects of a differential graded category to those satisfying a predicate leaves
its Hom complexes, differential, identities, and composition intact. The inclusion is an enriched
functor whose maps on Hom complexes are identities. This construction is useful for selecting
representable, finite cell, or perfect objects while retaining their chain-level morphisms.

The ambient DG category need not have an ordinary `Category` instance, so Mathlib's
`ObjectProperty.FullSubcategory` is unavailable here.

## Main definitions

* `MathlibExt.DGSource.DGFullSubcategory`: objects satisfying a predicate in a DG category.
* `MathlibExt.DGSource.DGFullSubcategory.inclusion`: the enriched inclusion.

## References

* B. Keller, *Deriving DG categories*, Section 2.
-/

public section

open CategoryTheory

namespace MathlibExt.DGSource

universe v u

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

/-- The full DG subcategory on objects satisfying `P`. Its Hom complexes are those of `C`. -/
@[ext]
structure DGFullSubcategory (P : C → Prop) where
  /-- The underlying object. -/
  obj : C
  /-- The predicate holds on the object. -/
  property : P obj

namespace DGFullSubcategory

variable {P : C → Prop}

noncomputable section

/-- The full subcategory inherits its enrichment from the ambient DG category. -/
instance : DGCategory R (DGFullSubcategory P) where
  Hom X Y := X.obj ⟶[CochainComplex (ModuleCat.{v} R) ℤ] Y.obj
  id X := eId (CochainComplex (ModuleCat.{v} R) ℤ) X.obj
  comp X Y Z := eComp (CochainComplex (ModuleCat.{v} R) ℤ) X.obj Y.obj Z.obj
  id_comp X Y := e_id_comp (CochainComplex (ModuleCat.{v} R) ℤ) X.obj Y.obj
  comp_id X Y := e_comp_id (CochainComplex (ModuleCat.{v} R) ℤ) X.obj Y.obj
  assoc W X Y Z := e_assoc (CochainComplex (ModuleCat.{v} R) ℤ) W.obj X.obj Y.obj Z.obj

/-- The inclusion of a full DG subcategory into its ambient DG category. Every map on Hom
complexes is the identity. -/
def inclusion : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ)
    (DGFullSubcategory P) C where
  obj X := X.obj
  map _ _ := 𝟙 _

/-- The enriched inclusion sends an object to its underlying object. -/
@[simp]
theorem inclusion_obj (X : DGFullSubcategory P) :
    (inclusion (R := R) (P := P)).obj X = X.obj := by
  rfl

/-- The enriched inclusion acts as the identity on each Hom complex. -/
@[simp]
theorem inclusion_map (X Y : DGFullSubcategory P) :
    (inclusion (R := R) (P := P)).map X Y =
      eqToHom (by simp only [inclusion_obj]; rfl) := by
  simp only [inclusion]
  rfl

/-- The enriched inclusion retains a homogeneous morphism. The heterogeneous equality
accounts for the object map of the inclusion in the target type. -/
@[simp]
theorem inclusion_dgMap_heq {X Y : DGFullSubcategory P} {n : ℤ} (f : DGHom R n X Y) :
    (inclusion (R := R)).dgMap n f ≍ f := by
  rw [CategoryTheory.EnrichedFunctor.dgMap_apply, inclusion_map]
  rfl

/-- The Hom complex in the full DG subcategory is the ambient Hom complex. -/
@[simp]
theorem dgHomComplex_eq (X Y : DGFullSubcategory P) :
    dgHomComplex R X Y = dgHomComplex R X.obj Y.obj := rfl

/-- The differential of the full DG subcategory is the ambient differential. -/
@[simp]
theorem dgDifferential_eq {X Y : DGFullSubcategory P} (n : ℤ) (f : DGHom R n X Y) :
    dgDifferential R n f = dgDifferential R n (X := X.obj) (Y := Y.obj) f := rfl

/-- The identity of the full DG subcategory is the ambient identity. -/
@[simp]
theorem dgId_eq (X : DGFullSubcategory P) : dgId R X = dgId R X.obj := by
  simp only [dgId_def]
  rfl

/-- Composition in the full DG subcategory is ambient composition. -/
@[simp]
theorem dgComp_eq {X Y Z : DGFullSubcategory P} {p q n : ℤ}
    (f : DGHom R p X Y) (g : DGHom R q Y Z) (h : p + q = n) :
    dgComp R f g h = dgComp R (X := X.obj) (Y := Y.obj) (Z := Z.obj) f g h := by
  rw [← dgCompMap_tmul, ← dgCompMap_tmul]
  congr 1
  simp only [dgCompMap_def]
  rfl

end

end DGFullSubcategory

end MathlibExt.DGSource
