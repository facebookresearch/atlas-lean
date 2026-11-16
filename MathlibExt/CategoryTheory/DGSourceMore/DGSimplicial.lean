/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/Simplicial.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only module/namespace paths are adapted for Atlas.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import MathlibExt.CategoryTheory.DGSource.DGOpposite
public import MathlibExt.CategoryTheory.DGSourceMore.CochainToSSet

/-!
# The simplicial enrichment of a differential graded category

The mapping simplicial sets of `DGSimplicialCategory R C` are the underlying simplicial
sets of `Γ(τ≥0 Hom_C(X,Y))`. They are Kan complexes. Composition comes from lax monoidal
good truncation and the Alexander–Whitney Dold–Kan functor.

Mathlib's enriched composition takes the earlier arrow first. Lurie's convention takes
the later arrow first. To implement Lurie's order, we first take the DG opposite, transport
its enrichment, and take the simplicial opposite. Thus composition swaps the simplicial
factors before the tensorator, and swaps the DG factors with the Koszul braiding afterwards.
The two opposites restore the original direction of the arrows. This is essential because
the Alexander–Whitney lax monoidal functor is not symmetric monoidal.

The construction uses Mathlib's `TransportEnrichment` and `EnrichedCategory.opposite`,
which supply the associativity and unit laws, and the existing good-truncation, Dold–Kan
and simplicial-group Kan constructions.

## References

* J. Lurie, *Higher Algebra*, Construction 1.3.1.13 and Remark 1.3.1.14.
-/

public section

open CategoryTheory MonoidalCategory Opposite

open scoped Simplicial

namespace MathlibExt.DGSource

universe v u

noncomputable section

variable (R : Type v) [CommRing R] (C : Type u) [DGCategory R C]

/-- The simplicial category associated to a DG category, with Lurie's order of composition.
The two opposites change composition order while retaining the original Hom complexes. -/
@[expose]
def DGSimplicialCategory := (TransportEnrichment (cochainToSSet R) Cᵒᵖ)ᵒᵖ

variable {C}

/-- An object of a DG category as an object of its associated simplicial category. -/
def DGSimplicialCategory.of (X : C) : DGSimplicialCategory R C := op (op X)

/-- Recover the DG object from an object of the associated simplicial category. -/
-- The inherited enrichment fields need the definitional identification with X.unop.unop.
@[expose]
def DGSimplicialCategory.underlying (X : DGSimplicialCategory R C) : C := X.unop.unop

-- The DG and simplicial opposites each reverse Hom, so the inherited Hom is definitionally
-- the image of the original DG Hom complex.
-- Spell out this field to make hom_eq hold by rfl, retaining the inherited unit and composition.
instance : EnrichedCategory SSet.{v} (DGSimplicialCategory R C) :=
  { (inferInstance : EnrichedCategory SSet.{v}
      (TransportEnrichment (cochainToSSet R) Cᵒᵖ)ᵒᵖ) with
    Hom X Y := (cochainToSSet R).obj
      (dgHomComplex R (X.underlying R) (Y.underlying R)) }

omit [DGCategory R C] in
@[simp]
theorem DGSimplicialCategory.underlying_of (X : C) :
    (of R X).underlying R = X :=
  (rfl)

omit [DGCategory R C] in
@[simp]
theorem DGSimplicialCategory.of_underlying (X : DGSimplicialCategory R C) :
    of R (X.underlying R) = X :=
  (rfl)

/-- The mapping simplicial set is Dold–Kan applied to the good truncation of the DG Hom. -/
theorem DGSimplicialCategory.hom_eq (X Y : DGSimplicialCategory R C) :
    (X ⟶[SSet.{v}] Y) = (cochainToSSet R).obj
      (dgHomComplex R (X.underlying R) (Y.underlying R)) :=
  (rfl)

/-- The associated simplicial category is locally Kan. -/
instance (X Y : DGSimplicialCategory R C) : SSet.KanComplex (X ⟶[SSet.{v}] Y) := by
  rw [DGSimplicialCategory.hom_eq]
  infer_instance

/-- The enriched unit is the image of the DG unit under the lax monoidal functor. -/
theorem DGSimplicialCategory.eId_eq (X : DGSimplicialCategory R C) :
    eId SSet.{v} X = Functor.LaxMonoidal.ε (cochainToSSet R) ≫
      (cochainToSSet R).map
        (eId (CochainComplex (ModuleCat.{v} R) ℤ) (X.underlying R)) :=
  (rfl)

/-- The vertex of the endomorphism space selected by the DG identity. -/
def DGSimplicialCategory.idVertex (X : DGSimplicialCategory R C) :
    (X ⟶[SSet.{v}] X).obj (op ⦋0⦌) :=
  (eId SSet.{v} X).app (op ⦋0⦌) PUnit.unit

/-- The identity vertex is obtained by applying the lax functor to the DG unit. -/
theorem DGSimplicialCategory.idVertex_def (X : DGSimplicialCategory R C) :
    X.idVertex R = ((Functor.LaxMonoidal.ε (cochainToSSet R) ≫
      (cochainToSSet R).map
        (eId (CochainComplex (ModuleCat.{v} R) ℤ) (X.underlying R))).app (op ⦋0⦌)) PUnit.unit := by
  rw [DGSimplicialCategory.idVertex, DGSimplicialCategory.eId_eq]

/-- The enriched unit is constant at the vertex selected by the DG identity, in every
simplicial degree. -/
theorem DGSimplicialCategory.eId_eq_const (X : DGSimplicialCategory R C) :
    eId SSet.{v} X = SSet.const (X.idVertex R) := by
  -- The tensor unit is the terminal simplicial set, with PUnit simplices in every degree.
  have h : SSet.const (X := 𝟙_ SSet.{v})
      (PUnit.unit : (𝟙_ SSet.{v}).obj (op ⦋0⦌)) = 𝟙 _ := by
    ext n x
    rfl
  rw [← Category.id_comp (eId SSet.{v} X), ← h, SSet.const_comp]
  simp [DGSimplicialCategory.idVertex]

/-- Composition in the earlier-arrow-first convention: swap the simplicial factors,
apply the tensorator, then use the Koszul-swapped DG composition. -/
theorem DGSimplicialCategory.eComp_eq (X Y Z : DGSimplicialCategory R C) :
    eComp SSet.{v} X Y Z =
      (β_ (X ⟶[SSet.{v}] Y) (Y ⟶[SSet.{v}] Z)).hom ≫
        Functor.LaxMonoidal.μ (cochainToSSet R)
          (dgHomComplex R (Y.underlying R) (Z.underlying R))
          (dgHomComplex R (X.underlying R) (Y.underlying R)) ≫
        (cochainToSSet R).map
          ((β_ (dgHomComplex R (Y.underlying R) (Z.underlying R))
            (dgHomComplex R (X.underlying R) (Y.underlying R))).hom ≫
              eComp (CochainComplex (ModuleCat.{v} R) ℤ)
                (X.underlying R) (Y.underlying R) (Z.underlying R)) :=
  (rfl)

end

end MathlibExt.DGSource
