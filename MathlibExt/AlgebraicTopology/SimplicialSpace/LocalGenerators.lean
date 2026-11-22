/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyGeneratingFamilies
public import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalizingMaps

/-!
# Literal auxiliary generators for local objects

The actual small indexed family adjoins to the raw Reedy horn family every
original Segal/full-E map inner-pushout-product with every scalar boundary,
including degree zero. The original designated maps, actual chosen pushouts
and both injection equations are retained. No monicity, weakness, terminal
recognition, small-object argument or model conclusion is asserted here.

Source: Rezk, *A model for the homotopy theory of homotopy theory* (2001),
Sections 4, 6 and 9.1. The completeness object is the full walking-isomorphism
nerve and the original selected vertex; no finite surrogate is used.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace SimplicialSpace.LocalGenerators

/-- Every original Segal/full-E index paired with every scalar boundary dimension. -/
abbrev BoundaryIndex := SSet.Rezk.LocalizingIndex × ℕ

/-- The literal raw Reedy horns and the added localizing boundary pushout-products. -/
abbrev Index := ReedyGeneratingFamilies.HornIndex ⊕ BoundaryIndex

/-- The original raw localizing arrow, transported by the designated native functor. -/
abbrev localizingArrow (i : SSet.Rezk.LocalizingIndex) : Arrow SimplicialSpace.{u} :=
  ofSimplicialObject.mapArrow.obj (SSet.Rezk.localizingMap.{u} i)

/-- The underlying original natural transformation is unchanged by designation. -/
lemma localizingArrow_hom (i : SSet.Rezk.LocalizingIndex) :
    (localizingArrow.{u} i).hom.hom = (SSet.Rezk.localizingMap.{u} i).hom := rfl

/-- The actual chosen pushout retains the original localizing map and scalar boundary. -/
def boundaryPushout (i : SSet.Rezk.LocalizingIndex) (n : ℕ) :
    innerTensorBifunctor.{u}.PushoutObjObj (localizingArrow.{u} i).hom
      (SSet.boundary.{u} n).ι :=
  Functor.PushoutObjObj.ofHasPushout innerTensorBifunctor.{u}
    (localizingArrow.{u} i).hom (SSet.boundary.{u} n).ι

/-- The added original arrow, with its actual chosen pushout as source. -/
def boundaryFamily (b : BoundaryIndex) : Arrow SimplicialSpace.{u} :=
  Arrow.mk (boundaryPushout.{u} b.1 b.2).ι

/-- The actual indexed auxiliary family, with no localization packet assumed. -/
def family : Index → Arrow SimplicialSpace.{u}
  | .inl h => ReedyGeneratingFamilies.hornFamily.{u} h
  | .inr b => boundaryFamily.{u} b

/-- The literal auxiliary family as the native small class of its indexed arrows. -/
def J : MorphismProperty SimplicialSpace.{u} :=
  MorphismProperty.ofHoms (fun i : Index => (family.{u} i).hom)

/-- Smallness is obtained from the original sum/product index, at the working size. -/
lemma isSmall_J : MorphismProperty.IsSmall.{u} J.{u} :=
  MorphismProperty.isSmall_ofHoms.{u} (fun i : Index => (family.{u} i).hom)

/-- The horn summand is exactly the existing raw family. -/
@[simp] lemma family_horn (h : ReedyGeneratingFamilies.HornIndex) :
    family.{u} (.inl h) = ReedyGeneratingFamilies.hornFamily.{u} h := rfl

/-- The localizing summand is exactly its original chosen scalar boundary arrow. -/
@[simp] lemma family_boundary (i : SSet.Rezk.LocalizingIndex) (n : ℕ) :
    family.{u} (.inr (i, n)) = Arrow.mk (boundaryPushout.{u} i n).ι := rfl

/-- Every original index supplies a member, without changing either endpoint. -/
lemma family_mem (i : Index) : J.{u} (family.{u} i).hom :=
  MorphismProperty.ofHoms.mk (f := fun i : Index => (family.{u} i).hom) i

/-- Membership is an equality with one of the actual original indexed arrows. -/
lemma mem_iff {A B : SimplicialSpace.{u}} (f : A ⟶ B) :
    J.{u} f ↔ ∃ i : Index, Arrow.mk f = family.{u} i := by
  simpa only [J, Arrow.mk_eq] using
    (MorphismProperty.ofHoms_iff (fun i : Index => (family.{u} i).hom) f)

/-- Every original raw Reedy horn is retained in the auxiliary family. -/
lemma horn_mem (h : ReedyGeneratingFamilies.HornIndex) :
    J.{u} (ReedyGeneratingFamilies.hornFamily.{u} h).hom :=
  family_mem.{u} (.inl h)

/-- Every literal localizing map and every boundary dimension is retained. -/
lemma boundary_mem (i : SSet.Rezk.LocalizingIndex) (n : ℕ) :
    J.{u} (boundaryPushout.{u} i n).ι :=
  family_mem.{u} (.inr (i, n))

/-- Both original injections recover the original tensor-factor maps. -/
lemma boundary_legs (i : SSet.Rezk.LocalizingIndex) (n : ℕ) :
    (boundaryPushout.{u} i n).inl ≫ (boundaryPushout.{u} i n).ι =
        (innerTensorBifunctor.{u}.obj (localizingArrow.{u} i).right).map
          (SSet.boundary.{u} n).ι ∧
      (boundaryPushout.{u} i n).inr ≫ (boundaryPushout.{u} i n).ι =
        (innerTensorBifunctor.{u}.map (localizingArrow.{u} i).hom).app
          (Δ[n] : SSet.{u}) :=
  ⟨(boundaryPushout.{u} i n).inl_ι, (boundaryPushout.{u} i n).inr_ι⟩

/-- The codomain keeps the raw outer coordinate and the actual inner scalar coordinate. -/
lemma target_bidegree (i : SSet.Rezk.LocalizingIndex) (n : ℕ)
    (m k : SimplexCategoryᵒᵖ) :
    (((boundaryFamily.{u} (i, n)).right.diagram.obj m).obj k) =
      (((SSet.Rezk.localizingMap.{u} i).right.obj m).obj k ×
        (Δ[n] : SSet.{u}).obj k) := rfl

end SimplicialSpace.LocalGenerators
