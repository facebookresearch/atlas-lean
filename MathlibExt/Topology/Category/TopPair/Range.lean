/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.Topology.Category.TopCat.Subspace
public import MathlibExt.Topology.Category.TopPair

/-!
# Range replacement for topological pairs

Every topological pair is naturally isomorphic to the pair whose subspace is
the range of its embedding.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace TopPair

/-- Replace the embedded subspace of a topological pair by its range. -/
noncomputable abbrev rangePair (P : TopPair.{u}) : TopPair.{u} :=
  TopPair.ofSubset (Set.range P.map)

/-- A map of pairs induces a map between their range replacements. -/
noncomputable def rangeMap {P Q : TopPair.{u}} (f : P ⟶ Q) :
    rangePair P ⟶ rangePair Q := by
  let ff : P.fst ⟶ Q.fst := TopPair.Hom.fst f
  exact TopPair.ofHom (X := rangePair P) (Y := rangePair Q) ff
    (AlgebraicTopology.subspaceMap (TopPair.Hom.fst f) (by
      rintro _ ⟨y, rfl⟩
      refine ⟨TopPair.Hom.snd f y, ?_⟩
      exact ConcreteCategory.congr_hom f.w y))
    (AlgebraicTopology.subspaceMap_comp_subspaceIncl _ _)

/-- Functorial range replacement of topological pairs. -/
noncomputable def rangeFunctor : TopPair.{u} ⥤ TopPair.{u} where
  obj := rangePair
  map := rangeMap
  map_id P := by
    ext <;> rfl
  map_comp f g := by
    ext <;> rfl

/-- A topological pair is canonically isomorphic to its range replacement. -/
noncomputable def rangeIso (P : TopPair.{u}) : P ≅ rangePair P :=
  CategoryTheory.MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo P.isEmbedding_map.toHomeomorph)
    (Iso.refl P.fst)
    (by ext x; rfl)

@[reassoc]
theorem rangeIso_hom_naturality {P Q : TopPair.{u}} (f : P ⟶ Q) :
    (rangeIso P).hom ≫ rangeMap f = f ≫ (rangeIso Q).hom := by
  ext
  · apply Subtype.ext
    change (TopPair.Hom.fst f) (P.map _) = Q.map (TopPair.Hom.snd f _)
    exact (ConcreteCategory.congr_hom f.w _).symm
  · rfl

/-- The identity functor on pairs is naturally isomorphic to range replacement. -/
noncomputable def rangeNatIso : Functor.id TopPair.{u} ≅ rangeFunctor :=
  NatIso.ofComponents rangeIso (fun f => (rangeIso_hom_naturality f).symm)

@[simp]
theorem ofSubset_fst {X : TopCat.{u}} (A : Set X) :
    (TopPair.ofSubset (X := X) A).fst = X := by
  rfl

/-- The ambient object of a subset pair, exposed as a canonical isomorphism
instead of relying on cross-module definitional reduction. -/
noncomputable def ofSubsetFstIso {X : TopCat.{u}} (A : Set X) :
    (TopPair.ofSubset (X := X) A).fst ≅ X :=
  eqToIso (ofSubset_fst A)

@[simp]
theorem ofSubsetFstIso_hom {X : TopCat.{u}} (A : Set X) :
    (ofSubsetFstIso A).hom = eqToHom (ofSubset_fst A) := by
  rfl

@[simp]
theorem ofSubsetFstIso_inv {X : TopCat.{u}} (A : Set X) :
    (ofSubsetFstIso A).inv = eqToHom (ofSubset_fst A).symm := by
  rfl

/-- The canonical empty pair is isomorphic to the empty-subset pair. -/
noncomputable def emptySubsetPairIso (X : TopCat.{u}) :
    TopPair.incl.obj X ≅ TopPair.ofSubset (∅ : Set X) := by
  letI : IsEmpty (TopPair.incl.obj X).snd := inferInstanceAs (IsEmpty PEmpty)
  letI : IsEmpty (TopPair.ofSubset (∅ : Set X)).snd :=
    ⟨fun x => x.property⟩
  exact CategoryTheory.MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo Homeomorph.empty) (Iso.refl X) (by
      ext x
      exact isEmptyElim x)

@[simp]
theorem emptySubsetPairIso_hom_fst (X : TopCat.{u}) :
    TopPair.Hom.fst (emptySubsetPairIso X).hom = 𝟙 X := by
  rfl

@[simp]
theorem emptySubsetPairIso_inv_fst (X : TopCat.{u}) :
    TopPair.Hom.fst (emptySubsetPairIso X).inv = 𝟙 X := by
  rfl

end TopPair
