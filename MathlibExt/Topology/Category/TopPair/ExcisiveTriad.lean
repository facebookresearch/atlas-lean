/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.RelativeCupCover
public import MathlibExt.Topology.Category.TopPair.Range

/-!
# Excisive triads of topological pairs
-/

@[expose] public section

/-!
Neutral pair geometry for excisive triads.

This layer records only `TopPair` objects and subset-pair maps; it has no
simplicial, chain, cochain, or cohomology dependency.
-/

open CategoryTheory

universe u

namespace TopPair

/-- Generic subset-pair map induced by an ambient `TopCat` map. -/
noncomputable def ofSubsetMap {X Y : TopCat.{u}} {A : Set X} {B : Set Y}
    (f : X ⟶ Y) (h : Set.MapsTo f A B) :
    TopPair.ofSubset A ⟶ TopPair.ofSubset B :=
  TopPair.ofHom f (AlgebraicTopology.subspaceMap f h)
    (AlgebraicTopology.subspaceMap_comp_subspaceIncl f h)

/-- An identity-induced subset-pair map along an equality of subsets is the
corresponding equality morphism. -/
theorem ofSubsetMap_id_eqToHom {X : TopCat.{u}} {U V : Set X}
    (hUV : U = V) (hMaps : Set.MapsTo (𝟙 X) U V) :
    ofSubsetMap (𝟙 X) hMaps =
      eqToHom (congrArg (fun C : Set X => TopPair.ofSubset C) hUV) := by
  subst V
  ext <;> rfl

noncomputable def ofSubsetUnionAssociator {X : TopCat.{u}} (A B C : Set X) :
    TopPair.ofSubset ((A ∪ B) ∪ C) ≅ TopPair.ofSubset (A ∪ (B ∪ C)) where
  hom := ofSubsetMap (𝟙 X) (by
    intro x hx
    simpa only [TopCat.id_app, Set.union_assoc] using hx)
  inv := ofSubsetMap (𝟙 X) (by
    intro x hx
    simpa only [TopCat.id_app, Set.union_assoc] using hx)
  hom_inv_id := by ext <;> rfl
  inv_hom_id := by ext <;> rfl

noncomputable def ofSubsetUnionLeftUnitor {X : TopCat.{u}} (A : Set X) :
    TopPair.ofSubset ((∅ : Set X) ∪ A) ≅ TopPair.ofSubset A where
  hom := ofSubsetMap (𝟙 X) (by
    intro x hx
    simpa only [TopCat.id_app, Set.empty_union] using hx)
  inv := ofSubsetMap (𝟙 X) (by
    intro x hx
    simpa only [TopCat.id_app, Set.empty_union] using hx)
  hom_inv_id := by ext <;> rfl
  inv_hom_id := by ext <;> rfl

noncomputable def ofSubsetUnionRightUnitor {X : TopCat.{u}} (A : Set X) :
    TopPair.ofSubset (A ∪ (∅ : Set X)) ≅ TopPair.ofSubset A where
  hom := ofSubsetMap (𝟙 X) (by
    intro x hx
    simpa only [TopCat.id_app, Set.union_empty] using hx)
  inv := ofSubsetMap (𝟙 X) (by
    intro x hx
    simpa only [TopCat.id_app, Set.union_empty] using hx)
  hom_inv_id := by ext <;> rfl
  inv_hom_id := by ext <;> rfl

noncomputable def ofSubsetUnionComm {X : TopCat.{u}} (A B : Set X) :
    TopPair.ofSubset (A ∪ B) ≅ TopPair.ofSubset (B ∪ A) where
  hom := ofSubsetMap (𝟙 X) (by
    intro x hx
    simpa only [TopCat.id_app, Set.union_comm] using hx)
  inv := ofSubsetMap (𝟙 X) (by
    intro x hx
    simpa only [TopCat.id_app, Set.union_comm] using hx)
  hom_inv_id := by ext <;> rfl
  inv_hom_id := by ext <;> rfl

end TopPair

namespace AlgebraicTopology.ExcisiveTriad

/-- Left subset-pair functor. -/
noncomputable def leftPairFunctor : ExcisiveTriad.{u} ⥤ TopPair.{u} where
  obj T := TopPair.ofSubset T.left
  map f := TopPair.ofSubsetMap f.f f.left_maps
  map_id _ := by ext <;> rfl
  map_comp f g := by ext <;> rfl

/-- Right subset-pair functor. -/
noncomputable def rightPairFunctor : ExcisiveTriad.{u} ⥤ TopPair.{u} where
  obj T := TopPair.ofSubset T.right
  map f := TopPair.ofSubsetMap f.f f.right_maps
  map_id _ := by ext <;> rfl
  map_comp f g := by ext <;> rfl

/-- Union subset-pair functor. -/
noncomputable def unionPairFunctor : ExcisiveTriad.{u} ⥤ TopPair.{u} where
  obj T := TopPair.ofSubset (T.left ∪ T.right)
  map f := TopPair.ofSubsetMap f.f (f.left_maps.union_union f.right_maps)
  map_id _ := by ext <;> rfl
  map_comp f g := by ext <;> rfl

@[simp]
theorem leftPairFunctor_obj (T : ExcisiveTriad.{u}) :
    leftPairFunctor.obj T = TopPair.ofSubset T.left :=
  rfl

@[simp]
theorem leftPairFunctor_map {S T : ExcisiveTriad.{u}} (f : S ⟶ T) :
    leftPairFunctor.map f = TopPair.ofSubsetMap f.f f.left_maps :=
  rfl

@[simp]
theorem rightPairFunctor_obj (T : ExcisiveTriad.{u}) :
    rightPairFunctor.obj T = TopPair.ofSubset T.right :=
  rfl

@[simp]
theorem rightPairFunctor_map {S T : ExcisiveTriad.{u}} (f : S ⟶ T) :
    rightPairFunctor.map f = TopPair.ofSubsetMap f.f f.right_maps :=
  rfl

@[simp]
theorem unionPairFunctor_obj (T : ExcisiveTriad.{u}) :
    unionPairFunctor.obj T = TopPair.ofSubset (T.left ∪ T.right) :=
  rfl

@[simp]
theorem unionPairFunctor_map {S T : ExcisiveTriad.{u}} (f : S ⟶ T) :
    unionPairFunctor.map f =
      TopPair.ofSubsetMap f.f (f.left_maps.union_union f.right_maps) :=
  rfl

/-- Empty excisive triad functor. -/
noncomputable def emptyFunctor : TopCat.{u} ⥤ ExcisiveTriad.{u} where
  obj X := ⟨X, ∅, ∅, AlgebraicTopology.isRelativeCupExcisive_empty_left ∅⟩
  map f := ⟨f, fun x hx => (Set.notMem_empty x hx).elim,
    fun x hx => (Set.notMem_empty x hx).elim⟩
  map_id _ := Hom.ext rfl
  map_comp _ _ := Hom.ext rfl

@[simp]
theorem emptyFunctor_obj_X (X : TopCat.{u}) :
    (emptyFunctor.obj X).X = X :=
  rfl

@[simp]
theorem emptyFunctor_obj_left (X : TopCat.{u}) :
    (emptyFunctor.obj X).left = ∅ :=
  rfl

@[simp]
theorem emptyFunctor_obj_right (X : TopCat.{u}) :
    (emptyFunctor.obj X).right = ∅ :=
  rfl

@[simp]
theorem emptyFunctor_map_f {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (emptyFunctor.map f).f = f :=
  rfl

/-- Left empty comparison. -/
noncomputable def emptyLeftPairNatIso :
    emptyFunctor ⋙ leftPairFunctor ≅ TopPair.incl :=
  NatIso.ofComponents (fun X => (TopPair.emptySubsetPairIso X).symm)
    (fun f => by ext <;> rfl)

/-- Right empty comparison. -/
noncomputable def emptyRightPairNatIso :
    emptyFunctor ⋙ rightPairFunctor ≅ TopPair.incl :=
  NatIso.ofComponents (fun X => (TopPair.emptySubsetPairIso X).symm)
    (fun f => by ext <;> rfl)

/-- Union empty comparison. -/
noncomputable def emptyUnionPairNatIso :
    emptyFunctor ⋙ unionPairFunctor ≅ TopPair.incl :=
  NatIso.ofComponents
    (fun X => (TopPair.ofSubsetUnionLeftUnitor (X := X) (∅ : Set X)).trans
      (TopPair.emptySubsetPairIso X).symm)
    (fun f => by ext <;> rfl)

end AlgebraicTopology.ExcisiveTriad
