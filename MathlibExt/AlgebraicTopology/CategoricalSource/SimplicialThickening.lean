/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Modifications copyright (c) 2026 Meta Platforms, Inc. and affiliates.
-/
module

/-
Completed proof port; original Apache 2.0 author/license header retained.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/SimplicialNerve/SimplicialThickening.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only import paths and the TauCeti helper namespace are adapted.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import Mathlib.AlgebraicTopology.SimplicialNerve
public import MathlibExt.AlgebraicTopology.CategoricalSource.EnrichedOrdinary
/-!
# Paths and functors out of the simplicial thickening

For a linear order `J`, Mathlib's simplicial thickening `SimplicialThickening J` is the simplicial
category `C[Δ^J]` whose mapping simplicial set from `i` to `j` is the nerve of the poset `Path i j`
of subsets of `[i, j]` containing both endpoints. This file collects basic facts about these
posets of paths and about chains of paths, the simplices of the mapping simplicial sets.

It also relates simplicial functors out of `C[Δ^J]` to ordinary functors out of `J`. A functor
`G : J ⥤ C` into a simplicial category induces a simplicial functor `ofFunctor G`, which sends
every chain of paths from `i` to `j` to the image of the morphism `i ⟶ j`. Conversely, a simplicial
functor `F` has an underlying functor `toFunctor F`, which sends `i ⟶ j` to the image of the path
through every element in between. When there is at most one path between any two elements of `J`,
these constructions are inverse equivalences.

## Main declarations

* `SimplicialThickening.Path.Icc`: the path from `i` to `j` through every element in between.
* `SimplicialThickening.Path.subsingleton_of_forall_not_lt`: there is at most one path between
  two elements with nothing strictly in between.
* `SimplicialThickening.chainMk`: the chain of paths given by a monotone family of paths.
* `SimplicialThickening.monotone_chain`: the paths of a chain increase.
* `SimplicialThickening.isIso_eId`: the identity `𝟙_ SSet ⟶ N(Path x x)` is an isomorphism.
* `SimplicialThickening.pathVertex`: the vertex of a mapping simplicial set given by `Path.Icc`,
  with `pathVertex_refl` and `pathVertex_comp` relating it to identities and composition.
* `SimplicialThickening.hom_ext_of_subsingleton`: maps into a mapping simplicial set with at most
  one path between its endpoints are equal.
* `SimplicialThickening.ofFunctor`: the simplicial functor `C[Δ^J] ⥤ C` induced by an ordinary
  functor `J ⥤ C`.
* `SimplicialThickening.toFunctor`: the ordinary functor underlying a simplicial functor out of
  `C[Δ^J]`.
* `SimplicialThickening.functorEquiv`: simplicial functors out of `C[Δ^J]` are ordinary functors
  out of `J`, when all posets of paths are subsingletons.
-/

public section

open CategoryTheory EnrichedCategory MonoidalCategory CartesianMonoidalCategory Opposite Simplicial

universe u' u

namespace CategoryTheory.SimplicialThickening

variable {J : Type u} [LinearOrder J] {i j : J}

instance : Quiver.IsThin (Path i j) :=
  fun _ _ ↦ ⟨fun _ _ ↦ InducedCategory.hom_ext (Subsingleton.elim _ _)⟩

/-- The path from `i` to `j` through every element in between. -/
def Path.Icc (h : i ≤ j) : Path i j where
  I := Set.Icc i j
  left := ⟨le_rfl, h⟩
  right := ⟨h, le_rfl⟩
  left_le _ hk := hk.1
  le_right _ hk := hk.2

@[simp]
lemma Path.Icc_I (h : i ≤ j) : (Path.Icc h).I = Set.Icc i j :=
  (rfl)

/-- If no element lies strictly between `i` and `j`, there is at most one path from `i` to `j`.
For instance, this holds for all `i` and `j` in a linear order with at most two elements. -/
lemma Path.subsingleton_of_forall_not_lt (h : ∀ k, i < k → ¬k < j) : Subsingleton (Path i j) := by
  have key (p q : Path i j) (k : J) (hk : k ∈ p.I) : k ∈ q.I := by
    rcases (p.left_le k hk).eq_or_lt with rfl | hik
    · exact q.left
    rcases (p.le_right k hk).eq_or_lt with rfl | hkj
    · exact q.right
    exact absurd hkj (h k hik)
  exact ⟨fun p q ↦ Path.ext (Set.ext fun k ↦ ⟨key p q k, key q p k⟩)⟩

/-- The only path from an element to itself is the singleton. -/
instance (a : J) : Subsingleton (Path a a) :=
  Path.subsingleton_of_forall_not_lt fun _ h₁ h₂ ↦ lt_asymm h₁ h₂

/-- The identity of an object `x` of the simplicial thickening is an isomorphism
`𝟙_ SSet ≅ N(Path x x)`, since the only path from `x` to itself is `{x}`. -/
instance isIso_eId (x : SimplicialThickening J) : IsIso (eId SSet x) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [isIso_iff_bijective]
  refine ⟨fun _ _ _ ↦ rfl, fun s ↦ ⟨PUnit.unit, ?_⟩⟩
  obtain ⟨⟨d⟩⟩ := n
  exact ComposableArrows.ext (C := Path x.as x.as) (fun _ ↦ Subsingleton.elim _ _)
    (by subsingleton)

/-- The vertex of the mapping simplicial set from `i` to `j` given by the path through every
element in between. -/
def pathVertex {i j : SimplicialThickening J} (h : i.as ≤ j.as) : 𝟙_ SSet.{u} ⟶ (i ⟶[SSet] j) :=
  (SSet.unitHomEquiv _).symm (ComposableArrows.mk₀ (Path.Icc h))

/-- Maps into a mapping simplicial set of the simplicial thickening are equal when there is at
most one path between its endpoints. -/
lemma hom_ext_of_subsingleton {X : SSet.{u}} {i j : SimplicialThickening J}
    [Subsingleton (Path i.as j.as)] (f g : X ⟶ (i ⟶[SSet] j)) : f = g := by
  ext n : 2
  ext x
  exact nerve.ext_of_isThin (C := Path i.as j.as) (funext fun _ ↦ Subsingleton.elim _ _)

/-- The path vertex from an object to itself is the identity. -/
lemma pathVertex_refl (i : SimplicialThickening J) : pathVertex (le_refl i.as) = eId SSet i :=
  hom_ext_of_subsingleton _ _

/-- Composing the path vertices from `i` to `j` and from `j` to `k` gives the path vertex from
`i` to `k`, since `[i, j] ∪ [j, k] = [i, k]`. -/
lemma pathVertex_comp {i j k : SimplicialThickening J} (hij : i.as ≤ j.as) (hjk : j.as ≤ k.as) :
    (λ_ _).inv ≫ (pathVertex hij ⊗ₘ pathVertex hjk) ≫ eComp SSet i j k =
      pathVertex (hij.trans hjk) := by
  apply (SSet.unitHomEquiv _).injective
  exact nerve.ext_of_isThin (C := Path i.as k.as)
    (funext fun _ ↦ Path.ext (Set.Icc_union_Icc_eq_Icc hij hjk))

/-- The chain of paths given by a monotone family of paths. -/
def chainMk {d : ℕ} (p : Fin (d + 1) → Path i j) (hp : Monotone fun t ↦ (p t).I) :
    ComposableArrows (Path i j) d where
  obj := p
  map h := InducedCategory.homMk (homOfLE (hp (leOfHom h)))

@[simp]
lemma chainMk_obj {d : ℕ} (p : Fin (d + 1) → Path i j) (hp : Monotone fun t ↦ (p t).I)
    (t : Fin (d + 1)) : (chainMk p hp).obj t = p t := by
  rfl

/-- The paths of a chain of paths increase. -/
lemma monotone_chain {d : ℕ} (x : ComposableArrows (Path i j) d) :
    Monotone fun t ↦ (x.obj t).I :=
  fun _ _ h ↦ (x.map (homOfLE h)).hom.le

section Functor

variable {C : Type u'} [Category.{u} C] [SimplicialCategory C]

/-- The map of mapping simplicial sets underlying `ofFunctor G`: a chain of paths from `i` to `j`
is sent to the image under `G` of the morphism `i ⟶ j`. -/
@[expose]
def ofFunctorMap (G : J ⥤ C) (i j : SimplicialThickening J) :
    (i ⟶[SSet] j) ⟶ (G.obj i.as ⟶[SSet] G.obj j.as) where
  app n := ↾fun p ↦ (eHomEquiv SSet (G.map (homOfLE (Path.le (p.obj 0))))).app n PUnit.unit
  naturality _ _ f := by
    ext p
    simpa using ConcreteCategory.congr_hom
      ((eHomEquiv SSet (G.map (homOfLE (Path.le (p.obj 0))))).naturality f) PUnit.unit

/-- On a pair `i ≤ j`, the map `ofFunctorMap G i j` is constant at the image of `i ⟶ j`. -/
private lemma ofFunctorMap_eq {G : J ⥤ C} {i j : SimplicialThickening J} (h : i.as ≤ j.as) :
    ofFunctorMap G i j = toUnit _ ≫ eHomEquiv SSet (G.map (homOfLE h)) :=
  (rfl)

/-- The simplicial functor `C[Δ^J] ⥤ C` induced by an ordinary functor `G : J ⥤ C`. It sends
every chain of paths from `i` to `j` to the image under `G` of the morphism `i ⟶ j`, so it only
depends on the endpoints of the chains. -/
@[expose, implicit_reducible]
def ofFunctor (G : J ⥤ C) : EnrichedFunctor SSet (SimplicialThickening J) C where
  obj i := G.obj i.as
  map := ofFunctorMap G
  map_id i := by
    rw [ofFunctorMap_eq le_rfl, Subsingleton.elim (homOfLE _) (𝟙 i.as), Functor.map_id,
      eHomEquiv_id, comp_toUnit_assoc]
    exact Category.id_comp _
  map_comp i j k := by
    by_cases hij : i.as ≤ j.as
    · by_cases hjk : j.as ≤ k.as
      · rw [ofFunctorMap_eq hij, ofFunctorMap_eq hjk, ofFunctorMap_eq (hij.trans hjk),
          toUnit_eHomEquiv_tensorHom_comp_eComp, ← Functor.map_comp, homOfLE_comp,
          comp_toUnit_assoc]
      · ext n ⟨p, q⟩
        exact absurd (Path.le (q.obj 0)) hjk
    · ext n ⟨p, q⟩
      exact absurd (Path.le (p.obj 0)) hij

@[simp]
lemma ofFunctor_obj (G : J ⥤ C) (i : SimplicialThickening J) : (ofFunctor G).obj i = G.obj i.as :=
  rfl

lemma ofFunctor_map_eq (G : J ⥤ C) {i j : SimplicialThickening J} (h : i.as ≤ j.as) :
    (ofFunctor G).map i j = toUnit _ ≫ eHomEquiv SSet (G.map (homOfLE h)) :=
  ofFunctorMap_eq h

/-- The ordinary functor underlying a simplicial functor `C[Δ^J] ⥤ C`: a morphism `i ⟶ j` is
sent to the image of the path from `i` to `j` through every element in between. -/
@[expose, implicit_reducible]
def toFunctor (F : EnrichedFunctor SSet (SimplicialThickening J) C) : J ⥤ C where
  obj i := F.obj ⟨i⟩
  map {i j} h :=
    (eHomEquiv SSet).symm (pathVertex (i := ⟨i⟩) (j := ⟨j⟩) (leOfHom h) ≫ F.map ⟨i⟩ ⟨j⟩)
  map_id i := by
    rw [pathVertex_refl, EnrichedFunctor.map_id, ← eHomEquiv_id, Equiv.symm_apply_apply]
  map_comp {i j k} f g := by
    apply (eHomEquiv SSet).injective
    simp only [eHomEquiv_comp, Equiv.apply_symm_apply]
    rw [← pathVertex_comp (leOfHom f) (leOfHom g)]
    simp [EnrichedFunctor.map_comp, tensorHom_comp_tensorHom_assoc]

@[simp]
lemma toFunctor_obj (F : EnrichedFunctor SSet (SimplicialThickening J) C) (i : J) :
    (toFunctor F).obj i = F.obj ⟨i⟩ :=
  rfl

lemma eHomEquiv_toFunctor_map (F : EnrichedFunctor SSet (SimplicialThickening J) C) {i j : J}
    (h : i ⟶ j) :
    eHomEquiv SSet ((toFunctor F).map h) =
      pathVertex (i := ⟨i⟩) (j := ⟨j⟩) (leOfHom h) ≫ F.map ⟨i⟩ ⟨j⟩ :=
  Equiv.apply_symm_apply _ _

section Subsingleton

variable [∀ i j : J, Subsingleton (Path i j)]

/-- When there is at most one path between any two elements of `J`, simplicial functors out of
the simplicial thickening `C[Δ^J]` are ordinary functors out of `J`. This applies to linear orders
with at most two elements, which give the vertices and edges of the simplicial nerve. -/
def functorEquiv : (J ⥤ C) ≃ EnrichedFunctor SSet (SimplicialThickening J) C where
  toFun := ofFunctor
  invFun := toFunctor
  left_inv G := Functor.ext (fun _ ↦ rfl) fun i j h ↦ by
    dsimp only [toFunctor]
    rw [ofFunctor_map_eq _ (leOfHom h), comp_toUnit_assoc, toUnit_unit, Category.id_comp]
    exact (Equiv.symm_apply_apply _ _).trans (by
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      exact congrArg G.map (Subsingleton.elim _ _))
  right_inv F := by
    refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) fun ⟨i⟩ ⟨j⟩ ↦ ?_
    by_cases h : i ≤ j
    · rw [ofFunctor_map_eq _ h]
      dsimp only [toFunctor]
      rw [Equiv.apply_symm_apply, ← Category.assoc,
        hom_ext_of_subsingleton (toUnit _ ≫ pathVertex _) (𝟙 _), Category.id_comp]
      simp
    · ext n p
      exact absurd (Path.le (p.obj 0)) h

@[simp]
lemma functorEquiv_apply (G : J ⥤ C) : functorEquiv G = ofFunctor G :=
  (rfl)

@[simp]
lemma functorEquiv_symm_apply (F : EnrichedFunctor SSet (SimplicialThickening J) C) :
    functorEquiv.symm F = toFunctor F :=
  (rfl)

end Subsingleton

end Functor

end CategoryTheory.SimplicialThickening
