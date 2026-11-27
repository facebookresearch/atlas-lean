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
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/SimplicialNerve/Basic.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only import paths and the TauCeti helper namespace are adapted.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import MathlibExt.AlgebraicTopology.CategoricalSource.SimplicialThickening
public import MathlibExt.AlgebraicTopology.CategoricalSource.EnrichedCat
/-!
# The simplicial nerve as a functor, and its low-dimensional simplices

This file makes Mathlib's simplicial (homotopy coherent) nerve `SimplicialNerve C` of a
simplicial category `C` functorial in simplicial functors, and identifies its vertices and edges.

A functor `G : J ⥤ C` out of a linear order induces a simplicial functor
`SimplicialThickening.ofFunctor G : C[Δ^J] ⥤ C`, which sends every chain of paths from `i` to `j`
to the image of the unique morphism `i ⟶ j` (see
`MathlibExt.CategoricalSource.AlgebraicTopology.SimplicialNerve.SimplicialThickening`). Applied to `J = Fin (n + 1)`
this gives a map of simplicial sets `SimplicialNerve.fromNerve C : nerve C ⟶ SimplicialNerve C`
from the ordinary nerve of the underlying category. When no element of `J` lies strictly between
two others, every poset of paths is a subsingleton and `ofFunctor` is a bijection
(`SimplicialThickening.functorEquiv`).
Hence `fromNerve C` is bijective in degrees `0` and `1`: the vertices of `SimplicialNerve C` are
the objects of `C` and its edges are the morphisms of `C`. In higher degrees `fromNerve C` need not
be surjective: a `2`-simplex of `SimplicialNerve C` with edges `f`, `g` and long edge `h` records
an edge from `h` to `g ∘ f` in a mapping simplicial set, not an equality.

## Main declarations

* `CategoryTheory.simplicialNerveMap`: the map of simplicial nerves induced by a simplicial
  functor.
* `CategoryTheory.simplicialNerveFunctor`: the simplicial nerve as a functor from the category of
  small simplicial categories to simplicial sets.
* `CategoryTheory.SimplicialNerve.fromNerve`: the comparison map from the ordinary nerve of the
  underlying category, with `bijective_fromNerve_app` in degrees at most one.
* `CategoryTheory.SimplicialNerve.vertexEquiv`: vertices of `SimplicialNerve C` are objects of `C`.
* `CategoryTheory.SimplicialNerve.homEquiv`: edges of `SimplicialNerve C` are morphisms of `C`.

## References

* [Jacob Lurie, *Higher Topos Theory*, Section 1.1.5][LurieHTT]
-/

public section

open CategoryTheory EnrichedCategory Opposite Simplicial

universe v u

namespace CategoryTheory

section Functoriality

variable {C D E : Type u} [Category.{v} C] [SimplicialCategory C] [Category.{v} D]
  [SimplicialCategory D] [Category.{v} E] [SimplicialCategory E]

/-- The map of simplicial nerves induced by a simplicial functor, given by postcomposition. -/
def simplicialNerveMap (F : EnrichedFunctor SSet C D) : SimplicialNerve C ⟶ SimplicialNerve D where
  app _ := ↾fun G ↦ G.comp SSet F
  naturality _ _ _ := by
    ext G
    exact EnrichedFunctor.comp_assoc (V := SSet) _ _ _

@[simp]
lemma simplicialNerveMap_app (F : EnrichedFunctor SSet C D) (n : SimplexCategoryᵒᵖ)
    (G : (SimplicialNerve C).obj n) :
    (simplicialNerveMap F).app n G = EnrichedFunctor.comp SSet G F :=
  (rfl)

@[simp]
lemma simplicialNerveMap_id : simplicialNerveMap (EnrichedFunctor.id SSet C) = 𝟙 _ := by
  ext n G
  exact EnrichedFunctor.comp_id (V := SSet) _

lemma simplicialNerveMap_comp (F : EnrichedFunctor SSet C D) (G : EnrichedFunctor SSet D E) :
    simplicialNerveMap (F.comp SSet G) = simplicialNerveMap F ≫ simplicialNerveMap G := by
  ext n H
  exact (EnrichedFunctor.comp_assoc (V := SSet) _ _ _).symm

/-- The simplicial nerve, as a functor from the category of simplicial categories and simplicial
functors to simplicial sets. -/
@[expose]
def simplicialNerveFunctor : EnrichedCat.{v, v + 1, u} SSet.{v} ⥤ SSet.{max u v} where
  obj C := SimplicialNerve (ForgetEnrichment SSet C)
  map F := simplicialNerveMap F
  map_id _ := simplicialNerveMap_id
  map_comp {X Y Z} F G := simplicialNerveMap_comp (C := ForgetEnrichment SSet X)
    (D := ForgetEnrichment SSet Y) (E := ForgetEnrichment SSet Z) F G

@[simp]
lemma simplicialNerveFunctor_obj (C : EnrichedCat.{v, v + 1, u} SSet.{v}) :
    simplicialNerveFunctor.obj C = SimplicialNerve (ForgetEnrichment SSet C) :=
  rfl

@[simp]
lemma simplicialNerveFunctor_map {C D : EnrichedCat.{v, v + 1, u} SSet.{v}} (F : C ⟶ D) :
    simplicialNerveFunctor.map F = simplicialNerveMap F :=
  rfl

end Functoriality

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

namespace SimplicialNerve

variable (C)

/-- The comparison map from the ordinary nerve of the underlying category of a simplicial
category `C` to its simplicial nerve. An `n`-simplex `G : Fin (n + 1) ⥤ C` is sent to the
simplicial functor `SimplicialThickening.ofFunctor G`. -/
def fromNerve : nerve C ⟶ SimplicialNerve C where
  app n := ↾fun G ↦ SimplicialThickening.ofFunctor
    ((Monotone.functor (f := (ULift.down : ULift.{v} (Fin (n.unop.len + 1)) → _))
      fun _ _ h ↦ h) ⋙ G)
  naturality _ _ _ := by
    ext G
    refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) fun _ _ ↦ ?_
    ext k p
    rfl

lemma fromNerve_app_apply (n : SimplexCategoryᵒᵖ) (G : (nerve C).obj n) :
    (fromNerve C).app n G = SimplicialThickening.ofFunctor
      ((Monotone.functor (f := (ULift.down : ULift.{v} (Fin (n.unop.len + 1)) → _))
        fun _ _ h ↦ h) ⋙ G) :=
  (rfl)

/-- The comparison map from the ordinary nerve is bijective on vertices and on edges. -/
theorem bijective_fromNerve_app {n : SimplexCategoryᵒᵖ} (hn : n.unop.len ≤ 1) :
    Function.Bijective ((fromNerve C).app n) := by
  have (i j : ULift.{v} (Fin (n.unop.len + 1))) :
      Subsingleton (SimplicialThickening.Path i j) :=
    SimplicialThickening.Path.subsingleton_of_forall_not_lt fun k hik hkj ↦ by
      have h₁ : i.down.val < k.down.val := hik
      have h₂ : k.down.val < j.down.val := hkj
      omega
  let U := Monotone.functor (f := (ULift.down : ULift.{v} (Fin (n.unop.len + 1)) → _))
    fun _ _ h ↦ h
  let U' := Monotone.functor (f := (ULift.up : Fin (n.unop.len + 1) → ULift.{v} _)) fun _ _ h ↦ h
  -- `ULift.up` and `ULift.down` are inverse order isomorphisms, so `U` and `U'` cancel.
  have hU'U : U' ⋙ U = 𝟭 _ := Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦ Subsingleton.elim _ _
  have hUU' : U ⋙ U' = 𝟭 _ := Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦ Subsingleton.elim _ _
  have hU : Function.Bijective fun G : Fin (n.unop.len + 1) ⥤ C ↦ U ⋙ G :=
    Function.bijective_iff_has_inverse.2 ⟨fun G ↦ U' ⋙ G,
      fun G ↦ by dsimp only; rw [← Functor.assoc, hU'U, Functor.id_comp],
      fun F ↦ by dsimp only; rw [← Functor.assoc, hUU', Functor.id_comp]⟩
  have h : ⇑((fromNerve C).app n) = SimplicialThickening.functorEquiv ∘ fun G ↦ U ⋙ G :=
    funext fun G ↦ (fromNerve_app_apply C n G).trans
      (SimplicialThickening.functorEquiv_apply _).symm
  rw [h]
  exact SimplicialThickening.functorEquiv.bijective.comp hU

/-- The vertices of the simplicial nerve of `C` are the objects of `C`. -/
def vertexEquiv : SimplicialNerve C _⦋0⦌ ≃ C where
  toFun x := x.obj ⟨⟨0⟩⟩
  invFun x := (fromNerve C).app (op ⦋0⦌) (nerveEquiv.symm x)
  left_inv x := by
    obtain ⟨G, rfl⟩ := (bijective_fromNerve_app C (n := op ⦋0⦌) zero_le_one).2 x
    exact congrArg ((fromNerve C).app _) (nerveEquiv.left_inv G)
  right_inv _ := rfl

@[simp]
lemma vertexEquiv_apply (x : SimplicialNerve C _⦋0⦌) : vertexEquiv C x = x.obj ⟨⟨0⟩⟩ :=
  (rfl)

lemma vertexEquiv_symm_apply (x : C) :
    (vertexEquiv C).symm x = (fromNerve C).app (op ⦋0⦌) (nerveEquiv.symm x) :=
  (rfl)

variable {C}

/-- The edge of the simplicial nerve given by a morphism of the underlying category. -/
def edgeMk {x y : C} (f : x ⟶ y) :
    (SimplicialNerve C).Edge ((vertexEquiv C).symm x) ((vertexEquiv C).symm y) :=
  (nerve.edgeMk f).map (fromNerve C)

@[simp]
lemma edgeMk_edge {x y : C} (f : x ⟶ y) :
    (edgeMk f).edge = (fromNerve C).app (op ⦋1⦌) (ComposableArrows.mk₁ f) :=
  (rfl)

lemma edgeMk_injective {x y : C} : Function.Injective (edgeMk : (x ⟶ y) → _) := fun f g h ↦ by
  have := (bijective_fromNerve_app C (n := op ⦋1⦌) le_rfl).1 (congrArg SSet.Edge.edge h)
  have h' := congrArg nerve.homEquiv (SSet.Edge.ext this : nerve.edgeMk f = nerve.edgeMk g)
  rwa [nerve.homEquiv_edgeMk, nerve.homEquiv_edgeMk] at h'

lemma edgeMk_surjective {x y : C} : Function.Surjective (edgeMk : (x ⟶ y) → _) := fun e ↦ by
  have h₀ := (bijective_fromNerve_app C (n := op ⦋0⦌) zero_le_one).1
  obtain ⟨g, hg⟩ := (bijective_fromNerve_app C (n := op ⦋1⦌) le_rfl).2 e.edge
  have hsrc : (nerve C).δ 1 g = nerveEquiv.symm x :=
    h₀ (by rw [SSet.δ_naturality_apply, hg, e.src_eq]; rfl)
  have htgt : (nerve C).δ 0 g = nerveEquiv.symm y :=
    h₀ (by rw [SSet.δ_naturality_apply, hg, e.tgt_eq]; rfl)
  obtain ⟨f, hf⟩ := nerve.edgeMk_surjective (SSet.Edge.mk g hsrc htgt)
  exact ⟨f, SSet.Edge.ext (by rw [edgeMk_edge, ← nerve.edgeMk_edge, hf]; exact hg)⟩

/-- The edges of the simplicial nerve between the vertices given by two objects are the
morphisms between these objects. -/
noncomputable def homEquiv {x y : C} :
    (SimplicialNerve C).Edge ((vertexEquiv C).symm x) ((vertexEquiv C).symm y) ≃ (x ⟶ y) :=
  (Equiv.ofBijective _ ⟨edgeMk_injective, edgeMk_surjective⟩).symm

@[simp]
lemma homEquiv_edgeMk {x y : C} (f : x ⟶ y) : homEquiv (edgeMk f) = f :=
  (Equiv.ofBijective _ ⟨edgeMk_injective, edgeMk_surjective⟩).symm_apply_apply f

@[simp]
lemma edgeMk_homEquiv {x y : C}
    (e : (SimplicialNerve C).Edge ((vertexEquiv C).symm x) ((vertexEquiv C).symm y)) :
    edgeMk (homEquiv e) = e :=
  (Equiv.ofBijective _ ⟨edgeMk_injective, edgeMk_surjective⟩).apply_symm_apply e

end SimplicialNerve

end CategoryTheory
