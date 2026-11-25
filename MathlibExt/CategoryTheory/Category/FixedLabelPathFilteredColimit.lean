/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Category.FixedLabelPathMaps
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Complete native paths in original filtered generator colimits

The entire arrow diagram and its genuine filtered colimit produce an
actual cocone of full native paths. Every full path occurs at an original
stage. With injective original transition maps the same cocone is proved
colimiting, retaining all original labels and complete paths.
-/

noncomputable section
universe u v w
open CategoryTheory Limits

namespace CategoryTheory.FixedLabelPathMaps.FilteredColimit

variable {O : Type u} {J : Type v} [Category.{w} J]
  (A : O → O → J ⥤ Type u)
  (c : ∀ a b, Cocone (A a b))

/-- The exact original arrow family at one original diagram stage. -/
@[instance_reducible]
def stageQuiver (j : J) : Quiver.{u} O where
  Hom a b := (A a b).obj j

/-- The exact full original arrow family of the supplied generator cocone. -/
@[instance_reducible]
def colimitQuiver : Quiver.{u} O where
  Hom a b := (c a b).pt

/-- Map a complete path by the same original diagram arrow map. -/
def stageMap {i j : J} (f : i ⟶ j) {a b : O}
    (p : @Quiver.Path O (stageQuiver A i) a b) : @Quiver.Path O (stageQuiver A j) a b :=
  mapPath (stageQuiver A i) (stageQuiver A j) (fun {a b} e => (A a b).map f e) p

/-- The actual stage cocone map on every complete path. -/
def injection (j : J) {a b : O} (p : @Quiver.Path O (stageQuiver A j) a b) :
    @Quiver.Path O (colimitQuiver A c) a b :=
  mapPath (stageQuiver A j) (colimitQuiver A c) (fun {a b} e => (c a b).ι.app j e) p

/-- The full original path injection preserves actual complete concatenation. -/
theorem injection_comp (j : J) {a b d : O}
    (p : @Quiver.Path O (stageQuiver A j) a b)
    (r : @Quiver.Path O (stageQuiver A j) b d) :
    injection A c j (@Quiver.Path.comp O (stageQuiver A j) a b d p r) =
      @Quiver.Path.comp O (colimitQuiver A c) a b d (injection A c j p) (injection A c j r) :=
  mapPath_comp (stageQuiver A j) (colimitQuiver A c)
    (fun {a b} e => (c a b).ι.app j e) p r

/-- Every full original stage path map retains the same identity. -/
theorem stageMap_id (j : J) {a b : O} (p : @Quiver.Path O (stageQuiver A j) a b) :
    stageMap A (𝟙 j) p = p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      rw [stageMap, mapPath_cons]
      change @Quiver.Path.cons O (stageQuiver A j) _ _ _
        (stageMap A (𝟙 j) p) ((A _ _).map (𝟙 j) e) = @Quiver.Path.cons O (stageQuiver A j) _ _ _ p e
      rw [ih, Functor.map_id_apply]

/-- Consecutive full original stage maps are the same whole composite map. -/
theorem stageMap_comp {i j k : J} (f : i ⟶ j) (g : j ⟶ k) {a b : O}
    (p : @Quiver.Path O (stageQuiver A i) a b) :
    stageMap A (f ≫ g) p = stageMap A g (stageMap A f p) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change @Quiver.Path.cons O (stageQuiver A k) _ _ _
        (stageMap A (f ≫ g) p) ((A _ _).map (f ≫ g) e) =
        @Quiver.Path.cons O (stageQuiver A k) _ _ _
          (stageMap A g (stageMap A f p)) ((A _ _).map g ((A _ _).map f e))
      rw [ih, Functor.map_comp_apply]

/-- The entire full-path cocone retains every original generator cocone equation. -/
theorem injection_stageMap {i j : J} (f : i ⟶ j) {a b : O}
    (p : @Quiver.Path O (stageQuiver A i) a b) :
    injection A c j (stageMap A f p) = injection A c i p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change @Quiver.Path.cons O (colimitQuiver A c) _ _ _
        (injection A c j (stageMap A f p)) ((c _ _).ι.app j ((A _ _).map f e)) =
        @Quiver.Path.cons O (colimitQuiver A c) _ _ _ (injection A c i p) ((c _ _).ι.app i e)
      rw [ih]
      exact congrArg (fun e => @Quiver.Path.cons O (colimitQuiver A c) _ _ _ (injection A c i p) e)
        (congr($((c _ _).w f) e))

/-- The actual native full-path Hom diagram at the same two original labels. -/
def pathDiagram (a b : O) : J ⥤ Type u where
  obj j := @Quiver.Path O (stageQuiver A j) a b
  map f := ↾stageMap A f
  map_id j := by ext p; exact stageMap_id A j p
  map_comp f g := by ext p; exact stageMap_comp A f g p

/-- The actual whole-path cocone keeps the supplied original generator colimit. -/
def pathCocone (a b : O) : Cocone (pathDiagram A a b) where
  pt := @Quiver.Path O (colimitQuiver A c) a b
  ι :=
    { app j := ↾injection A c j
      naturality i j f := by ext p; exact injection_stageMap A c f p }

variable [IsFiltered J] (hc : ∀ a b, IsColimit (c a b))

include hc in
/-- Every full original path in the generator colimit is the image of a path at one original
stage. -/
theorem jointly_surjective {a b : O} (p : @Quiver.Path O (colimitQuiver A c) a b) :
    ∃ (j : J) (q : @Quiver.Path O (stageQuiver A j) a b), injection A c j q = p := by
  induction p with
  | nil =>
      exact ⟨Classical.choice IsFiltered.nonempty, @Quiver.Path.nil O (stageQuiver A
        (Classical.choice
        IsFiltered.nonempty)) _, rfl⟩
  | cons p e ih =>
      obtain ⟨i, p, hp⟩ := ih
      obtain ⟨j, e, he⟩ := Types.jointly_surjective_of_isColimit (hc _ _) e
      let k := IsFiltered.max i j
      let fi := IsFiltered.leftToMax i j
      let fj := IsFiltered.rightToMax i j
      refine ⟨k, @Quiver.Path.cons O (stageQuiver A k) _ _ _
        (stageMap A fi p) ((A _ _).map fj e), ?_⟩
      change @Quiver.Path.cons O (colimitQuiver A c) _ _ _
        (injection A c k (stageMap A fi p)) ((c _ _).ι.app k ((A _ _).map fj e)) = _
      rw [injection_stageMap, hp]
      exact congrArg (fun e => @Quiver.Path.cons O (colimitQuiver A c) _ _ _ _ e)
        ((congr($((c _ _).w fj) e)).trans he)



variable (hm : ∀ {i j : J} (f : i ⟶ j) (a b : O),
  Function.Injective ((A a b).map f))

include hc hm in
/-- Every original generator colimit leg is injective from the actual monic transitions. -/
theorem generator_injection_injective (j : J) (a b : O) :
    Function.Injective ((c a b).ι.app j) := by
  intro x y hxy
  obtain ⟨k, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' (hc a b) x y).mp hxy
  exact hm f a b hf

include hc hm in
/-- Every complete original path colimit leg is injective. -/
theorem injection_injective (j : J) (a b : O) :
    Function.Injective (injection A c j (a := a) (b := b)) :=
  mapPath_injective (stageQuiver A j) (colimitQuiver A c)
    (fun {a b} e => (c a b).ι.app j e)
    (fun a b => generator_injection_injective A c hc hm j a b) a b

/-- The complete native paths form the actual filtered colimit at every original endpoint pair. -/
def pathIsColimit (a b : O) : IsColimit (pathCocone A c a b) :=
  Types.FilteredColimit.isColimitOf' (pathDiagram A a b) (pathCocone A c a b)
    (fun p => by obtain ⟨j, q, rfl⟩ := jointly_surjective A c hc p; exact ⟨j, q, rfl⟩)
    (fun j p q h => ⟨j, 𝟙 j, by
      have hpq := injection_injective A c hc hm j a b h
      rw [hpq]⟩)

end CategoryTheory.FixedLabelPathMaps.FilteredColimit
