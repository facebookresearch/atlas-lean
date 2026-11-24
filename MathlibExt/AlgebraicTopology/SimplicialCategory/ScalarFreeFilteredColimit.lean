/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectFilteredColimits
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectScalarCategories
import MathlibExt.CategoryTheory.Category.FixedLabelPathFilteredColimit
import MathlibExt.CategoryTheory.Category.RelativeFreePresentation

/-!
# Complete original scalar path presentations in filtered enriched colimits

The full original scalar Hom cocone is colimiting. A compatible actual
generator path presentation gives a genuine cocone of complete paths
to those same Hom simplices. The genuine generator and Hom colimits
then construct the complete free presentation, keeping the original
stage maps and all individual object labels.
-/

noncomputable section
universe u v w
open CategoryTheory Limits Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.ScalarFreeColimit
open RelativeWords
open CategoryTheory.FixedLabelPathMaps

variable {O : Type u} {J : Type v} [Category.{w} J] [IsFiltered J] [Small.{u} J]
  (F : J ⥤ FixedObjects O) (s : Cocone F) (hs : IsColimit s) (q : SimplexCategoryᵒᵖ)
  (A : O → O → J ⥤ Type u)
  (c : ∀ a b, Cocone (A a b)) (hc : ∀ a b, IsColimit (c a b))
  (hm : ∀ {i j : J} (f : i ⟶ j) (a b : O), Function.Injective ((A a b).map f))

/-- The whole actual scalar Hom diagram of the original enriched diagram. -/
def homDiagram (a b : O) : J ⥤ Type u :=
  F ⋙ evaluation a b ⋙ (CategoryTheory.evaluation _ _).obj q

/-- The full actual scalar Hom cocone retains every original enriched cocone leg. -/
def homCocone (a b : O) : Cocone (homDiagram F q a b) :=
  ((CategoryTheory.evaluation _ _).obj q).mapCocone ((evaluation a b).mapCocone s)

/-- The entire actual scalar Hom cocone is genuinely colimiting. -/
def homIsColimit (a b : O) : IsColimit (homCocone F s q a b) :=
  isColimitOfPreserves ((CategoryTheory.evaluation _ _).obj q)
    (isColimitOfPreserves (evaluation a b) hs)

/-- Genuine original path evaluations on each entire original scalar stage. -/
structure StagePresentation where
  /-- Evaluate every whole native path in the actual original Hom simplex. -/
  map (j : J) {a b : O} :
    @Quiver.Path O (FixedLabelPathMaps.FilteredColimit.stageQuiver A j) a b →
      (hom (F.obj j) a b).obj q
  /-- The original empty path is the actual original scalar identity. -/
  map_id (j : J) (a : O) : map j (@Quiver.Path.nil O (FixedLabelPathMaps.FilteredColimit.stageQuiver A j) a) =
    (identityMap (F.obj j) a).app q PUnit.unit
  /-- Every whole native path composition is genuine original scalar composition. -/
  map_comp (j : J) {a b c : O}
      (p : @Quiver.Path O (FixedLabelPathMaps.FilteredColimit.stageQuiver A j) a b)
      (r : @Quiver.Path O (FixedLabelPathMaps.FilteredColimit.stageQuiver A j) b c) :
    map j (@Quiver.Path.comp O (FixedLabelPathMaps.FilteredColimit.stageQuiver A j) a b c p r) = (compositionMap
      (F.obj j) a b c).app q (map j p, map j r)
  /-- These actual whole stage Hom maps are genuinely bijective. -/
  bijective (j : J) (a b : O) : Function.Bijective (@map j a b)
  /-- The whole path evaluation retains every actual original stage map. -/
  naturality {i j : J} (f : i ⟶ j) {a b : O}
      (p : @Quiver.Path O (FixedLabelPathMaps.FilteredColimit.stageQuiver A i) a b) :
    map j (FixedLabelPathMaps.FilteredColimit.stageMap A f p) =
      (homMap (F.map f) a b).app q (map i p)

variable (P : StagePresentation F q A)

/-- The complete original stage path evaluations give the actual path cocone to original Hom simplices. -/
def evaluationCocone (a b : O) :
    Cocone (FixedLabelPathMaps.FilteredColimit.pathDiagram A a b) where
  pt := (hom s.pt a b).obj q
  ι :=
    { app j := ↾fun p => (homMap (s.ι.app j) a b).app q (P.map j p)
      naturality i j f := by
        ext p
        change (homMap (s.ι.app j) a b).app q
          (P.map j (FixedLabelPathMaps.FilteredColimit.stageMap A f p)) =
            (homMap (s.ι.app i) a b).app q (P.map i p)
        have hp := P.naturality f p
        have h := congrArg (fun e => homMap e a b) (s.w f)
        have hcomp := homMap_comp (F.map f) (s.ι.app j) a b
        have h' := hcomp.symm.trans h
        exact (congrArg (fun e => (homMap (s.ι.app j) a b).app q e) hp).trans
          (congrArg (fun e => e.app q (P.map i p)) h') }

/-- Evaluate every complete path of the genuine generator colimit by the original Hom cocone. -/
def evaluate {a b : O}
    (p : @Quiver.Path O (FixedLabelPathMaps.FilteredColimit.colimitQuiver A c) a b) :
    (hom s.pt a b).obj q :=
  (FixedLabelPathMaps.FilteredColimit.pathIsColimit A c hc hm a b).desc
    (evaluationCocone F s q A P a b) p

omit [Small.{u} J] in
/-- Evaluation keeps every actual original whole stage path map. -/
theorem evaluate_injection {a b : O} (j : J)
    (p : @Quiver.Path O (FixedLabelPathMaps.FilteredColimit.stageQuiver A j) a b) :
    evaluate F s q A c hc hm P (FixedLabelPathMaps.FilteredColimit.injection A c j p) =
      (homMap (s.ι.app j) a b).app q (P.map j p) :=
  congr($((FixedLabelPathMaps.FilteredColimit.pathIsColimit A c hc hm a b).fac
    (evaluationCocone F s q A P a b) j) p)


include hs in
/-- Every actual original colimit Hom simplex is the evaluation of a complete original path. -/
theorem evaluate_surjective (a b : O) :
    Function.Surjective (evaluate F s q A c hc hm P (a := a) (b := b)) := by
  intro x
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit (homIsColimit F s hs q a b) x
  obtain ⟨p, rfl⟩ := (P.bijective j a b).2 y
  exact ⟨FixedLabelPathMaps.FilteredColimit.injection A c j p,
    (evaluate_injection F s q A c hc hm P j p).trans hy⟩

include hs in
/-- Complete path evaluation is injective in the SAME original scalar Hom colimit. -/
theorem evaluate_injective (a b : O) :
    Function.Injective (evaluate F s q A c hc hm P (a := a) (b := b)) := by
  intro p r h
  obtain ⟨i, p, rfl⟩ := FixedLabelPathMaps.FilteredColimit.jointly_surjective A c hc p
  obtain ⟨j, r, rfl⟩ := FixedLabelPathMaps.FilteredColimit.jointly_surjective A c hc r
  rw [evaluate_injection, evaluate_injection] at h
  obtain ⟨k, f, g, hfg⟩ := (Types.FilteredColimit.isColimit_eq_iff
    (homDiagram F q a b) (homIsColimit F s hs q a b)).mp h
  change (homMap (F.map f) a b).app q (P.map i p) =
    (homMap (F.map g) a b).app q (P.map j r) at hfg
  rw [← P.naturality, ← P.naturality] at hfg
  have hp := (P.bijective k a b).1 hfg
  calc
    _ = FixedLabelPathMaps.FilteredColimit.injection A c k
        (FixedLabelPathMaps.FilteredColimit.stageMap A f p) :=
      (FixedLabelPathMaps.FilteredColimit.injection_stageMap A c f p).symm
    _ = FixedLabelPathMaps.FilteredColimit.injection A c k
        (FixedLabelPathMaps.FilteredColimit.stageMap A g r) := congrArg _ hp
    _ = _ := FixedLabelPathMaps.FilteredColimit.injection_stageMap A c g r


omit [Small.{u} J] in
/-- The colimit path evaluation keeps the actual original identity. -/
theorem evaluate_id (a : O) :
    evaluate F s q A c hc hm P
        (@Quiver.Path.nil O (FixedLabelPathMaps.FilteredColimit.colimitQuiver A c) a) =
      (identityMap s.pt a).app q PUnit.unit := by
  let j : J := Classical.choice IsFiltered.nonempty
  have hj := evaluate_injection F s q A c hc hm P j
    (@Quiver.Path.nil O (FixedLabelPathMaps.FilteredColimit.stageQuiver A j) a)
  change evaluate F s q A c hc hm P (@Quiver.Path.nil O (FixedLabelPathMaps.FilteredColimit.colimitQuiver A c) a) =
    (homMap (s.ι.app j) a a).app q (P.map j (@Quiver.Path.nil O (FixedLabelPathMaps.FilteredColimit.stageQuiver A j)
      a)) at hj
  exact hj.trans ((congrArg ((homMap (s.ι.app j) a a).app q) (P.map_id j a)).trans
    (congr($(identityMap_homMap (s.ι.app j) a).app q PUnit.unit)))

omit [Small.{u} J] in
/-- The colimit path evaluation retains every whole original composition. -/
theorem evaluate_comp {a b d : O}
    (p : @Quiver.Path O (FixedLabelPathMaps.FilteredColimit.colimitQuiver A c) a b)
    (r : @Quiver.Path O (FixedLabelPathMaps.FilteredColimit.colimitQuiver A c) b d) :
    evaluate F s q A c hc hm P
        (@Quiver.Path.comp O (FixedLabelPathMaps.FilteredColimit.colimitQuiver A c) a b d p r) =
      (compositionMap s.pt a b d).app q
        (evaluate F s q A c hc hm P p, evaluate F s q A c hc hm P r) := by
  obtain ⟨i, p, rfl⟩ := FixedLabelPathMaps.FilteredColimit.jointly_surjective A c hc p
  obtain ⟨j, r, rfl⟩ := FixedLabelPathMaps.FilteredColimit.jointly_surjective A c hc r
  let k := IsFiltered.max i j
  let fi := IsFiltered.leftToMax i j
  let fj := IsFiltered.rightToMax i j
  let p' := FixedLabelPathMaps.FilteredColimit.stageMap A fi p
  let r' := FixedLabelPathMaps.FilteredColimit.stageMap A fj r
  have hp := FixedLabelPathMaps.FilteredColimit.injection_stageMap A c fi p
  have hr := FixedLabelPathMaps.FilteredColimit.injection_stageMap A c fj r
  have hi := FixedLabelPathMaps.FilteredColimit.injection_comp A c k p' r'
  have hj := evaluate_injection F s q A c hc hm P k
    (@Quiver.Path.comp O (FixedLabelPathMaps.FilteredColimit.stageQuiver A k) a b d p' r')
  have hP := P.map_comp k p' r'
  have hE := congr($(compositionMap_homMap (s.ι.app k) a b d).app q (P.map k p', P.map k r'))
  have hx := evaluate_injection F s q A c hc hm P k p'
  have hy := evaluate_injection F s q A c hc hm P k r'
  have hz := hj.trans ((congrArg ((homMap (s.ι.app k) a d).app q) hP).trans hE)
  have hpath := hi.trans (congrArg₂
    (@Quiver.Path.comp O (FixedLabelPathMaps.FilteredColimit.colimitQuiver A c) a b d) hp hr)
  exact (congrArg (evaluate F s q A c hc hm P) hpath).symm.trans
    (hz.trans (congrArg₂ (fun x y => (compositionMap s.pt a b d).app q (x,y))
      (hx.symm.trans (congrArg (evaluate F s q A c hc hm P) hp))
      (hy.symm.trans (congrArg (evaluate F s q A c hc hm P) hr))))

/-- The genuine terminal scalar free presentation retains the same original enriched colimit. -/
def presentation : FreePresentation.{u,u,u} (scalarCategory s.pt q) where
  quiver := FixedLabelPathMaps.FilteredColimit.colimitQuiver A c
  map p := evaluate F s q A c hc hm P p
  map_id a := evaluate_id F s q A c hc hm P a
  map_comp p r := evaluate_comp F s q A c hc hm P p r
  bijective a b := ⟨evaluate_injective F s hs q A c hc hm P a b,
    evaluate_surjective F s hs q A c hc hm P a b⟩

end CategoryTheory.SimplicialEnrichment.FixedObjects.ScalarFreeColimit
