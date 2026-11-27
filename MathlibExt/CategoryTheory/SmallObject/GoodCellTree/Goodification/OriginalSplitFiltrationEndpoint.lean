/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tsutomu Okano, Codex
-/
module

public import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.Basic

/-!
# Original endpoints of compatible split diagrams

An actual colimit of the original target diagram and its original endpoint
splitting construct the source colimit. The source point is the original
retract endpoint, and both cocone-leg squares retain the original maps.
No source colimit, endpoint comparison or assembled splitting is assumed.
This is the colimit step in Hovey's Model Categories, Proposition 2.1.16,
and in the split-filtration argument of Higher Topos Theory, Appendix A.1.5.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u v uI vI

namespace CategoryTheory.SmallObject.OriginalSplitFiltrationEndpoint

open CategoryTheory.Limits CoherentRetracts

variable {C : Type u} [Category.{v} C] {I : Type uI} [Category.{vI} I]
  (D : I ⥤ SplitObject C) (c : Cocone (D ⋙ SplitObject.targetFunctor))
  {Y : C} (i : Y ⟶ c.pt) (r : c.pt ⟶ Y) (hir : i ≫ r = 𝟙 Y)
  (hcompat : ∀ a, c.ι.app a ≫ r ≫ i =
    (D.obj a).retraction ≫ (D.obj a).inclusion ≫ c.ι.app a)

/-- The actual split-source cocone has the original endpoint Y as its point. -/
abbrev sourceCocone : Cocone (D ⋙ SplitObject.sourceFunctor) where
  pt := Y
  ι := SplitObject.inclusionNatTrans D ≫ c.ι ≫ (Functor.const I).map r

include hcompat in
theorem sourceLeg_inclusion (a : I) :
    (sourceCocone D c r).ι.app a ≫ i = (D.obj a).inclusion ≫ c.ι.app a := by
  change ((D.obj a).inclusion ≫ c.ι.app a ≫ r) ≫ i = _
  calc
    _ = (D.obj a).inclusion ≫ (c.ι.app a ≫ r ≫ i) := by
      simp only [Category.assoc]
    _ = (D.obj a).inclusion ≫
        ((D.obj a).retraction ≫ (D.obj a).inclusion ≫ c.ι.app a) := by
      rw [hcompat a]
    _ = ((D.obj a).inclusion ≫ (D.obj a).retraction) ≫
        (D.obj a).inclusion ≫ c.ι.app a := by simp only [Category.assoc]
    _ = _ := by rw [(D.obj a).splitting, Category.id_comp]

include hir hcompat in
theorem targetLeg_retraction (a : I) :
    c.ι.app a ≫ r = (D.obj a).retraction ≫ (sourceCocone D c r).ι.app a := by
  change c.ι.app a ≫ r = (D.obj a).retraction ≫
    ((D.obj a).inclusion ≫ c.ι.app a ≫ r)
  have h := congrArg (fun f => f ≫ r) (hcompat a)
  simpa only [Category.assoc, hir, Category.comp_id] using h

/-- Every actual source cocone gives a target cocone by the original projections. -/
abbrev targetCocone (t : Cocone (D ⋙ SplitObject.sourceFunctor)) :
    Cocone (D ⋙ SplitObject.targetFunctor) where
  pt := t.pt
  ι := SplitObject.retractionNatTrans D ≫ t.ι

/-- The original target UP constructs the actual source descender. -/
def desc (hc : IsColimit c) (t : Cocone (D ⋙ SplitObject.sourceFunctor)) : Y ⟶ t.pt :=
  i ≫ hc.desc (targetCocone D t)

/-- The original endpoint Y is a colimit of the split sources, proved from the target UP. -/
def sourceIsColimit (hc : IsColimit c) : IsColimit (sourceCocone D c r) where
  desc := desc D c i hc
  fac t a := by
    change (sourceCocone D c r).ι.app a ≫
      (i ≫ hc.desc (targetCocone D t)) = t.ι.app a
    rw [← Category.assoc, sourceLeg_inclusion D c i r hcompat a,
      Category.assoc, hc.fac]
    change (D.obj a).inclusion ≫ ((D.obj a).retraction ≫ t.ι.app a) = _
    rw [← Category.assoc, (D.obj a).splitting, Category.id_comp]
  uniq t m hm := by
    have hdesc : r ≫ m = hc.desc (targetCocone D t) := by
      apply hc.hom_ext
      intro a
      rw [← Category.assoc, targetLeg_retraction D c i r hir hcompat a,
        Category.assoc, hm a, hc.fac]
      rfl
    change m = i ≫ hc.desc (targetCocone D t)
    calc
      m = (i ≫ r) ≫ m := by rw [hir, Category.id_comp]
      _ = i ≫ (r ≫ m) := Category.assoc _ _ _
      _ = _ := by rw [hdesc]

/-- Both original endpoint objects and maps form the actual endpoint splitting. -/
def endpointSplit : SplitObject C where
  source := Y
  target := c.pt
  inclusion := i
  retraction := r
  splitting := hir

/-- Every original target cocone leg and constructed source leg retains both splitting squares. -/
def splittingCocone : Cocone D where
  pt := endpointSplit D c i r hir
  ι :=
    { app a :=
        { left := (sourceCocone D c r).ι.app a
          right := c.ι.app a
          inclusion_naturality := (sourceLeg_inclusion D c i r hcompat a).symm
          retraction_naturality := (targetLeg_retraction D c i r hir hcompat a).symm }
      naturality a b f := by
        apply SplitObject.Hom.ext
        · exact (sourceCocone D c r).ι.naturality f
        · exact c.ι.naturality f }

/-- The actual endpoint splitting cocone has both original component universal properties. -/
def splittingIsColimit (hc : IsColimit c) :
    IsColimit (splittingCocone D c i r hir hcompat) where
  desc t :=
    { left := (sourceIsColimit D c i r hir hcompat hc).desc
        (SplitObject.sourceFunctor.mapCocone t)
      right := hc.desc (SplitObject.targetFunctor.mapCocone t)
      inclusion_naturality := by
        change i ≫ hc.desc (SplitObject.targetFunctor.mapCocone t) =
          (sourceIsColimit D c i r hir hcompat hc).desc
            (SplitObject.sourceFunctor.mapCocone t) ≫ t.pt.inclusion
        apply (sourceIsColimit D c i r hir hcompat hc).hom_ext
        intro a
        rw [← Category.assoc, sourceLeg_inclusion D c i r hcompat,
          Category.assoc, hc.fac, ← Category.assoc,
          (sourceIsColimit D c i r hir hcompat hc).fac]
        exact (t.ι.app a).inclusion_naturality
      retraction_naturality := by
        change r ≫ (sourceIsColimit D c i r hir hcompat hc).desc
            (SplitObject.sourceFunctor.mapCocone t) =
          hc.desc (SplitObject.targetFunctor.mapCocone t) ≫ t.pt.retraction
        apply hc.hom_ext
        intro a
        rw [← Category.assoc, targetLeg_retraction D c i r hir hcompat,
          Category.assoc, (sourceIsColimit D c i r hir hcompat hc).fac,
          ← Category.assoc, hc.fac]
        exact (t.ι.app a).retraction_naturality }
  fac t a := by
    apply SplitObject.Hom.ext
    · exact (sourceIsColimit D c i r hir hcompat hc).fac
        (SplitObject.sourceFunctor.mapCocone t) a
    · exact hc.fac (SplitObject.targetFunctor.mapCocone t) a
  uniq t m hm := by
    apply SplitObject.Hom.ext
    · apply (sourceIsColimit D c i r hir hcompat hc).hom_ext
      intro a
      exact (congrArg SplitObject.Hom.left (hm a)).trans
        ((sourceIsColimit D c i r hir hcompat hc).fac
          (SplitObject.sourceFunctor.mapCocone t) a).symm
    · apply hc.hom_ext
      intro a
      exact (congrArg SplitObject.Hom.right (hm a)).trans
        (hc.fac (SplitObject.targetFunctor.mapCocone t) a).symm

end CategoryTheory.SmallObject.OriginalSplitFiltrationEndpoint
