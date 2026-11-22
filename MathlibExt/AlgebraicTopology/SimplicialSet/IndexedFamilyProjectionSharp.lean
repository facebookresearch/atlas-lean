/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.IndexedSums
import MathlibExt.AlgebraicTopology.SimplicialSet.SharpRecognition
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FullProductWeakEquivalences

/-!
# The SAME entire indexed family projection is sharp

Each original index labels its whole original simplicial coefficient.
Every simplex of the original constant label set has one fixed label.
Its native pullback is the full original coefficient product with the
standard simplex. Every complete transition is the original ordinal
map tensored with that same coefficient, with both projections retained.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial

namespace SSet.IndexedFamilyProjection

variable {I : Type u} (X : I → SSet.{u})

/-- The actual constant simplicial set of the original index labels. -/
abbrev base (I : Type u) : SSet.{u} := (SimplicialObject.const (Type u)).obj I

/-- The complete original family projection retains the actual index in every degree. -/
def projection : IndexedSums.object X ⟶ base I where
  app _ := ↾_root_.Sigma.fst
  naturality _ _ _ := rfl

/-- Every original represented simplex has its actual original constant label. -/
def label (s : SimplexIndex (base I)) : I := SSet.yonedaEquiv s.hom

/-- The entire original represented simplex has the SAME label on every full simplex. -/
lemma hom_app_label (s : SimplexIndex (base I)) (q : SimplexCategoryᵒᵖ)
    (a : (SSet.stdSimplex.obj s.left).obj q) : s.hom.app q a = label s := by
  calc
    s.hom.app q a = (SSet.yonedaEquiv.symm (label s)).app q a :=
      congrArg (fun f => f.app q a) (SSet.yonedaEquiv.symm_apply_apply s.hom).symm
    _ = label s := rfl

/-- The original coefficient and whole standard simplex map into the SAME native pullback. -/
def productToPullback (i : I) {n : SimplexCategory} (b : SSet.stdSimplex.obj n ⟶ base I)
    (hb : ∀ q a, b.app q a = i) : X i ⊗ SSet.stdSimplex.obj n ⟶ pullback (projection X) b :=
  pullback.lift (fst _ _ ≫ IndexedSums.inclusion X i) (snd _ _) (by
    apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro a
    exact (hb q a.2).symm)

/-- Its first projection is the SAME full original coefficient inclusion. -/
@[reassoc]
lemma productToPullback_fst (i : I) {n : SimplexCategory} (b : SSet.stdSimplex.obj n ⟶ base I)
    (hb : ∀ q a, b.app q a = i) :
    productToPullback X i b hb ≫ pullback.fst (projection X) b = fst _ _ ≫ IndexedSums.inclusion X i :=
  pullback.lift_fst _ _ _

/-- Its second projection is the SAME complete original standard-simplex parameter. -/
@[reassoc]
lemma productToPullback_snd (i : I) {n : SimplexCategory} (b : SSet.stdSimplex.obj n ⟶ base I)
    (hb : ∀ q a, b.app q a = i) :
    productToPullback X i b hb ≫ pullback.snd (projection X) b = snd _ _ := pullback.lift_snd _ _ _

/-- The comparison is an actual full Iso, preserving every coefficient and parameter simplex. -/
instance productToPullback_isIso (i : I) {n : SimplexCategory} (b : SSet.stdSimplex.obj n ⟶ base I)
    (hb : ∀ q a, b.app q a = i) : IsIso (productToPullback X i b hb) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro q
  rw [isIso_iff_bijective]
  let E := (CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type u)).obj q
  have hpb := (IsPullback.of_hasPullback (projection X) b).map E
  have hfst := congrArg (fun f => f.app q) (productToPullback_fst X i b hb)
  have hsnd := congrArg (fun f => f.app q) (productToPullback_snd X i b hb)
  constructor
  · intro a a' haa
    apply _root_.Prod.ext
    · have hc : (⟨i, a.1⟩ : Σ j : I, (X j).obj q) = ⟨i, a'.1⟩ :=
        (congr($(hfst) a)).symm.trans
          ((congrArg (fun z => (pullback.fst (projection X) b).app q z) haa).trans (congr($(hfst) a')))
      exact eq_of_heq (Sigma.mk.inj_iff.mp hc).2
    · exact (congr($(hsnd) a)).symm.trans
        ((congrArg (fun z => (pullback.snd (projection X) b).app q z) haa).trans (congr($(hsnd) a')))
  · intro a
    rcases hx : (pullback.fst (projection X) b).app q a with ⟨j, x⟩
    let t := (pullback.snd (projection X) b).app q a
    have hj : j = i := by
      have h := congr($(pullback.condition (f := projection X) (g := b)).app q a)
      change (projection X).app q ((pullback.fst (projection X) b).app q a) = b.app q t at h
      rw [hx] at h
      exact h.trans (hb q t)
    subst j
    refine ⟨(x, t), Types.ext_of_isPullback hpb ?_ ?_⟩
    · exact (congr($(hfst) (x, t))).trans hx.symm
    · exact congr($(hsnd) (x, t))

/-- Both full original maps identify the SAME native pullback with the whole coefficient product. -/
def pullbackProductIso (i : I) {n : SimplexCategory} (b : SSet.stdSimplex.obj n ⟶ base I)
    (hb : ∀ q a, b.app q a = i) : X i ⊗ SSet.stdSimplex.obj n ≅ pullback (projection X) b :=
  asIso (productToPullback X i b hb)

/-- Every full original simplex transition is the SAME original ordinal map
on the complete parameter, retaining its entire fixed original coefficient. -/
theorem transition_weak {s t : SimplexIndex (base I)} (a : s ⟶ t) :
    realizationWeakEquivalences ((simplexPullbackDiagram (projection X)).map a) := by
  let i := label t
  have ht : ∀ q x, t.hom.app q x = i := hom_app_label t
  have hs : ∀ q x, s.hom.app q x = i := by
    intro q x
    have h := congr($(CostructuredArrow.w a).app q x)
    exact h.symm.trans (ht q ((SSet.stdSimplex.map a.left).app q x))
  let eS := pullbackProductIso X i s.hom hs
  let eT := pullbackProductIso X i t.hom ht
  have hmap : eS.hom ≫ (simplexPullbackDiagram (projection X)).map a =
      (X i ◁ SSet.stdSimplex.map a.left) ≫ eT.hom := by
    change productToPullback X i s.hom hs ≫ simplexPullbackMap (projection X) a =
      (X i ◁ SSet.stdSimplex.map a.left) ≫ productToPullback X i t.hom ht
    apply pullback.hom_ext
    · rw [Category.assoc, simplexPullbackMap_fst, productToPullback_fst,
        Category.assoc, productToPullback_fst, whiskerLeft_fst_assoc]
    · rw [Category.assoc, simplexPullbackMap_snd, productToPullback_snd_assoc,
        Category.assoc, productToPullback_snd, whiskerLeft_snd]
  exact (realizationWeakEquivalences.arrow_mk_iso_iff
    (Arrow.isoMk' (X i ◁ SSet.stdSimplex.map a.left)
      ((simplexPullbackDiagram (projection X)).map a) eS eT hmap)).mp
    (realizationWeakEquivalences.whiskerLeft _ _ (stdSimplex_map_mem_realizationWeakEquivalences _))

/-- The SAME full original indexed family projection is sharp, without
Kan or nonempty-index premises and with ALL original simplex arities retained. -/
theorem projection_sharp : MorphismProperty.sharpMaps realizationWeakEquivalences (projection X) :=
  (sharpMaps_iff_simplexPullbackTransitions _).mpr (transition_weak X)

end SSet.IndexedFamilyProjection
