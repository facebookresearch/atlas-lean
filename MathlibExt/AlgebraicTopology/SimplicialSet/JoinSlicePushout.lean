/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceIndexIso
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Index pushouts and original over-slice pullbacks

A pushout of indexing simplicial sets induces a pullback of the original
over-slice carriers. In each degree, the proof glues the whole joined maps
using preservation of pushouts by the join with a fixed left factor. The
original indexing pushout verifies the fixed-right-factor condition.

The common restriction uses the canonical equality of fixed diagrams from
the indexing square. Its readback preserves the entire joined map.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet.sliceOver

variable {A B C D X : SSet.{u}} {f : A ⟶ B} {g : A ⟶ C}
  {f' : B ⟶ D} {g' : C ⟶ D}

/-- The right restriction of an indexing square, transported to the same
fixed diagram as the left restriction. -/
def commSqRightRestriction (sq : CommSq f g f' g') (q : D ⟶ X) :
    sliceOver X (g' ≫ q) ⟶ sliceOver X (f ≫ (f' ≫ q)) :=
  restrict X (g' ≫ q) g ≫ eqToHom (congrArg (sliceOver X) (by
    rw [← Category.assoc, ← sq.w, Category.assoc]))

/-- Transporting the fixed diagram leaves the whole original restricted map
unchanged. -/
@[simp]
theorem commSqRightRestriction_app_val (sq : CommSq f g f' g') (q : D ⟶ X)
    (n : SimplexCategoryᵒᵖ) (s : (sliceOver X (g' ≫ q)).obj n) :
    (((commSqRightRestriction sq q).app n s).1) =
      (join.obj (stdSimplex.obj n.unop)).map g ≫ s.1 := by
  have heq : g ≫ (g' ≫ q) = f ≫ (f' ≫ q) := by
    rw [← Category.assoc, ← sq.w, Category.assoc]
  exact fixedDiagramEq_app_val heq n ((restrict X (g' ≫ q) g).app n s)

/-- The original restrictions of an indexing square commute after the
canonical identification of their fixed diagrams. -/
theorem restrict_commSq (sq : CommSq f g f' g') (q : D ⟶ X) :
    restrict X q f' ≫ restrict X (f' ≫ q) f =
      restrict X q g' ≫ commSqRightRestriction sq q := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  simp only [NatTrans.comp_app, types_comp_apply, restrict_app_val,
    commSqRightRestriction_app_val]
  rw [← Category.assoc, ← Functor.map_comp, sq.w,
    Functor.map_comp, Category.assoc]

/-- An actual pushout of indexing shapes gives an actual pullback of the
full original over-slice carriers. The result applies to arbitrary simplicial
sets and retains the original restrictions in every degree. -/
theorem isPullback_restrict_of_isPushout (hpo : IsPushout f g f' g') (q : D ⟶ X) :
    IsPullback (restrict X q f') (restrict X q g')
      (restrict X (f' ≫ q) f)
      (restrict X (g' ≫ q) g ≫ eqToHom (congrArg (sliceOver X) (by
        rw [← Category.assoc, ← hpo.w, Category.assoc]))) := by
  change IsPullback (restrict X q f') (restrict X q g')
    (restrict X (f' ≫ q) f) (commSqRightRestriction hpo.toCommSq q)
  apply IsPullback.of_forall_isPullback_app
  intro n
  let J := join.obj (stdSimplex.obj n.unop)
  have hJ : IsPushout (J.map f) (J.map g) (J.map f') (J.map g') := hpo.map J
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨?_, ?_, ?_⟩
  · simpa only [NatTrans.comp_app] using
      NatTrans.congr_app (restrict_commSq hpo.toCommSq q) n
  · rintro s t ⟨hb, hc⟩
    apply Subtype.ext
    apply hJ.hom_ext
    · simpa only [restrict_app_val] using congrArg Subtype.val hb
    · simpa only [restrict_app_val] using congrArg Subtype.val hc
  · intro sb sc hbc
    have hw : J.map f ≫ sb.1 = J.map g ≫ sc.1 := by
      simpa only [restrict_app_val, commSqRightRestriction_app_val] using
        congrArg Subtype.val hbc
    obtain ⟨d, hdb, hdc⟩ := hJ.exists_desc sb.1 sc.1 hw
    have hd : joinInr (stdSimplex.obj n.unop) D ≫ d = q := by
      apply hpo.hom_ext
      · rw [← Category.assoc, map_comp_joinInr, Category.assoc, hdb]
        exact sb.2
      · rw [← Category.assoc, map_comp_joinInr, Category.assoc, hdc]
        exact sc.2
    refine ⟨⟨d, hd⟩, ?_, ?_⟩
    · apply Subtype.ext
      exact hdb
    · apply Subtype.ext
      exact hdc

end SSet.sliceOver
