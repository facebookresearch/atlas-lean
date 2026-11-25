/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.KTheory.Exact.Quillen.SpanMap

/-!
# Span-map composition compatibility

For an additive exact functor `F`, the raw span action preserves the chosen
pullback used in span composition. The comparison iso identifies the mapped
composite span with the composite of the mapped spans, and the representative
quotient law follows from the quotient API. No bundled functor, no
limit-preservation hypothesis, and no further invariance or consumer content.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v₁ u₁ v₂ u₂

namespace AlgebraicKTheory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

/-- Iso comparing the mapped composite span with the composite of mapped spans. -/
noncomputable def QuillenSpan.mapSpanCompIso (F : C ⥤ D) [F.Additive] [F.IsExact]
    {X Y Z : C} (S₁ : QuillenSpan X Y) (S₂ : QuillenSpan Y Z) :
    QuillenSpan.map F (Span.comp S₁ S₂) ≅
      Span.comp (QuillenSpan.map F S₁) (QuillenSpan.map F S₂) := by
  have hpb_source : IsPullback (pullback.fst S₁.r S₂.l)
      (pullback.snd S₁.r S₂.l) S₁.r S₂.l :=
    IsPullback.of_hasPullback _ _
  have hMappedIsPullback : IsPullback (F.map (pullback.fst S₁.r S₂.l))
      (F.map (pullback.snd S₁.r S₂.l)) (F.map S₁.r) (F.map S₂.l) :=
    F.map_isPullback_of_isAdmissibleMono_of_isAdmissibleEpi
      hpb_source S₁.wr S₂.wl
  haveI : HasPullback (F.map S₂.l) (F.map S₁.r) :=
    hasPullback_ofHasPullbacksAgainst
      (P := admissibleEpisOf D IsAdmissibleExact)
      (P' := admissibleMonosOf D IsAdmissibleExact)
      (f := F.map S₂.l) (g := F.map S₁.r)
      (QuillenSpan.map F S₂).wl (QuillenSpan.map F S₁).wr
  haveI : HasPullback (F.map S₁.r) (F.map S₂.l) :=
    hasPullback_symmetry _ _
  have hTarget : IsPullback (pullback.fst (F.map S₁.r) (F.map S₂.l))
      (pullback.snd (F.map S₁.r) (F.map S₂.l)) (F.map S₁.r) (F.map S₂.l) :=
    IsPullback.of_hasPullback _ _
  let e : F.obj (pullback S₁.r S₂.l) ≅ pullback (F.map S₁.r) (F.map S₂.l) :=
    hMappedIsPullback.isoIsPullback _ _ hTarget
  have he_fst : e.hom ≫ pullback.fst (F.map S₁.r) (F.map S₂.l) =
      F.map (pullback.fst S₁.r S₂.l) := by
    change (hMappedIsPullback.isoIsPullback _ _ hTarget).hom ≫
      pullback.fst (F.map S₁.r) (F.map S₂.l) = F.map (pullback.fst S₁.r S₂.l)
    exact hMappedIsPullback.isoIsPullback_hom_fst _ _ hTarget
  have he_snd : e.hom ≫ pullback.snd (F.map S₁.r) (F.map S₂.l) =
      F.map (pullback.snd S₁.r S₂.l) := by
    change (hMappedIsPullback.isoIsPullback _ _ hTarget).hom ≫
      pullback.snd (F.map S₁.r) (F.map S₂.l) = F.map (pullback.snd S₁.r S₂.l)
    exact hMappedIsPullback.isoIsPullback_hom_snd _ _ hTarget
  refine Span.mkIso e ?hl ?hr
  · calc e.hom ≫ (pullback.fst (F.map S₁.r) (F.map S₂.l) ≫ F.map S₁.l)
        = (e.hom ≫ pullback.fst (F.map S₁.r) (F.map S₂.l)) ≫ F.map S₁.l := by
          rw [Category.assoc]
      _ = F.map (pullback.fst S₁.r S₂.l) ≫ F.map S₁.l := by rw [he_fst]
      _ = F.map (pullback.fst S₁.r S₂.l ≫ S₁.l) := by rw [F.map_comp]
  · calc e.hom ≫ (pullback.snd (F.map S₁.r) (F.map S₂.l) ≫ F.map S₂.r)
        = (e.hom ≫ pullback.snd (F.map S₁.r) (F.map S₂.l)) ≫ F.map S₂.r := by
          rw [Category.assoc]
      _ = F.map (pullback.snd S₁.r S₂.l) ≫ F.map S₂.r := by rw [he_snd]
      _ = F.map (pullback.snd S₁.r S₂.l ≫ S₂.r) := by rw [F.map_comp]

/-- Representative quotient law for mapped span composition. -/
theorem QuillenQ.mapSpanQuotient_comp_rep (F : C ⥤ D) [F.Additive] [F.IsExact]
    {X Y Z : QuillenQ C} (S₁ : QuillenSpan X.obj Y.obj)
    (S₂ : QuillenSpan Y.obj Z.obj) :
    QuillenQ.mapSpanQuotient F (QuillenQ.mkHom (Span.comp S₁ S₂)) =
      quillenComp (QuillenQ.mkHom (QuillenSpan.map F S₁))
        (QuillenQ.mkHom (QuillenSpan.map F S₂)) := by
  rw [QuillenQ.mapSpanQuotient_mk, mkHom_comp]
  exact QuillenQ.mkHom_sound (QuillenSpan.mapSpanCompIso F S₁ S₂)

end AlgebraicKTheory
