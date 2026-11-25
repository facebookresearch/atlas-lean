/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.KTheory.Exact.Quillen.UnderlyingIso

/-!
# Naturality of Quillen spans under endpoint isomorphisms

An isomorphism between the apices of two admissible spans, compatible with
isomorphisms of both endpoints, gives the expected naturality square in the
Quillen Q-construction.  The proof compares the two pullback-composite span
representatives through explicit intermediate spans.

This file contains no Stage grid, representative choice, all-degree lift,
nerve, realization, or Q/S comparison construction.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- Compatible isomorphisms of the source, target, and apex of two admissible
spans give a naturality square between their Quillen morphisms. -/
theorem QuillenQ.mkHom_naturality_of_span_iso
    {X X' Y Y' : C}
    (S : QuillenSpan X Y) (T : QuillenSpan X' Y')
    (eX : X ≅ X') (eY : Y ≅ Y') (eA : S.apex ≅ T.apex)
    (hl : eA.hom ≫ T.l = S.l ≫ eX.hom)
    (hr : eA.hom ≫ T.r = S.r ≫ eY.hom) :
    QuillenQ.mkHom S ≫ (QuillenQ.underlyingIso eY).hom =
      (QuillenQ.underlyingIso eX).hom ≫ QuillenQ.mkHom T := by
  have : HasPullback (QuillenQ.underlyingIsoFwdSpan eY).l S.r :=
    hasPullback_ofHasPullbacksAgainst
      (P := admissibleEpisOf C IsAdmissibleExact)
      (P' := admissibleMonosOf C IsAdmissibleExact)
      (QuillenQ.underlyingIsoFwdSpan eY).wl S.wr
  have : HasPullback S.r (QuillenQ.underlyingIsoFwdSpan eY).l :=
    hasPullback_symmetry _ _
  have : HasPullback T.l (QuillenQ.underlyingIsoFwdSpan eX).r :=
    hasPullback_ofHasPullbacksAgainst
      (P := admissibleEpisOf C IsAdmissibleExact)
      (P' := admissibleMonosOf C IsAdmissibleExact)
      T.wl (QuillenQ.underlyingIsoFwdSpan eX).wr
  have : HasPullback (QuillenQ.underlyingIsoFwdSpan eX).r T.l :=
    hasPullback_symmetry _ _
  let Amid : QuillenSpan X Y' :=
    { apex := S.apex
      l := S.l
      r := S.r ≫ eY.hom
      wl := S.wl
      wr := admissibleMono_comp.comp_mem _ _ S.wr
        (IsAdmissibleMono.of_isIso _) }
  let Bmid : QuillenSpan X Y' :=
    { apex := T.apex
      l := T.l ≫ eX.inv
      r := T.r
      wl := admissibleEpi_comp.comp_mem _ _ T.wl
        (IsAdmissibleEpi.of_isIso _)
      wr := T.wr }
  have hLeftPullback :
      pullback.snd S.r (QuillenQ.underlyingIsoFwdSpan eY).l =
        pullback.fst S.r (QuillenQ.underlyingIsoFwdSpan eY).l ≫ S.r := by
    simpa using (pullback.condition
      (f := S.r) (g := (QuillenQ.underlyingIsoFwdSpan eY).l)).symm
  have hA_iso :
      Span.comp S (QuillenQ.underlyingIsoFwdSpan eY) ≅ Amid := by
    have : IsIso (QuillenQ.underlyingIsoFwdSpan eY).l := by
      change IsIso (𝟙 Y)
      infer_instance
    let p := pullback.fst S.r (QuillenQ.underlyingIsoFwdSpan eY).l
    have hp : IsIso p := by infer_instance
    refine Span.mkIso (@asIso _ _ _ _ p hp) ?_ ?_
    · change p ≫ S.l = p ≫ S.l
      rfl
    · change p ≫ (S.r ≫ eY.hom) =
        pullback.snd S.r
            (QuillenQ.underlyingIsoFwdSpan eY).l ≫ eY.hom
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun f ↦ f ≫ eY.hom) hLeftPullback.symm)
  have hB_iso :
      Span.comp (QuillenQ.underlyingIsoFwdSpan eX) T ≅ Bmid := by
    have : IsIso (QuillenQ.underlyingIsoFwdSpan eX).r := by
      change IsIso eX.hom
      infer_instance
    let p := pullback.snd (QuillenQ.underlyingIsoFwdSpan eX).r T.l
    have hp : IsIso p := by infer_instance
    refine Span.mkIso (@asIso _ _ _ _ p hp) ?_ ?_
    · change p ≫ (T.l ≫ eX.inv) =
        pullback.fst (QuillenQ.underlyingIsoFwdSpan eX).r T.l ≫ 𝟙 X
      have hCondition :
          pullback.fst (QuillenQ.underlyingIsoFwdSpan eX).r T.l ≫ eX.hom =
            pullback.snd (QuillenQ.underlyingIsoFwdSpan eX).r T.l ≫ T.l :=
        pullback.condition
      rw [← Category.assoc, ← hCondition, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    · change p ≫ T.r = p ≫ T.r
      rfl
  have hMid_iso : Amid ≅ Bmid := by
    refine Span.mkIso eA ?_ ?_
    · change eA.hom ≫ (T.l ≫ eX.inv) = S.l
      rw [← Category.assoc, hl, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    · exact hr
  have hCompIso :
      Span.comp S (QuillenQ.underlyingIsoFwdSpan eY) ≅
        Span.comp (QuillenQ.underlyingIsoFwdSpan eX) T :=
    hA_iso.trans (hMid_iso.trans hB_iso.symm)
  rw [QuillenQ.underlyingIso_hom, QuillenQ.underlyingIso_hom]
  change quillenComp (QuillenQ.mkHom S)
      (QuillenQ.mkHom (QuillenQ.underlyingIsoFwdSpan eY)) =
    quillenComp
      (QuillenQ.mkHom (QuillenQ.underlyingIsoFwdSpan eX))
      (QuillenQ.mkHom T)
  rw [mkHom_comp, mkHom_comp]
  exact QuillenQ.mkHom_sound hCompIso

end AlgebraicKTheory

end
