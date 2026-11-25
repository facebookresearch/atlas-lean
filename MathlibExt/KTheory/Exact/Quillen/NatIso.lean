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

public import MathlibExt.KTheory.Exact.Quillen.UnderlyingIso

/-!
# Natural-isomorphism transport for Quillen-Q maps

For a natural isomorphism `e : F ≅ G` between additive exact functors,
`QuillenQ.map F ≅ QuillenQ.map G` is assembled via `NatIso.ofComponents`
with components reusing `QuillenQ.underlyingIso`.
The explicit span-comparison construction is retained only for naturality,
which uses quotient induction with a span isomorphism from `e.hom.naturality`
and pullback comparison patterns.
No equivalence constructor, G-theory edit, test, root, nerve,
realization, Q/S comparison, S-construction, spectrum, or BGT content.
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

/-- Natural-isomorphism transport for bundled Quillen-Q maps. -/
noncomputable def QuillenQ.mapNatIso (F G : C ⥤ D) [F.Additive]
    [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    QuillenQ.map F ≅ QuillenQ.map G :=
  NatIso.ofComponents
    (fun X => QuillenQ.underlyingIso (e.app X.obj))
    (fun {X Y : QuillenQ C} (f : X ⟶ Y) => by
      change
          quillenComp (QuillenQ.mapSpanQuotient F f)
            ((QuillenQ.underlyingIso (e.app Y.obj)).hom) =
          quillenComp ((QuillenQ.underlyingIso (e.app X.obj)).hom)
            (QuillenQ.mapSpanQuotient G f)
      simp only [QuillenQ.underlyingIso_hom]
      refine Quotient.inductionOn f ?_
      intro S
      have : HasPullback (QuillenQ.underlyingIsoFwdSpan (e.app Y.obj)).l
          (QuillenSpan.map F S).r :=
        hasPullback_ofHasPullbacksAgainst
          (P := admissibleEpisOf D IsAdmissibleExact)
          (P' := admissibleMonosOf D IsAdmissibleExact)
          (QuillenQ.underlyingIsoFwdSpan (e.app Y.obj)).wl
          (QuillenSpan.map F S).wr
      have : HasPullback (QuillenSpan.map F S).r
          (QuillenQ.underlyingIsoFwdSpan (e.app Y.obj)).l :=
        hasPullback_symmetry _ _
      have : HasPullback (QuillenSpan.map G S).l
          (QuillenQ.underlyingIsoFwdSpan (e.app X.obj)).r :=
        hasPullback_ofHasPullbacksAgainst
          (P := admissibleEpisOf D IsAdmissibleExact)
          (P' := admissibleMonosOf D IsAdmissibleExact)
          (QuillenSpan.map G S).wl
          (QuillenQ.underlyingIsoFwdSpan (e.app X.obj)).wr
      have : HasPullback (QuillenQ.underlyingIsoFwdSpan (e.app X.obj)).r
          (QuillenSpan.map G S).l :=
        hasPullback_symmetry _ _
      have h_nat_l :
          F.map S.l ≫ e.hom.app X.obj =
            e.hom.app S.apex ≫ G.map S.l :=
        e.hom.naturality S.l
      have h_nat_r :
          F.map S.r ≫ e.hom.app Y.obj =
            e.hom.app S.apex ≫ G.map S.r :=
        e.hom.naturality S.r
      have hPA_eq :
          pullback.snd (QuillenSpan.map F S).r
              (QuillenQ.underlyingIsoFwdSpan (e.app Y.obj)).l =
            pullback.fst (QuillenSpan.map F S).r
                (QuillenQ.underlyingIsoFwdSpan (e.app Y.obj)).l ≫
              F.map S.r := by
        simpa using (pullback.condition
          (f := (QuillenSpan.map F S).r)
          (g := (QuillenQ.underlyingIsoFwdSpan (e.app Y.obj)).l)).symm
      let Amid : QuillenSpan (F.obj X.obj) (G.obj Y.obj) :=
        { apex := F.obj S.apex
          l := F.map S.l
          r := F.map S.r ≫ e.hom.app Y.obj
          wl := (QuillenSpan.map F S).wl
          wr := admissibleMono_comp.comp_mem _ _
            (QuillenSpan.map F S).wr
            (IsAdmissibleMono.of_isIso _) };
      let Bmid : QuillenSpan (F.obj X.obj) (G.obj Y.obj) :=
        { apex := G.obj S.apex
          l := G.map S.l ≫ (e.symm).hom.app X.obj
          r := G.map S.r
          wl := admissibleEpi_comp.comp_mem _ _
            (QuillenSpan.map G S).wl
            (IsAdmissibleEpi.of_isIso _)
          wr := (QuillenSpan.map G S).wr };
      have hA_iso :
          Span.comp (QuillenSpan.map F S)
              (QuillenQ.underlyingIsoFwdSpan (e.app Y.obj)) ≅ Amid := by
        have : IsIso (QuillenQ.underlyingIsoFwdSpan (e.app Y.obj)).l := by
          change IsIso (𝟙 _)
          infer_instance
        let p := pullback.fst (QuillenSpan.map F S).r
          (QuillenQ.underlyingIsoFwdSpan (e.app Y.obj)).l
        have hFstA_iso : IsIso p := by
          infer_instance
        refine Span.mkIso
          (@asIso _ _ _ _ p hFstA_iso) ?_ ?_
        · change p ≫ F.map S.l =
            p ≫ F.map S.l
          rfl
        · change p ≫ (F.map S.r ≫ e.hom.app Y.obj) =
            pullback.snd (QuillenSpan.map F S).r
              (QuillenQ.underlyingIsoFwdSpan (e.app Y.obj)).l ≫ e.hom.app Y.obj
          change pullback.fst (QuillenSpan.map F S).r
              (QuillenQ.underlyingIsoFwdSpan (e.app Y.obj)).l ≫
              (F.map S.r ≫ e.hom.app Y.obj) =
            pullback.snd (QuillenSpan.map F S).r
              (QuillenQ.underlyingIsoFwdSpan (e.app Y.obj)).l ≫ e.hom.app Y.obj
          exact (Category.assoc _ _ _).symm.trans
            (congrArg (fun x => x ≫ e.hom.app Y.obj) hPA_eq.symm)
      have hB_iso :
          Span.comp (QuillenQ.underlyingIsoFwdSpan (e.app X.obj))
              (QuillenSpan.map G S) ≅ Bmid := by
        have : IsIso (QuillenQ.underlyingIsoFwdSpan (e.app X.obj)).r := by
          change IsIso ((e.app X.obj).hom)
          infer_instance
        let p := pullback.snd
          (QuillenQ.underlyingIsoFwdSpan (e.app X.obj)).r
          (QuillenSpan.map G S).l
        have hSndB_iso : IsIso p := by
          infer_instance
        refine Span.mkIso
          (@asIso _ _ _ _ p hSndB_iso) ?_ ?_
        · change p ≫
                ((QuillenSpan.map G S).l ≫ (e.app X.obj).inv) =
              pullback.fst
                (QuillenQ.underlyingIsoFwdSpan (e.app X.obj)).r
                (QuillenSpan.map G S).l ≫
                (QuillenQ.underlyingIsoFwdSpan (e.app X.obj)).l
          have h_cond : pullback.fst
                (QuillenQ.underlyingIsoFwdSpan (e.app X.obj)).r
                (QuillenSpan.map G S).l ≫
                (QuillenQ.underlyingIsoFwdSpan (e.app X.obj)).r =
              pullback.snd
                (QuillenQ.underlyingIsoFwdSpan (e.app X.obj)).r
                (QuillenSpan.map G S).l ≫ (QuillenSpan.map G S).l :=
            pullback.condition
          rw [← Category.assoc, ← h_cond, Category.assoc, Iso.hom_inv_id,
            Category.comp_id]
        · change p ≫ G.map S.r =
            p ≫ G.map S.r
          rfl
      have hMid_iso : Amid ≅ Bmid := by
        have h_cancel : e.hom.app X.obj ≫ (e.app X.obj).inv = 𝟙 (F.obj X.obj) := by
          change (e.app X.obj).hom ≫ (e.app X.obj).inv = 𝟙 _
          exact Iso.hom_inv_id _
        refine Span.mkIso (e.app S.apex) ?_ ?_
        · change e.hom.app S.apex ≫ (G.map S.l ≫ (e.app X.obj).inv) = F.map S.l
          rw [← Category.assoc, ← h_nat_l, Category.assoc, h_cancel, Category.comp_id]
        · change e.hom.app S.apex ≫ G.map S.r = F.map S.r ≫ e.hom.app Y.obj
          exact h_nat_r.symm
      have h_comp_iso :
          Span.comp (QuillenSpan.map F S)
              (QuillenQ.underlyingIsoFwdSpan (e.app Y.obj)) ≅
            Span.comp (QuillenQ.underlyingIsoFwdSpan (e.app X.obj))
              (QuillenSpan.map G S) :=
        hA_iso.trans (hMid_iso.trans hB_iso.symm)
      change quillenComp (QuillenQ.mkHom (QuillenSpan.map F S))
          (QuillenQ.mkHom
            (QuillenQ.underlyingIsoFwdSpan (e.app Y.obj))) =
        quillenComp (QuillenQ.mkHom
            (QuillenQ.underlyingIsoFwdSpan (e.app X.obj)))
          (QuillenQ.mkHom (QuillenSpan.map G S))
      rw [mkHom_comp, mkHom_comp]
      exact QuillenQ.mkHom_sound h_comp_iso)

end AlgebraicKTheory
