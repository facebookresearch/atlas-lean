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

public import MathlibExt.KTheory.Exact.Quillen.Functor

/-!
# Underlying-isomorphism lift for the Quillen Q-construction

For an isomorphism `e : X ≅ Y` in an exact category, the spans with apex `X`,
forward legs `𝟙 X` / `e.hom` and inverse legs `e.hom` / `𝟙 X`, assemble into
`(⟨X⟩ : QuillenQ C) ≅ ⟨Y⟩`. Admissibility uses identity and isomorphism lemmas;
inverse laws follow the `QuillenQ.mapNatIso` component pattern via `mkHom_comp`,
`mkHom_id`, `mkHom_sound` with explicit `Span.mkIso` comparisons.

Orientation: forward goes from `X` to `Y` through apex `X`; inverse returns
through the same apex. Later packets compose this with zero-object maps, nerve
edges, and realization paths. This file endows `QuillenQ` with no distinguished
point and proves exact-functor map compatibility, while proving no nerve,
realization, or pointed claim.
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

/-- Forward span for the underlying-iso lift (apex `X`). -/
abbrev QuillenQ.underlyingIsoFwdSpan {X Y : C} (e : X ≅ Y) : QuillenSpan X Y where
  apex := X
  l := 𝟙 X
  r := e.hom
  wl := IsAdmissibleEpi.id X
  wr := IsAdmissibleMono.of_isIso e.hom

/-- Inverse span for the underlying-iso lift (apex `X`). -/
abbrev QuillenQ.underlyingIsoInvSpan {X Y : C} (e : X ≅ Y) : QuillenSpan Y X where
  apex := X
  l := e.hom
  r := 𝟙 X
  wl := IsAdmissibleEpi.of_isIso e.hom
  wr := IsAdmissibleMono.id X

/-- Reusable lift of an underlying isomorphism to `QuillenQ`. -/
noncomputable def QuillenQ.underlyingIso {X Y : C} (e : X ≅ Y) :
    (⟨X⟩ : QuillenQ C) ≅ ⟨Y⟩ where
  hom := QuillenQ.mkHom (underlyingIsoFwdSpan e)
  inv := QuillenQ.mkHom (underlyingIsoInvSpan e)
  hom_inv_id := by
    change quillenComp (QuillenQ.mkHom (underlyingIsoFwdSpan e))
      (QuillenQ.mkHom (underlyingIsoInvSpan e)) = 𝟙 (⟨X⟩ : QuillenQ C)
    have : HasPullback (underlyingIsoInvSpan e).l (underlyingIsoFwdSpan e).r :=
      hasPullback_ofHasPullbacksAgainst
        (P := admissibleEpisOf C IsAdmissibleExact)
        (P' := admissibleMonosOf C IsAdmissibleExact)
        (underlyingIsoInvSpan e).wl (underlyingIsoFwdSpan e).wr
    have : HasPullback (underlyingIsoFwdSpan e).r (underlyingIsoInvSpan e).l :=
      hasPullback_symmetry _ _
    have h_eq :
        pullback.fst (underlyingIsoFwdSpan e).r (underlyingIsoInvSpan e).l =
          pullback.snd (underlyingIsoFwdSpan e).r (underlyingIsoInvSpan e).l :=
      (cancel_mono (underlyingIsoFwdSpan e).r).mp pullback.condition
    rw [mkHom_comp, ← mkHom_id]
    apply QuillenQ.mkHom_sound
    have : IsIso (underlyingIsoFwdSpan e).r := by
      change IsIso e.hom
      infer_instance
    have : IsIso (underlyingIsoInvSpan e).l := by
      change IsIso e.hom
      infer_instance
    let p := pullback.fst (underlyingIsoFwdSpan e).r (underlyingIsoInvSpan e).l
    have hFst_iso : IsIso p := by
      infer_instance
    refine Span.mkIso (@asIso _ _ _ _ p hFst_iso) ?_ ?_
    · change p ≫ 𝟙 _ = p ≫ 𝟙 _
      rfl
    · change p ≫ 𝟙 _ =
        pullback.snd (underlyingIsoFwdSpan e).r (underlyingIsoInvSpan e).l ≫ 𝟙 _
      change pullback.fst (underlyingIsoFwdSpan e).r (underlyingIsoInvSpan e).l ≫
          𝟙 _ =
        pullback.snd (underlyingIsoFwdSpan e).r (underlyingIsoInvSpan e).l ≫ 𝟙 _
      rw [h_eq]
  inv_hom_id := by
    change quillenComp (QuillenQ.mkHom (underlyingIsoInvSpan e))
      (QuillenQ.mkHom (underlyingIsoFwdSpan e)) = 𝟙 (⟨Y⟩ : QuillenQ C)
    have : HasPullback (underlyingIsoFwdSpan e).l (underlyingIsoInvSpan e).r :=
      hasPullback_ofHasPullbacksAgainst
        (P := admissibleEpisOf C IsAdmissibleExact)
        (P' := admissibleMonosOf C IsAdmissibleExact)
        (underlyingIsoFwdSpan e).wl (underlyingIsoInvSpan e).wr
    have : HasPullback (underlyingIsoInvSpan e).r (underlyingIsoFwdSpan e).l :=
      hasPullback_symmetry _ _
    have h_eq :
        pullback.fst (underlyingIsoInvSpan e).r (underlyingIsoFwdSpan e).l =
          pullback.snd (underlyingIsoInvSpan e).r (underlyingIsoFwdSpan e).l := by
      simpa using (pullback.condition
        (f := (underlyingIsoInvSpan e).r) (g := (underlyingIsoFwdSpan e).l))
    rw [mkHom_comp, ← mkHom_id]
    apply QuillenQ.mkHom_sound
    have : IsIso (underlyingIsoInvSpan e).l := by
      change IsIso e.hom
      infer_instance
    have : IsIso (underlyingIsoFwdSpan e).l := by
      change IsIso (𝟙 _)
      infer_instance
    have : IsIso (pullback.fst (underlyingIsoInvSpan e).r
        (underlyingIsoFwdSpan e).l) := by
      infer_instance
    let p := pullback.fst (underlyingIsoInvSpan e).r (underlyingIsoFwdSpan e).l ≫
      (underlyingIsoInvSpan e).l
    have hComp_iso : IsIso p := by
      infer_instance
    refine Span.mkIso (@asIso _ _ _ _ p hComp_iso) ?_ ?_
    · simp [p]
    · simp [p, h_eq]

/-- Representative formula for the forward direction. -/
@[simp]
theorem QuillenQ.underlyingIso_hom {X Y : C} (e : X ≅ Y) :
    (QuillenQ.underlyingIso e).hom =
      QuillenQ.mkHom (QuillenQ.underlyingIsoFwdSpan e) :=
  rfl

/-- Representative formula for the inverse direction. -/
@[simp]
theorem QuillenQ.underlyingIso_inv {X Y : C} (e : X ≅ Y) :
    (QuillenQ.underlyingIso e).inv =
      QuillenQ.mkHom (QuillenQ.underlyingIsoInvSpan e) :=
  rfl

/-- Reflexivity: the lift of `Iso.refl` is the identity isomorphism. -/
theorem QuillenQ.underlyingIso_refl (X : C) :
    QuillenQ.underlyingIso (Iso.refl X) = Iso.refl (⟨X⟩ : QuillenQ C) := by
  apply Iso.ext
  rw [QuillenQ.underlyingIso_hom]
  change QuillenQ.mkHom _ = 𝟙 (⟨X⟩ : QuillenQ C)
  rw [← mkHom_id]
  apply QuillenQ.mkHom_sound
  exact Span.mkIso (Iso.refl _)
    (by change 𝟙 X ≫ 𝟙 X = 𝟙 X; exact Category.id_comp _)
    (by change 𝟙 X ≫ 𝟙 X = 𝟙 X; exact Category.id_comp _)

/-- Transitivity: the lift preserves composition of underlying isomorphisms. -/
theorem QuillenQ.underlyingIso_trans {X Y Z : C} (e : X ≅ Y) (f : Y ≅ Z) :
    QuillenQ.underlyingIso (e.trans f) =
      (QuillenQ.underlyingIso e).trans (QuillenQ.underlyingIso f) := by
  apply Iso.ext
  change QuillenQ.mkHom (QuillenQ.underlyingIsoFwdSpan (e.trans f)) =
    quillenComp (QuillenQ.mkHom (QuillenQ.underlyingIsoFwdSpan e))
      (QuillenQ.mkHom (QuillenQ.underlyingIsoFwdSpan f))
  have hPB : HasPullback (QuillenQ.underlyingIsoFwdSpan f).l
      (QuillenQ.underlyingIsoFwdSpan e).r :=
    hasPullback_ofHasPullbacksAgainst
      (P := admissibleEpisOf C IsAdmissibleExact)
      (P' := admissibleMonosOf C IsAdmissibleExact)
      (QuillenQ.underlyingIsoFwdSpan f).wl
      (QuillenQ.underlyingIsoFwdSpan e).wr
  have hPB' : HasPullback (QuillenQ.underlyingIsoFwdSpan e).r
      (QuillenQ.underlyingIsoFwdSpan f).l :=
    hasPullback_symmetry _ _
  rw [mkHom_comp]
  apply Eq.symm
  apply QuillenQ.mkHom_sound
  have hRe : IsIso (QuillenQ.underlyingIsoFwdSpan e).r := by
    change IsIso e.hom
    infer_instance
  have hLf : IsIso (QuillenQ.underlyingIsoFwdSpan f).l := by
    change IsIso (𝟙 Y)
    infer_instance
  have hFst_iso : IsIso (pullback.fst
      (QuillenQ.underlyingIsoFwdSpan e).r
      (QuillenQ.underlyingIsoFwdSpan f).l) := by
    infer_instance
  have h_cond : pullback.fst
        (QuillenQ.underlyingIsoFwdSpan e).r
        (QuillenQ.underlyingIsoFwdSpan f).l ≫
        (QuillenQ.underlyingIsoFwdSpan e).r =
      pullback.snd
        (QuillenQ.underlyingIsoFwdSpan e).r
        (QuillenQ.underlyingIsoFwdSpan f).l ≫
        (QuillenQ.underlyingIsoFwdSpan f).l :=
    pullback.condition
  refine Span.mkIso (@asIso _ _ _ _ _ hFst_iso) ?_ ?_
  · change pullback.fst (QuillenQ.underlyingIsoFwdSpan e).r
        (QuillenQ.underlyingIsoFwdSpan f).l ≫ 𝟙 X =
      pullback.fst (QuillenQ.underlyingIsoFwdSpan e).r
        (QuillenQ.underlyingIsoFwdSpan f).l ≫ 𝟙 X
    rfl
  · change pullback.fst (QuillenQ.underlyingIsoFwdSpan e).r
        (QuillenQ.underlyingIsoFwdSpan f).l ≫
        ((QuillenQ.underlyingIsoFwdSpan e).r ≫ (QuillenQ.underlyingIsoFwdSpan f).r) =
      pullback.snd (QuillenQ.underlyingIsoFwdSpan e).r
        (QuillenQ.underlyingIsoFwdSpan f).l ≫ (QuillenQ.underlyingIsoFwdSpan f).r
    rw [← Category.assoc, h_cond, Category.comp_id]

/-- Compatibility with exact-functor maps at iso level. -/
theorem QuillenQ.underlyingIso_map (F : C ⥤ D) [F.Additive] [F.IsExact]
    {X Y : C} (e : X ≅ Y) :
    (QuillenQ.map F).mapIso (QuillenQ.underlyingIso e) =
      QuillenQ.underlyingIso (F.mapIso e) := by
  apply Iso.ext
  change (QuillenQ.map F).map (QuillenQ.underlyingIso e).hom =
    (QuillenQ.underlyingIso (F.mapIso e)).hom
  rw [QuillenQ.underlyingIso_hom, QuillenQ.map_mk, QuillenQ.underlyingIso_hom]
  apply QuillenQ.mkHom_sound
  refine Span.mkIso (Iso.refl _) ?_ ?_
  · change 𝟙 _ ≫ 𝟙 _ = F.map (𝟙 X)
    rw [Category.id_comp, F.map_id]
  · change 𝟙 _ ≫ F.map e.hom = F.map e.hom
    rw [Category.id_comp]

end AlgebraicKTheory
