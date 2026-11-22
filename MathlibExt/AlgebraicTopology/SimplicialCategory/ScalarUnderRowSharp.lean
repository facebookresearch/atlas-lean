/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarUnderRowCoefficients
import MathlibExt.AlgebraicTopology.SimplicialSet.IndexedFamilyProjectionSharp

/-!
# Sharpness of the SAME full original scalar-under rows

The complete original row coefficient is the literal native pullback
of its original full indexed Hom family by the base word's first
original object. Both whole pullback projections and all coefficient
values are retained. The proved family sharpness gives actual row
sharpness, with no Kan or groupoid premise on the original enrichment.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.ScalarUnderCategory

variable (C : CategoryTheory.SimplicialEnrichment.Carrier.{u})

/-- The first original object of the SAME complete base word, constant
under every original scalar operator. -/
def rowFirstObject (n : ℕ) : baseRow C n ⟶ IndexedFamilyProjection.base (C : Type u) where
  app _ := ↾fun w => (w.obj 0).obj
  naturality _ _ _ := rfl

/-- The SAME full original indexed Hom family at the supplied source. -/
abbrev rowHomFamily (z : C) := IndexedSums.object (fun x : C => z ⟶[SSet.{u}] x)

/-- Preserve the original first-object label and its entire original initial Hom coefficient. -/
def rowCoefficientsFamilyMap (z : C) (n : ℕ) : rowCoefficients C z n ⟶ rowHomFamily C z where
  app _ := ↾fun a => ⟨(a.1.obj 0).obj, a.2⟩
  naturality _ _ _ := rfl

/-- The SAME full original row coefficient comparison into the native family pullback. -/
def rowCoefficientsToFamilyPullback (z : C) (n : ℕ) :
    rowCoefficients C z n ⟶ pullback
      (IndexedFamilyProjection.projection (fun x : C => z ⟶[SSet.{u}] x)) (rowFirstObject C n) :=
  pullback.lift (rowCoefficientsFamilyMap C z n) (rowCoefficientsProjection C z n) rfl

/-- Its first projection keeps the SAME original first label and whole Hom coefficient. -/
@[reassoc]
lemma rowCoefficientsToFamilyPullback_fst (z : C) (n : ℕ) :
    rowCoefficientsToFamilyPullback C z n ≫ pullback.fst _ _ = rowCoefficientsFamilyMap C z n :=
  pullback.lift_fst _ _ _

/-- Its second projection keeps the SAME entire original base word. -/
@[reassoc]
lemma rowCoefficientsToFamilyPullback_snd (z : C) (n : ℕ) :
    rowCoefficientsToFamilyPullback C z n ≫ pullback.snd _ _ = rowCoefficientsProjection C z n :=
  pullback.lift_snd _ _ _

/-- The full original row comparison is an actual Iso, retaining every
base word and complete coefficient in every original scalar degree. -/
instance rowCoefficientsToFamilyPullback_isIso (z : C) (n : ℕ) :
    IsIso (rowCoefficientsToFamilyPullback C z n) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro q
  rw [isIso_iff_bijective]
  let H : C → SSet.{u} := fun x => z ⟶[SSet.{u}] x
  let P := IndexedFamilyProjection.projection H
  let b := rowFirstObject C n
  let E := (CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type u)).obj q
  have hpb := (IsPullback.of_hasPullback P b).map E
  have hfst := congrArg (fun f => f.app q) (rowCoefficientsToFamilyPullback_fst C z n)
  have hsnd := congrArg (fun f => f.app q) (rowCoefficientsToFamilyPullback_snd C z n)
  constructor
  · intro a a' haa
    apply Sigma.ext
    · exact (congr($(hsnd) a)).symm.trans
        ((congrArg (fun t => (pullback.snd P b).app q t) haa).trans (congr($(hsnd) a')))
    · have hh : (⟨(a.1.obj 0).obj, a.2⟩ : Σ x : C, (H x).obj q) = ⟨(a'.1.obj 0).obj, a'.2⟩ :=
        (congr($(hfst) a)).symm.trans
          ((congrArg (fun t => (pullback.fst P b).app q t) haa).trans (congr($(hfst) a')))
      exact (Sigma.mk.inj_iff.mp hh).2
  · intro a
    rcases hx : (pullback.fst P b).app q a with ⟨x, h⟩
    let w := (pullback.snd P b).app q a
    have he : x = (w.obj 0).obj := by
      have hp := congr($(pullback.condition (f := P) (g := b)).app q a)
      change P.app q ((pullback.fst P b).app q a) = b.app q w at hp
      rw [hx] at hp
      exact hp
    subst x
    refine ⟨⟨w, h⟩, Types.ext_of_isPullback hpb ?_ ?_⟩
    · exact (congr($(hfst) (⟨w, h⟩ : (rowCoefficients C z n).obj q))).trans hx.symm
    · exact congr($(hsnd) (⟨w, h⟩ : (rowCoefficients C z n).obj q))

/-- Both original row maps form the actual full original family pullback square. -/
theorem rowCoefficients_family_isPullback (z : C) (n : ℕ) :
    IsPullback (rowCoefficientsFamilyMap C z n) (rowCoefficientsProjection C z n)
      (IndexedFamilyProjection.projection (fun x : C => z ⟶[SSet.{u}] x)) (rowFirstObject C n) :=
  IsPullback.of_iso_pullback (CommSq.mk rfl) (asIso (rowCoefficientsToFamilyPullback C z n))
    (rowCoefficientsToFamilyPullback_fst C z n) (rowCoefficientsToFamilyPullback_snd C z n)

/-- The SAME entire original row-coefficient projection is sharp. -/
theorem rowCoefficientsProjection_sharp (z : C) (n : ℕ) :
    MorphismProperty.sharpMaps realizationWeakEquivalences (rowCoefficientsProjection C z n) :=
  MorphismProperty.of_isPullback (rowCoefficients_family_isPullback C z n)
    (IndexedFamilyProjection.projection_sharp (fun x : C => z ⟶[SSet.{u}] x))

/-- EVERY SAME full original scalar-under row is sharp, without Kan,
groupoid or nonempty-object assumptions and with all original arities. -/
theorem rowProjection_sharp (z : C) (n : ℕ) :
    MorphismProperty.sharpMaps realizationWeakEquivalences (rowProjection C z n) := by
  let e : Arrow.mk (rowCoefficientsProjection C z n) ≅ Arrow.mk (rowProjection C z n) :=
    Arrow.isoMk' _ _ (rowCoefficientsIso C z n) (Iso.refl _) (by
      change (rowCoefficientsIso C z n).hom ≫ rowProjection C z n =
        rowCoefficientsProjection C z n ≫ 𝟙 (baseRow C n)
      rw [Category.comp_id]
      exact rowCoefficientsIso_hom_projection C z n)
  exact (MorphismProperty.sharpMaps realizationWeakEquivalences).arrow_mk_iso_iff e |>.mp
    (rowCoefficientsProjection_sharp C z n)

end SSet.ScalarUnderCategory
