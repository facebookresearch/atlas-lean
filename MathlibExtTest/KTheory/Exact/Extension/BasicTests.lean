/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Exact.Extension.Basic

/-!
# Ordinary clients of actual extension quotient diagrams

The object and hom universes are independent. The normalized first leg
points from the target kernel to the source kernel; the second points from
the source middle object to the target middle object.
-/

open CategoryTheory CategoryTheory.ExactCategory AlgebraicKTheory

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [Limits.HasZeroObject C] [Limits.HasBinaryBiproducts C] [ExactCategory C]

set_option pp.universes true in
#check @ExtensionCategory
set_option pp.universes true in
#check @ExtensionDiagram
set_option pp.universes true in
#check @ExtensionDiagram.normalize

example (E' E : ExtensionCategory C) (d : ExtensionDiagram E' E) :
    E'.subdivisionObj ⟶ E.subdivisionObj := d.normalize

example (E' E : ExtensionCategory C) (d : ExtensionDiagram E' E) :
    (d.normalize.hom.1.unop).hom = d.alpha := d.normalize_alpha

example (E' E : ExtensionCategory C) (d : ExtensionDiagram E' E) :
    d.normalize.hom.2.hom = d.beta := d.normalize_beta

example (E' E : ExtensionCategory C) (w : E'.subdivisionObj ⟶ E.subdivisionObj) :
    (ExtensionDiagram.ofNormalization w).normalize = w :=
  ExtensionDiagram.normalize_ofNormalization w

example (E' E : ExtensionCategory C) (d e : ExtensionDiagram E' E) :
    ExtensionCategory.mkHom d = ExtensionCategory.mkHom e ↔ ExtensionDiagram.Rel d e :=
  ExtensionCategory.mkHom_eq_iff d e

example (E' E : ExtensionCategory C) (d e : ExtensionDiagram E' E)
    (ha : d.alpha = e.alpha) (hb : d.beta = e.beta) :
    ExtensionCategory.mkHom d = ExtensionCategory.mkHom e := by
  exact (ExtensionCategory.mkHom_eq_iff d e).mpr (ExtensionDiagram.rel_of_components_eq ha hb)

example (E F G : ExtensionCategory C) (d : ExtensionDiagram E F) (e : ExtensionDiagram F G) :
    (ExtensionCategory.homNormalization
      ((ExtensionCategory.mkHom d : E ⟶ F) ≫ (ExtensionCategory.mkHom e : F ⟶ G))).hom.1.unop.hom =
        e.alpha ≫ d.alpha := ExtensionCategory.comp_alpha d e

example (E F G : ExtensionCategory C) (d : ExtensionDiagram E F) (e : ExtensionDiagram F G) :
    (ExtensionCategory.homNormalization
      ((ExtensionCategory.mkHom d : E ⟶ F) ≫ (ExtensionCategory.mkHom e : F ⟶ G))).hom.2.hom =
        d.beta ≫ e.beta := ExtensionCategory.comp_beta d e

example (x : AdmissibleMonoSubdivision (C := C)) :
    (ExtensionCategory.normalizationEquivalence (C := C)).inverse.obj x =
      ExtensionCategory.fromSubdivisionObj x :=
  ExtensionCategory.normalizationEquivalence_inverse_obj x

example (x : AdmissibleMonoSubdivision (C := C)) :
    (ExtensionCategory.fromSubdivisionObj x).row.X₁ = (Opposite.unop x.obj.1).obj ∧
    (ExtensionCategory.fromSubdivisionObj x).row.X₂ = x.obj.2.obj ∧
    (ExtensionCategory.fromSubdivisionObj x).row.X₃ =
      CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlag.admissibleMonoQuotient
        x.val.hom x.val.property :=
  ⟨ExtensionCategory.fromSubdivisionObj_source x, ExtensionCategory.fromSubdivisionObj_middle x,
    ExtensionCategory.fromSubdivisionObj_quotient x⟩

example (E : ExtensionCategory C) :
    (ExtensionCategory.normalizationEquivalence (C := C)).unitIso.app E =
      ExtensionCategory.normalizationUnitApp E :=
  ExtensionCategory.normalizationEquivalence_unit_app E

example (x : AdmissibleMonoSubdivision (C := C)) :
    (ExtensionCategory.normalizationEquivalence (C := C)).counitIso.app x =
      ExtensionCategory.normalizationCounitApp x :=
  ExtensionCategory.normalizationEquivalence_counit_app x

example (E : ExtensionCategory C) :
    (ExtensionCategory.normalizationUnitApp E).hom =
      ExtensionCategory.mkHom (ExtensionCategory.normalizationUnitDiagram E) :=
  ExtensionCategory.normalizationUnit_hom_mkHom E

example (E : ExtensionCategory C) :
    (ExtensionCategory.normalizationUnitDiagram E).D = E.row.X₃ ∧
      (ExtensionCategory.normalizationUnitDiagram E).q = E.row.g ∧
      (ExtensionCategory.normalizationUnitDiagram E).lambda = 𝟙 E.row.X₃ ∧
      (ExtensionCategory.normalizationUnitDiagram E).mu = (ExtensionCategory.quotientIso E).inv :=
  ⟨rfl, rfl, rfl, rfl⟩

example (E : ExtensionCategory C) :
    CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlag.admissibleMonoQuotientπ
        E.row.f (isAdmissibleMono_f E.admissible) ≫
      (ExtensionCategory.quotientIso E).hom = E.row.g :=
  ExtensionCategory.quotientIso_projection E

example (E : ExtensionCategory C) :
    (ExtensionCategory.normalization (C := C)).map
        ((ExtensionCategory.normalizationEquivalence (C := C)).unitIso.app E).hom ≫
      ((ExtensionCategory.normalizationEquivalence (C := C)).counitIso.app
        ((ExtensionCategory.normalization (C := C)).obj E)).hom = 𝟙 _ :=
  (ExtensionCategory.normalizationEquivalence (C := C)).functor_unitIso_comp E

example (E : ExtensionCategory C) :
    (ExtensionCategory.normalizationUnitApp E).hom ≫ (ExtensionCategory.normalizationUnitApp E).inv =
      𝟙 E := (ExtensionCategory.normalizationUnitApp E).hom_inv_id

example (x : AdmissibleMonoSubdivision (C := C)) :
    (ExtensionCategory.normalizationCounitApp x).inv ≫
        (ExtensionCategory.normalizationCounitApp x).hom = 𝟙 x :=
  (ExtensionCategory.normalizationCounitApp x).inv_hom_id
