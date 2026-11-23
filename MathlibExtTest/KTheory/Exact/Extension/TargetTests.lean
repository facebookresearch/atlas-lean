/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Exact.Extension.Target

/-!
# Ordinary clients of the given-quotient extension target

These clients retain independent object and morphism universes. The unit
comparison uses the actual given quotient as its raw apex and an explicit
isomorphism to the selected quotient in the inverse Quillen span.
-/

open CategoryTheory CategoryTheory.ExactCategory AlgebraicKTheory

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [Limits.HasZeroObject C] [Limits.HasBinaryBiproducts C] [ExactCategory C]

example (E : ExtensionCategory C) :
    (ExtensionCategory.target (C := C)).obj E = (⟨E.row.X₃⟩ : QuillenQ C) :=
  ExtensionCategory.target_obj E

example (E : ExtensionCategory C) :
    QuillenQ.get ((ExtensionCategory.target (C := C)).obj E) = E.row.X₃ := rfl

example (E' E : ExtensionCategory C) (d : ExtensionDiagram E' E) :
    d.toQuillenSpan.apex = d.D ∧ d.toQuillenSpan.l = d.lambda ∧
      d.toQuillenSpan.r = d.mu :=
  ⟨d.toQuillenSpan_apex, d.toQuillenSpan_l, d.toQuillenSpan_r⟩

example (E' E : ExtensionCategory C) (d : ExtensionDiagram E' E) :
    (ExtensionCategory.target (C := C)).map (ExtensionCategory.mkHom d) =
      QuillenQ.mkHom
        (X := (⟨E'.row.X₃⟩ : QuillenQ C)) (Y := (⟨E.row.X₃⟩ : QuillenQ C))
        { apex := d.D, l := d.lambda, r := d.mu,
          wl := d.lambda_admissible, wr := d.mu_admissible } :=
  ExtensionCategory.target_map_mkHom d

example (E' E : ExtensionCategory C) (f : E' ⟶ E) :
    (ExtensionCategory.target (C := C)).map f =
      (QuillenQ.underlyingIso (ExtensionCategory.quotientIso E')).inv ≫
        (ExtensionCategory.normalization ⋙ admissibleMonoSubdivisionQuillenFunctor).map f ≫
        (QuillenQ.underlyingIso (ExtensionCategory.quotientIso E)).hom :=
  ExtensionCategory.target_map f

example (E : ExtensionCategory C) :
    (ExtensionCategory.targetNormalizationIso (C := C)).app E =
      QuillenQ.underlyingIso (ExtensionCategory.quotientIso E) :=
  ExtensionCategory.targetNormalizationIso_app E

example (E' E : ExtensionCategory C) (f : E' ⟶ E) :
    (ExtensionCategory.normalization ⋙ admissibleMonoSubdivisionQuillenFunctor).map f ≫
        ((ExtensionCategory.targetNormalizationIso (C := C)).app E).hom =
      ((ExtensionCategory.targetNormalizationIso (C := C)).app E').hom ≫
        (ExtensionCategory.target (C := C)).map f :=
  (ExtensionCategory.targetNormalizationIso (C := C)).hom.naturality f

example (E : ExtensionCategory C) :
    (ExtensionCategory.target (C := C)).map (𝟙 E) = 𝟙 _ :=
  (ExtensionCategory.target (C := C)).map_id E

example (E F G : ExtensionCategory C) (d : ExtensionDiagram E F) (e : ExtensionDiagram F G) :
    (ExtensionCategory.target (C := C)).map
        (ExtensionCategory.mkHom (ExtensionDiagram.ofNormalization (d.normalize ≫ e.normalize))) =
      QuillenQ.mkHom (X := (⟨E.row.X₃⟩ : QuillenQ C))
          (Y := (⟨F.row.X₃⟩ : QuillenQ C)) d.toQuillenSpan ≫
        QuillenQ.mkHom (X := (⟨F.row.X₃⟩ : QuillenQ C))
          (Y := (⟨G.row.X₃⟩ : QuillenQ C)) e.toQuillenSpan := by
  rw [← ExtensionCategory.mkHom_comp, Functor.map_comp,
    ExtensionCategory.target_map_mkHom, ExtensionCategory.target_map_mkHom]
  rfl

example (E' E : ExtensionCategory C) (d e : ExtensionDiagram E' E)
    (h : ExtensionDiagram.Rel d e) :
    QuillenQ.mkHom (X := (⟨E'.row.X₃⟩ : QuillenQ C))
        (Y := (⟨E.row.X₃⟩ : QuillenQ C)) d.toQuillenSpan =
      QuillenQ.mkHom (X := (⟨E'.row.X₃⟩ : QuillenQ C))
        (Y := (⟨E.row.X₃⟩ : QuillenQ C)) e.toQuillenSpan := by
  calc
    _ = (ExtensionCategory.target (C := C)).map (ExtensionCategory.mkHom d) :=
      (ExtensionCategory.target_map_mkHom d).symm
    _ = (ExtensionCategory.target (C := C)).map (ExtensionCategory.mkHom e) :=
      congrArg ((ExtensionCategory.target (C := C)).map)
        ((ExtensionCategory.mkHom_eq_iff d e).mpr h)
    _ = _ := ExtensionCategory.target_map_mkHom e

example (E : ExtensionCategory C) :
    (ExtensionCategory.target (C := C)).map (ExtensionCategory.normalizationUnitApp E).hom =
      (QuillenQ.underlyingIso (ExtensionCategory.quotientIso E)).inv := by
  rw [ExtensionCategory.normalizationUnit_hom_mkHom,
    ExtensionCategory.target_map_mkHom, QuillenQ.underlyingIso_inv]
  apply QuillenQ.mkHom_sound
  refine Span.mkIso (ExtensionCategory.quotientIso E).symm ?_ ?_
  · change (ExtensionCategory.quotientIso E).inv ≫
        (ExtensionCategory.quotientIso E).hom = 𝟙 _
    exact (ExtensionCategory.quotientIso E).inv_hom_id
  · change (ExtensionCategory.quotientIso E).inv ≫ 𝟙 _ =
        (ExtensionCategory.quotientIso E).inv
    exact Category.comp_id _
