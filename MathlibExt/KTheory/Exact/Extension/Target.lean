/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.Basic
public import MathlibExt.KTheory.Exact.Quillen.AdmissibleMonoSubdivisionFunctor
public import MathlibExt.KTheory.Exact.Quillen.SpanUnderlyingIsoNaturality

/-!
# The extension target with the given quotient objects

The target of an admissible exact row is its given quotient. Its maps are
the actual admissible spans of representative extension diagrams, compared
with the selected-quotient subdivision functor by cokernel uniqueness.
-/

public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.ExactCategory Limits
open CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlag

universe u v

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

namespace ExtensionDiagram

variable {E' E : ExtensionCategory C}

/-- The right column of an extension diagram, with its given middle quotient. -/
@[expose]
def toQuillenSpan (d : ExtensionDiagram E' E) : QuillenSpan E'.row.X₃ E.row.X₃ where
  apex := d.D
  l := d.lambda
  r := d.mu
  wl := d.lambda_admissible
  wr := d.mu_admissible

/-- The representative span retains the given middle quotient. -/
@[simp]
theorem toQuillenSpan_apex (d : ExtensionDiagram E' E) : d.toQuillenSpan.apex = d.D := rfl

/-- The left leg is the given admissible quotient map. -/
@[simp]
theorem toQuillenSpan_l (d : ExtensionDiagram E' E) : d.toQuillenSpan.l = d.lambda := rfl

/-- The right leg is the given admissible inclusion. -/
@[simp]
theorem toQuillenSpan_r (d : ExtensionDiagram E' E) : d.toQuillenSpan.r = d.mu := rfl

private abbrev diagramFlag (d : ExtensionDiagram E' E) :=
  admissibleMonoTripleFlag d.alpha d.alpha_admissible E'.row.f
    (isAdmissibleMono_f E'.admissible) d.beta d.beta_admissible

private theorem diagramFlag_map_one_three (d : ExtensionDiagram E' E) :
    (diagramFlag d).chain.map (homOfLE (show (1 : Fin 5) ≤ 3 by decide)) = d.j := by
  change (ComposableArrows.mk₃ d.alpha E'.row.f d.beta).map' 0 2 = d.j
  rw [ComposableArrows.map'_comp _ 0 1 2]
  exact d.j_eq.symm

private def normalizedApexIso (d : ExtensionDiagram E' E) :
    (admissibleMonoSubdivisionQuillenSpan d.normalize).apex ≅ d.D := by
  let F := diagramFlag d
  let h13 : (1 : Fin 5) ≤ 3 := by decide
  have hz : F.chain.map (homOfLE h13) ≫ d.q = 0 := by
    rw [diagramFlag_map_one_three]
    exact d.zero
  have he : IsAdmissibleExact (ShortComplex.mk (F.chain.map (homOfLE h13)) d.q hz) := by
    change IsAdmissibleExact (ShortComplex.mk (d.alpha ≫ E'.row.f) d.q _)
    simpa only [← d.j_eq] using d.admissible
  exact F.intervalIsoOfExact h13 d.q hz he

private theorem normalizedApexIso_projection (d : ExtensionDiagram E' E) :
    (diagramFlag d).intervalπ (1 : Fin 5) 3 (by decide) ≫
      (normalizedApexIso d).hom = d.q := by
  unfold normalizedApexIso
  exact (diagramFlag d).intervalπ_intervalIsoOfExact_hom
    (show (1 : Fin 5) ≤ 3 by decide) d.q _ _

private theorem normalizedSpan_left_projection (d : ExtensionDiagram E' E) :
    (diagramFlag d).intervalπ (1 : Fin 5) 3 (by decide) ≫
      (admissibleMonoSubdivisionQuillenSpan d.normalize).l ≫
      (ExtensionCategory.quotientIso E').hom = E'.row.g := by
  let F := diagramFlag d
  let h12 : (1 : Fin 5) ≤ 2 := by decide
  let h23 : (2 : Fin 5) ≤ 3 := by decide
  let h13 : (1 : Fin 5) ≤ 3 := by decide
  change F.intervalπ 1 3 h13 ≫
      ((F.intervalMap h13 h23 h12 le_rfl ≫
        (admissibleMonoTripleSourceIso d.alpha d.alpha_admissible E'.row.f
          (isAdmissibleMono_f E'.admissible) d.beta d.beta_admissible).hom) ≫ 𝟙 _) ≫
        (ExtensionCategory.quotientIso E').hom = E'.row.g
  rw [Category.comp_id, ← Category.assoc, ← Category.assoc, F.intervalπ_naturality]
  have hid : F.chain.map (homOfLE (le_rfl : (3 : Fin 5) ≤ 3)) = 𝟙 _ := by
    rw [Subsingleton.elim (homOfLE _) (𝟙 _), F.chain.map_id]
  rw [hid, Category.id_comp, admissibleMonoTripleSourceIso_projection,
    ExtensionCategory.quotientIso_projection]

private theorem normalizedSpan_right_projection (d : ExtensionDiagram E' E) :
    (diagramFlag d).intervalπ (1 : Fin 5) 3 (by decide) ≫
      (admissibleMonoSubdivisionQuillenSpan d.normalize).r ≫
      (ExtensionCategory.quotientIso E).hom = d.beta ≫ E.row.g := by
  let F := diagramFlag d
  let h13 : (1 : Fin 5) ≤ 3 := by decide
  let h14 : (1 : Fin 5) ≤ 4 := by decide
  let h34 : (3 : Fin 5) ≤ 4 := by decide
  have hcomp : (d.alpha ≫ E'.row.f) ≫ d.beta = E.row.f := by
    rw [← d.j_eq, d.j_beta]
  change F.intervalπ 1 3 h13 ≫
      ((F.intervalMap h13 h14 le_rfl h34 ≫
        (admissibleMonoTripleTargetIso d.alpha d.alpha_admissible E'.row.f
          (isAdmissibleMono_f E'.admissible) d.beta d.beta_admissible).hom) ≫
        (admissibleMonoQuotientIsoOfEq
          (admissibleMonoTriple_comp_admissible d.alpha d.alpha_admissible E'.row.f
            (isAdmissibleMono_f E'.admissible) d.beta d.beta_admissible)
          (isAdmissibleMono_f E.admissible)
          hcomp).hom) ≫
        (ExtensionCategory.quotientIso E).hom = d.beta ≫ E.row.g
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, F.intervalπ_naturality]
  have htarget : F.intervalπ 1 4 h14 ≫
      (admissibleMonoTripleTargetIso d.alpha d.alpha_admissible E'.row.f
        (isAdmissibleMono_f E'.admissible) d.beta d.beta_admissible).hom =
      𝟙 _ ≫ admissibleMonoQuotientπ ((d.alpha ≫ E'.row.f) ≫ d.beta) _ :=
    admissibleMonoTripleTargetIso_projection d.alpha d.alpha_admissible E'.row.f
      (isAdmissibleMono_f E'.admissible) d.beta d.beta_admissible
  simp only [Category.assoc]
  rw [← Category.assoc (F.intervalπ 1 4 h14), htarget]
  simp only [Category.id_comp]
  change d.beta ≫
    (admissibleMonoQuotientπ ((d.alpha ≫ E'.row.f) ≫ d.beta) _ ≫ _ ≫ _) = _
  rw [admissibleMonoQuotientπ_isoOfEq_hom_assoc,
    ExtensionCategory.quotientIso_projection]

private theorem normalizedApexIso_left (d : ExtensionDiagram E' E) :
    (normalizedApexIso d).hom ≫ d.lambda =
      (admissibleMonoSubdivisionQuillenSpan d.normalize).l ≫
        (ExtensionCategory.quotientIso E').hom := by
  let π := (diagramFlag d).intervalπ (1 : Fin 5) 3 (by decide)
  let _ : Epi π := (isAdmissibleEpi_g ((diagramFlag d).interval_exact 1 3 (by decide))).epi
  apply (cancel_epi π).1
  rw [← Category.assoc, normalizedApexIso_projection, d.q_lambda,
    normalizedSpan_left_projection]

private theorem normalizedApexIso_right (d : ExtensionDiagram E' E) :
    (normalizedApexIso d).hom ≫ d.mu =
      (admissibleMonoSubdivisionQuillenSpan d.normalize).r ≫
        (ExtensionCategory.quotientIso E).hom := by
  let π := (diagramFlag d).intervalπ (1 : Fin 5) 3 (by decide)
  let _ : Epi π := (isAdmissibleEpi_g ((diagramFlag d).interval_exact 1 3 (by decide))).epi
  apply (cancel_epi π).1
  rw [← Category.assoc, normalizedApexIso_projection, d.q_mu,
    normalizedSpan_right_projection]

end ExtensionDiagram

namespace ExtensionCategory

/-- The extension target with the literal given quotient as its object. -/
@[expose]
def target : ExtensionCategory C ⥤ QuillenQ C where
  obj E := ⟨E.row.X₃⟩
  map {E' E} f :=
    (QuillenQ.underlyingIso (quotientIso E')).inv ≫
      (normalization ⋙ admissibleMonoSubdivisionQuillenFunctor).map f ≫
      (QuillenQ.underlyingIso (quotientIso E)).hom
  map_id E := by
    rw [(normalization (C := C) ⋙ admissibleMonoSubdivisionQuillenFunctor).map_id E]
    let e := QuillenQ.underlyingIso (quotientIso E)
    change e.inv ≫ (𝟙 _ ≫ e.hom) = 𝟙 _
    rw [Category.id_comp]
    exact e.inv_hom_id
  map_comp f g := by
    simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

/-- The target object is the given quotient, without replacing its carrier. -/
@[simp]
theorem target_obj (E : ExtensionCategory C) :
    (target (C := C)).obj E = (⟨E.row.X₃⟩ : QuillenQ C) := rfl

/-- Target maps conjugate the actual normalization functor by cokernel comparisons. -/
theorem target_map {E' E : ExtensionCategory C} (f : E' ⟶ E) :
    (target (C := C)).map f =
      (QuillenQ.underlyingIso (quotientIso E')).inv ≫
        (normalization ⋙ admissibleMonoSubdivisionQuillenFunctor).map f ≫
        (QuillenQ.underlyingIso (quotientIso E)).hom := rfl

/-- Every representative maps to its actual right-column span with the given apex. -/
theorem target_map_mkHom {E' E : ExtensionCategory C} (d : ExtensionDiagram E' E) :
    (target (C := C)).map (mkHom d) = QuillenQ.mkHom d.toQuillenSpan := by
  have h := QuillenQ.mkHom_naturality_of_span_iso
    (admissibleMonoSubdivisionQuillenSpan d.normalize) d.toQuillenSpan
    (quotientIso E') (quotientIso E) (ExtensionDiagram.normalizedApexIso d)
    (ExtensionDiagram.normalizedApexIso_left d) (ExtensionDiagram.normalizedApexIso_right d)
  rw [target_map]
  change (QuillenQ.underlyingIso (quotientIso E')).inv ≫
      (QuillenQ.mkHom
        (X := admissibleMonoSubdivisionQuillenObj E'.subdivisionObj)
        (Y := admissibleMonoSubdivisionQuillenObj E.subdivisionObj)
        (admissibleMonoSubdivisionQuillenSpan d.normalize) ≫
        (QuillenQ.underlyingIso (quotientIso E)).hom) = _
  rw [h, Iso.inv_hom_id_assoc]

/-- Canonical comparison from the selected-quotient functor to the given-quotient target. -/
@[expose]
def targetNormalizationIso :
    (normalization (C := C) ⋙ admissibleMonoSubdivisionQuillenFunctor) ≅ target :=
  NatIso.ofComponents (fun E => QuillenQ.underlyingIso (quotientIso E)) (by
    intro E' E f
    dsimp only [target]
    simp only [Iso.hom_inv_id_assoc])

/-- The comparison component is the lift of the actual cokernel isomorphism. -/
@[simp]
theorem targetNormalizationIso_app (E : ExtensionCategory C) :
    (targetNormalizationIso (C := C)).app E =
      QuillenQ.underlyingIso (quotientIso E) := rfl

end ExtensionCategory

end AlgebraicKTheory
