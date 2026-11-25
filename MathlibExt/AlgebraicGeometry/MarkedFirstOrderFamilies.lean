/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MarkedMapDeformationCones
public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Actual pointed first-order deformations of marked map families

The parameter algebra is the native square-zero algebra Ω⊕Ω.
Reduction is Spec of its actual projection and the constant parameter
map is Spec of its actual inclusion. A deformation is an actual marked
map family over that parameter with a genuine Cartesian reduction to
the original family, retaining every marking and target equation.

Isomorphism classes use actual map-family isomorphisms commuting with
that reduction. A trivial deformation is additionally fixed by its
Cartesian projection to the original curve and all its maps.
No free tangent carrier or arbitrary equivalence relation is supplied.

Generic square-zero/base-change and stable-family operations are complete
public-source integration (AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
Cotangent/AlgebraExtension and Stacks/HomStack, Apache 2.0; TauCeti
62bbc0596dc3539d488232e4e924a338548ea0a9, Curves/StableMaps).
The normalized comparison with the computed cotangent cone is separate.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MarkedFirstOrderFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies

abbrev DualNumbers (Ω : Type) [Field Ω] := TrivSqZeroExt Ω Ω

def parameterProjection (Ω : Type) [Field Ω] : Spec (.of (DualNumbers Ω)) ⟶ Spec (.of Ω) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom Ω Ω))

def reduction (Ω : Type) [Field Ω] : Spec (.of Ω) ⟶ Spec (.of (DualNumbers Ω)) :=
  Spec.map (CommRingCat.ofHom
    (TrivSqZeroExt.fstHom (R := Ω) (M := Ω) (S := Ω)).toRingHom)

theorem reduction_projection (Ω : Type) [Field Ω] :
    reduction Ω ≫ parameterProjection Ω = 𝟙 (Spec (.of Ω)) := by
  have h : (CommRingCat.ofHom (TrivSqZeroExt.inlHom Ω Ω)) ≫
      CommRingCat.ofHom
        (TrivSqZeroExt.fstHom (R := Ω) (M := Ω) (S := Ω)).toRingHom =
      𝟙 (CommRingCat.of Ω) := by
    ext x
    rfl
  rw [reduction, parameterProjection, ← Spec.map_comp, h, Spec.map_id]

variable {V S : Scheme.{0}} {q : V ⟶ S} {n g : ℕ}
  {Ω : Type} [Field Ω] {b : Spec (.of Ω) ⟶ S}
  (F : Family q n g (Spec (.of Ω)) b)

/-- Actual first-order marked map with its exact Cartesian reduction. -/
structure Deformation where
  family : Family q n g (Spec (.of (DualNumbers Ω))) (parameterProjection Ω ≫ b)
  reductionMap : F.curve.X ⟶ family.curve.X
  square : IsPullback reductionMap F.curve.π family.curve.π (reduction Ω)
  markings : ∀ i : Fin n, F.curve.marking i ≫ reductionMap = reduction Ω ≫ family.curve.marking i
  targetMap : reductionMap ≫ family.map = F.map

/-- Genuine first-order family isomorphism retaining the original reduction. -/
def Isomorphic (D E : Deformation F) : Prop :=
  ∃ h : D.family ⟶ E.family, D.reductionMap ≫ h.iso.hom = E.reductionMap

theorem isomorphic_refl (D : Deformation F) : Isomorphic F D D := by
  refine ⟨𝟙 D.family, ?_⟩
  change D.reductionMap ≫ 𝟙 D.family.curve.X = D.reductionMap
  exact Category.comp_id _

theorem isomorphic_symm {D E : Deformation F} (h : Isomorphic F D E) : Isomorphic F E D := by
  obtain ⟨h, hh⟩ := h
  refine ⟨Groupoid.inv h, ?_⟩
  change E.reductionMap ≫ h.iso.inv = D.reductionMap
  rw [← hh]
  simp [Category.assoc]

theorem isomorphic_trans {D E G : Deformation F}
    (h : Isomorphic F D E) (k : Isomorphic F E G) : Isomorphic F D G := by
  obtain ⟨h, hh⟩ := h
  obtain ⟨k, hk⟩ := k
  refine ⟨h ≫ k, ?_⟩
  change D.reductionMap ≫ (h.iso.hom ≫ k.iso.hom) = G.reductionMap
  rw [← Category.assoc, hh, hk]

def deformationSetoid : Setoid (Deformation F) where
  r := Isomorphic F
  iseqv := ⟨isomorphic_refl F, isomorphic_symm F, isomorphic_trans F⟩

abbrev DeformationClasses := Quotient (deformationSetoid F)

def deformationClass (D : Deformation F) : DeformationClasses F :=
  Quotient.mk (deformationSetoid F) D

/-- A genuine constant first-order family, with its native Cartesian projection fixed. -/
structure TrivialDeformation where
  deformation : Deformation F
  projection : deformation.family.curve.X ⟶ F.curve.X
  square : IsPullback projection deformation.family.curve.π F.curve.π (parameterProjection Ω)
  reduction_identity : deformation.reductionMap ≫ projection = 𝟙 F.curve.X
  markings : ∀ i : Fin n,
    deformation.family.curve.marking i ≫ projection = parameterProjection Ω ≫ F.curve.marking i
  targetMap : projection ≫ F.map = deformation.family.map

/-- A genuine first-order motion of a given point in the fixed target fibre. -/
structure PointDeformation (x : Spec (.of Ω) ⟶ V) (hx : x ≫ q = b) where
  map : Spec (.of (DualNumbers Ω)) ⟶ V
  over : map ≫ q = parameterProjection Ω ≫ b
  reduction_map : reduction Ω ≫ map = x

@[ext] theorem pointDeformation_ext {x : Spec (.of Ω) ⟶ V} {hx : x ≫ q = b}
    {A B : PointDeformation (q := q) (b := b) x hx} (h : A.map = B.map) : A = B := by
  cases A
  cases B
  cases h
  rfl

/-- Evaluation of a first-order family is its literal marked target map. -/
def evaluationDeformation (D : Deformation F) (i : Fin n) :
    PointDeformation (evaluation F i) (evaluation_over F i) where
  map := evaluation D.family i
  over := evaluation_over D.family i
  reduction_map := by
    rw [GeneralStableMapFamilies.evaluation, ← Category.assoc,
      ← D.markings i, Category.assoc, D.targetMap]
    rfl

theorem evaluationDeformation_eq_of_isomorphic {D E : Deformation F}
    (h : Isomorphic F D E) (i : Fin n) :
    evaluationDeformation F D i = evaluationDeformation F E i := by
  obtain ⟨h, _⟩ := h
  apply pointDeformation_ext
  exact evaluation_eq_of_hom D.family h i

/-- The actual first-order evaluation descends to family-isomorphism classes. -/
def classEvaluation (i : Fin n) :
    DeformationClasses F → PointDeformation (evaluation F i) (evaluation_over F i) :=
  Quotient.lift (fun D => evaluationDeformation F D i)
    (fun _ _ h => evaluationDeformation_eq_of_isomorphic F h i)

theorem classEvaluation_mk (D : Deformation F) (i : Fin n) :
    classEvaluation F i (deformationClass F D) = evaluationDeformation F D i := rfl

/-- The zero tangent point is the actual constant target map over dual numbers. -/
def constantPointDeformation (x : Spec (.of Ω) ⟶ V) (hx : x ≫ q = b) :
    PointDeformation (q := q) (b := b) x hx where
  map := parameterProjection Ω ≫ x
  over := by rw [Category.assoc, hx]
  reduction_map := by rw [← Category.assoc, reduction_projection, Category.id_comp]

theorem classEvaluation_trivial (T : TrivialDeformation F) (i : Fin n) :
    classEvaluation F i (deformationClass F T.deformation) =
      constantPointDeformation (evaluation F i) (evaluation_over F i) := by
  apply pointDeformation_ext
  change T.deformation.family.curve.marking i ≫ T.deformation.family.map =
    parameterProjection Ω ≫ (F.curve.marking i ≫ F.map)
  rw [← T.targetMap, ← Category.assoc, T.markings i, Category.assoc]

end MathlibExt.AlgebraicGeometry.MarkedFirstOrderFamilies
