/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiGenericSourceAssemblyModels
public import MathlibExt.AlgebraicGeometry.LiGluingRelativeTypes

/-!
# Native relative-family qualification of every generic Li source chart

A qualified chart is the actual relative moduli point interpreted by its
native family functor. Its source curves, all ordered markings, contact
orders, boundary ideal and map are identified with that family. Its
target is the actual standard expanded pair, with the native parameter,
contraction and scaling action. Thus an unrelated geometry or source
comparison is not an input to the source constructor.

Every possible qualified chart belongs to the complete source index.
The normalized global source assembly is a construction output.
Source: Jun Li math/0110113v1 (1.23)--(1.25) and Theorem 2.3;
math/0009097v1 Sections 4.1--4.3.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiRelativeSourceModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry _root_.Opposite
open GeneralStackGeometry StackCycleGeometry StackAffineModules
open ExpandedTargetChainGeometry RelativeProjectiveLineModels StandardRelativeExpansionModels
open ExpansionParameterModels ExpandedRelativeFamilies LiGluingRelativeTypes
open LiGenericSourceIndex

variable {k : Type} [Field k]
  (P : RelativePair (k := k)) (R : ProjectiveLine P.divisor.left (normalLineModule P))
  (S : StandardSystem P R) {n r : ℕ} (G : FullType n r)
  [LocallyOfFiniteType P.target.hom] [IsNoetherian P.target.left]
  (beta : Fin G.vertices → StableMapNumericalClasses.NumericalClass P.target.left)
  (M : ModuliModel P R S G beta)

def actualFamily (C : SourceChart M.stack) : LiGluingRelativeTypes.Family P R S G C.spec :=
  ((M.family C.spec).obj C.point).obj

structure Frame (C : SourceChart M.stack) where
  gauge : LiGenericGaugeSourceModels.Source C
  target : Over.mk C.family.structural ≅ (S.chart gauge.gauge.rank).scheme
  parameter : Over.mk C.family.parameterStructural ≅ ParameterSpace k gauge.gauge.rank
  projection : C.family.projection ≫ parameter.hom.left =
    target.hom.left ≫ (S.chart gauge.gauge.rank).projection.left
  parameterMap : C.spec ⟶ ParameterSpace k gauge.gauge.rank
  parameter_square : C.family.parameter ≫ parameter.hom.left = parameterMap.left
  identification : StandardFamilyIdentification P R S
    (actualFamily P R S G beta M C).target gauge.gauge.rank parameterMap
  relativeTarget : pullback C.family.projection C.family.parameter ≅
    (actualFamily P R S G beta M C).target.scheme.left
  relative_projection : relativeTarget.hom ≫
    (actualFamily P R S G beta M C).target.projection.left =
      pullback.snd C.family.projection C.family.parameter
  relative_template : relativeTarget.hom ≫ identification.comparison.hom.left ≫
    (pullback.fst (S.chart gauge.gauge.rank).projection parameterMap).left =
      pullback.fst C.family.projection C.family.parameter ≫ target.hom.left
  vertex : Fin G.vertices ≃ Fin C.family.components
  marking : ∀ v, Fin (G.legs v + G.roots v) ≃ Fin (C.family.markings (vertex v))
  genus : ∀ v, C.family.genus (vertex v) = G.genus v
  curve : ∀ v, (C.family.curve (vertex v)).X ≅ ((actualFamily P R S G beta M C).maps v).curve.X
  curve_projection : ∀ v, (curve v).hom ≫
    ((actualFamily P R S G beta M C).maps v).curve.π = (C.family.curve (vertex v)).π
  curve_marking : ∀ v i, (C.family.curve (vertex v)).marking (marking v i) ≫ (curve v).hom =
    ((actualFamily P R S G beta M C).maps v).curve.marking i
  map : ∀ v, C.family.relative (vertex v) ≫ relativeTarget.hom =
    (curve v).hom ≫ ((actualFamily P R S G beta M C).maps v).map
  boundary : Fin 1 ≃ Fin C.family.boundaryCount
  boundary_ideal : C.family.boundary (boundary 0) =
    (S.chart gauge.gauge.rank).boundary.left.ker.comap target.hom.left
  ordinary_marking : ∀ v i, C.family.root (vertex v) (marking v (Fin.castAdd (G.roots v) i)) = none
  relative_marking : ∀ v i, C.family.root (vertex v) (marking v (Fin.natAdd (G.legs v) i)) =
    some (boundary 0)
  order : ∀ v i, C.family.order (vertex v) (marking v (Fin.natAdd (G.legs v) i)) =
    G.order (G.rootLabels.symm ⟨v, i⟩)
  parameterLabels : Fin gauge.gauge.rank ≃ Fin C.family.parameterCount
  parameter_normalized : ∀ i, C.family.parameterBaseFunction (parameterLabels i) =
    parameter.hom.left.appTop.hom (parameterCoordinate k gauge.gauge.rank i)
  scaling : ExpansionScalingModels.ScalingData P R S gauge.gauge.rank gauge.gauge.torus
  scaling_normalized : letI := gauge.gauge.torus.group;
    letI := gauge.gauge.action; letI := scaling.standard;
    γ[torusScheme k gauge.gauge.rank,Over.mk C.family.structural] ≫ target.hom =
      (torusScheme k gauge.gauge.rank ◁ target.hom) ≫
        γ[torusScheme k gauge.gauge.rank,(S.chart gauge.gauge.rank).scheme]

abbrev QualifiedFrame (C : SourceChart M.stack) := ULift.{2} (Frame P R S G beta M C)

def gauge (C : SourceChart M.stack) (h : QualifiedFrame P R S G beta M C) := h.down.gauge

def actualSourceArrow {C E : SourceChart M.stack}
    (h : Frame P R S G beta M C) (j : Frame P R S G beta M E) (f : E.native ⟶ C.native)
    (v : Fin G.vertices) : (E.family.curve (j.vertex v)).X ⟶ (C.family.curve (h.vertex v)).X :=
  (j.curve v).hom ≫ (((M.family E.spec).map f.hom.fiber).hom.source v).hom ≫
    (M.reindex f.hom.base C.point).source v ≫ (h.curve v).inv

def actualTargetArrow {C E : SourceChart M.stack}
    (h : Frame P R S G beta M C) (j : Frame P R S G beta M E) (f : E.native ⟶ C.native) :
    pullback E.family.projection E.family.parameter ⟶ pullback C.family.projection C.family.parameter :=
  j.relativeTarget.hom ≫ ((M.family E.spec).map f.hom.fiber).hom.target.iso.hom.left ≫
    (M.reindex f.hom.base C.point).target.left ≫ h.relativeTarget.inv

/-- Source refinements use the actual interpreted stack arrow, including every stabilizer. -/
structure ArrowNormalization {C E : SourceChart M.stack}
    (h : Frame P R S G beta M C) (j : Frame P R S G beta M E) (f : E.native ⟶ C.native)
    (F : LiGenericSourceRefinementModels.FamilyMap C E f) : Prop where
  vertex : F.vertex = j.vertex.symm.trans h.vertex
  source : ∀ v : Fin G.vertices, HEq (F.source (j.vertex v))
    (actualSourceArrow P R S G beta M h j f v)
  target : F.target = actualTargetArrow P R S G beta M h j f

/-- Every source chart, arbitrary affine base change and actual etale covering is retained. -/
structure Source where
  assembly : LiGenericSourceAssemblyModels.Assembly M.stack (QualifiedFrame P R S G beta M)
    (gauge P R S G beta M)
  left : ∀ (C E : SourceChart M.stack) (h : QualifiedFrame P R S G beta M C)
    (j : QualifiedFrame P R S G beta M E) (f : E.native ⟶ C.native),
    ArrowNormalization P R S G beta M h.down
      (assembly.native.refinement C E h j f).qualification.down
      (assembly.native.refinement C E h j f).left (assembly.native.leftSource C E h j f).family
  right : ∀ (C E : SourceChart M.stack) (h : QualifiedFrame P R S G beta M C)
    (j : QualifiedFrame P R S G beta M E) (f : E.native ⟶ C.native),
    ArrowNormalization P R S G beta M j.down
      (assembly.native.refinement C E h j f).qualification.down
      (assembly.native.refinement C E h j f).right (assembly.native.rightSource C E h j f).family

end MathlibExt.AlgebraicGeometry.LiRelativeSourceModels
