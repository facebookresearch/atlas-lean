/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RubberMapFamilies
public import MathlibExt.AlgebraicGeometry.ExpansionScalingModels
public import MathlibExt.AlgebraicGeometry.FiniteCoverLocalComparison

/-!
# Actual original and expanded-component rubber scalings

The last torus coordinate scales the original P1 by diag(1,c) on the
actual O plus O subline functor, on every parameter scheme. The other
coordinates scale the expansion parameters by the source's adjacent
ratios. Their standard-family action is tied to the actual contraction,
projection and both endpoint ideals.

This group has m+1 factors on the length-m framed chart. Its actual Lie
action must be removed when passing from the framed Li complex to rubber
moduli; a virtual-rank correction alone does not define that operation.
Source: JPPZ arXiv:1602.04705v2, Section0.2.4;
Jun Li arXiv:math/0009097v1, Sections1 and4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.RubberStandardScalingModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.MonObj
open _root_.AlgebraicGeometry
open CoherentCurveLinearSeries RelativeProjectiveLineModels ExpansionParameterModels ExpansionScalingModels
open ExpandedTargetChainGeometry StandardRelativeExpansionModels RubberMapFamilies FiniteCoverLocalComparison

variable {k : Type} [Field k]
  (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
  (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
  (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
  (m : ℕ) (H : TorusTheory k (m + 1))

structure Diagonal (T : Over (Spec (.of k))) (c : Γ(T.left, ⊤)ˣ) where
  split : (Scheme.Modules.pullback T.hom).obj
    (rulingModule (Spec (.of k)) (structureModule (Spec (.of k)))) ≅
      structureModule T.left ⊞ structureModule T.left
  split_left : (Scheme.Modules.pullback T.hom).map biprod.inl ≫ split.hom =
    (pullbackStructureIso T.hom).hom ≫ biprod.inl
  split_right : (Scheme.Modules.pullback T.hom).map biprod.inr ≫ split.hom =
    (pullbackStructureIso T.hom).hom ≫ biprod.inr
  map : (Scheme.Modules.pullback T.hom).obj
    (rulingModule (Spec (.of k)) (structureModule (Spec (.of k)))) ≅
      (Scheme.Modules.pullback T.hom).obj
        (rulingModule (Spec (.of k)) (structureModule (Spec (.of k))))
  localValues : ∀ (U : T.left.Opens) (x y : Γ(T.left, U)),
    (split.hom.val.app (.op U)).hom ((map.hom.val.app (.op U)).hom
      ((split.inv.val.app (.op U)).hom
        (((biprod.inl : structureModule T.left ⟶ structureModule T.left ⊞ structureModule T.left).val.app (.op U)).hom x +
         ((biprod.inr : structureModule T.left ⟶ structureModule T.left ⊞ structureModule T.left).val.app (.op U)).hom y))) =
    ((biprod.inl : structureModule T.left ⟶ structureModule T.left ⊞ structureModule T.left).val.app (.op U)).hom x +
    ((biprod.inr : structureModule T.left ⟶ structureModule T.left ⊞ structureModule T.left).val.app (.op U)).hom
      (((T.left.presheaf.map (homOfLE le_top).op).hom (c : Γ(T.left, ⊤))) * y)

structure ScaledSubline {T : Over (Spec (.of k))} {c : Γ(T.left, ⊤)ˣ}
    (d : Diagonal (k := k) T c)
    (L : Subline (Spec (.of k)) (structureModule (Spec (.of k))) T) where
  line : Subline (Spec (.of k)) (structureModule (Spec (.of k))) T
  module : line.module ≅ L.module
  inclusion : line.inclusion = module.hom ≫ L.inclusion ≫ d.map.hom

structure OriginalAction where
  action : letI := H.group; ModObj (torusScheme k (m + 1)) P.target
  diagonal : ∀ (T : Over (Spec (.of k))) (h : T ⟶ torusScheme k (m + 1)),
    Diagonal T (H.units T h (Fin.last m))
  scaled : ∀ (T : Over (Spec (.of k))) (h : T ⟶ torusScheme k (m + 1))
    (L : Subline (Spec (.of k)) (structureModule (Spec (.of k))) T), ScaledSubline (diagonal T h) L
  points : letI := H.group; letI := action;
    ∀ (T : Over (Spec (.of k))) (h : T ⟶ torusScheme k (m + 1)) (x : T ⟶ P.target),
    O.points T (CartesianMonoidalCategory.lift h x ≫ γ[torusScheme k (m + 1),P.target] ≫ D.target.hom) =
      sublineClass (Spec (.of k)) (structureModule (Spec (.of k)))
        (scaled T h (O.reindex (x ≫ D.target.hom) O.universal).subline).line

def productAction {G Y B : Over (Spec (.of k))} [GrpObj G] [ModObj G Y] [ModObj G B] :
    G ⊗ prod Y B ⟶ prod Y B :=
  prod.lift ((G ◁ (prod.fst : prod Y B ⟶ Y)) ≫ γ[G,Y])
    ((G ◁ (prod.snd : prod Y B ⟶ B)) ≫ γ[G,B])

def standardZeroIdeal : (S.chart m).scheme.left.IdealSheafData :=
  (originalZero O P D).left.ker.comap ((S.chart m).contraction.left ≫
    (prod.fst : prod P.target (ParameterSpace k m) ⟶ P.target).left)

structure StandardAction where
  original : OriginalAction O P D m H
  parameter : letI := H.group; ModObj (torusScheme k (m + 1)) (ParameterSpace k m)
  standard : letI := H.group; ModObj (torusScheme k (m + 1)) (S.chart m).scheme
  coordinates : letI := H.group; letI := parameter;
    ∀ (T : Over (Spec (.of k))) (h : T ⟶ torusScheme k (m + 1))
    (x : T ⟶ ParameterSpace k m) (i : Fin m),
      (CartesianMonoidalCategory.lift h x ≫ γ[torusScheme k (m + 1),ParameterSpace k m]).left.appTop.hom
        (parameterCoordinate k m i) =
      (adjacentUnit (fun j : Fin m => H.units T h j.castSucc) i : Γ(T.left, ⊤)) *
        x.left.appTop.hom (parameterCoordinate k m i)
  projection : letI := H.group; letI := parameter; letI := standard;
    γ[torusScheme k (m + 1),(S.chart m).scheme] ≫ (S.chart m).projection =
      (torusScheme k (m + 1) ◁ (S.chart m).projection) ≫ γ[torusScheme k (m + 1),ParameterSpace k m]
  contraction : letI := H.group; letI := original.action; letI := parameter; letI := standard;
    γ[torusScheme k (m + 1),(S.chart m).scheme] ≫ (S.chart m).contraction =
      (torusScheme k (m + 1) ◁ (S.chart m).contraction) ≫ productAction
  infinity : letI := H.group; letI := parameter; letI := standard;
    originalProductAction P.divisor ≫ (S.chart m).boundary =
      (torusScheme k (m + 1) ◁ (S.chart m).boundary) ≫ γ[torusScheme k (m + 1),(S.chart m).scheme]
  zero : letI := H.group; letI := standard;
    (standardZeroIdeal O P D R S m).comap γ[torusScheme k (m + 1),(S.chart m).scheme].left =
      (standardZeroIdeal O P D R S m).comap
        (CartesianMonoidalCategory.snd (torusScheme k (m + 1)) (S.chart m).scheme).left

end MathlibExt.AlgebraicGeometry.RubberStandardScalingModels
