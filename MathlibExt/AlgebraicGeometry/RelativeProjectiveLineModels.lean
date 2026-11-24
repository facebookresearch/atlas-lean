/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeLineDuals
public import MathlibExt.AlgebraicGeometry.CartierIdealModels
public import MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry
public import MathlibExt.AlgebraicGeometry.SchemeNormalBundleMaps
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Actual relative projective lines and coordinate boundaries

P(O_D tensorplus N) represents rank-one subbundles of that actual module,
with locally free rank-one quotient. All parameter schemes, inclusion maps,
isomorphisms and pullbacks are retained. The convention is sublines: the
O_D coordinate section has normal bundle N, while the N coordinate section
has normal bundle N inverse, as in Jun Li's expansion construction.
Source: Jun Li arXiv:math/0009097v1, Section 1, p6; Stacks Project,
relative projective bundles. Native modules, kernels and pullbacks are
completed Mathlib/Stacks source; their pinned notices are in the imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeProjectiveLineModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open CoherentCurveLinearSeries NativeLineDuals AlgebraicBundleGeometry

variable (D : Scheme.{0}) (N : D.Modules)

def rulingModule : D.Modules := structureModule D ⊞ N

structure Subline (T : Over D) where
  module : T.left.Modules
  line : IsLineBundle module
  inclusion : module ⟶ (Scheme.Modules.pullback T.hom).obj (rulingModule D N)
  [mono : Mono inclusion]
  quotientLine : IsLineBundle (cokernel inclusion)

structure SublineIso {T : Over D} (P Q : Subline D N T) where
  iso : P.module ≅ Q.module
  inclusion : iso.hom ≫ Q.inclusion = P.inclusion

def sublineRelation (T : Over D) (P Q : Subline D N T) : Prop := Nonempty (SublineIso D N P Q)

@[instance_reducible] def sublineSetoid (T : Over D) :=
  Relation.EqvGen.setoid (sublineRelation D N T)

abbrev SublineClasses (T : Over D) := Quotient (sublineSetoid D N T)

def sublineClass {T : Over D} (P : Subline D N T) : SublineClasses D N T := Quotient.mk _ P

/-- Reindexing keeps the literal pulled module and the full native inclusion square. -/
structure SublineReindex {T U : Over D} (f : T ⟶ U) (P : Subline D N U) where
  subline : Subline D N T
  module : (Scheme.Modules.pullback f.left).obj P.module ≅ subline.module
  inclusion : (Scheme.Modules.pullback f.left).map P.inclusion ≫
      (Scheme.Modules.pullbackComp f.left U.hom).hom.app (rulingModule D N) ≫
        (Scheme.Modules.pullbackCongr (Over.w f)).hom.app (rulingModule D N) =
    module.hom ≫ subline.inclusion

def classesReindex {T U : Over D} (f : T ⟶ U)
    (R : ∀ P : Subline D N U, SublineReindex D N f P)
    (I : ∀ {P Q : Subline D N U}, SublineIso D N P Q →
      SublineIso D N (R P).subline (R Q).subline) : SublineClasses D N U → SublineClasses D N T :=
  Quotient.map (fun P => (R P).subline) (by
    intro P Q h
    induction h with
    | rel P Q h => exact Relation.EqvGen.rel _ _ (h.map I)
    | refl P => exact Relation.EqvGen.refl _
    | symm P Q h ih => exact Relation.EqvGen.symm _ _ ih
    | trans P Q V hPQ hQV ihPQ ihQV => exact Relation.EqvGen.trans _ _ _ ihPQ ihQV)

/-- The actual represented relative scheme, universal subline, and coordinate sections. -/
structure ProjectiveLine where
  scheme : Scheme.{0}
  projection : scheme ⟶ D
  proper : IsProper projection
  smooth : SmoothOfRelativeDimension 1 projection
  connected : GeometricallyConnected projection
  universal : Subline D N (Over.mk projection)
  points : ∀ T : Over D, (T ⟶ Over.mk projection) ≃ SublineClasses D N T
  reindex : ∀ {T U : Over D} (f : T ⟶ U) (P : Subline D N U), SublineReindex D N f P
  reindexIso : ∀ {T U : Over D} (f : T ⟶ U) {P Q : Subline D N U},
    SublineIso D N P Q → SublineIso D N (reindex f P).subline (reindex f Q).subline
  identity : ∀ (T : Over D) (P : Subline D N T),
    Nonempty (SublineIso D N (reindex (𝟙 T) P).subline P)
  composition : ∀ {T U V : Over D} (f : T ⟶ U) (g : U ⟶ V) (P : Subline D N V),
    Nonempty (SublineIso D N (reindex f (reindex g P).subline).subline (reindex (f ≫ g) P).subline)
  universalPoint : ∀ (T : Over D) (f : T ⟶ Over.mk projection),
    points T f = sublineClass D N (reindex f universal).subline
  naturality : ∀ {T U : Over D} (f : T ⟶ U) (g : U ⟶ Over.mk projection),
    points T (f ≫ g) = classesReindex D N f (reindex f) (reindexIso f) (points U g)
  zero : D ⟶ scheme
  infinity : D ⟶ scheme
  zero_over : zero ≫ projection = 𝟙 D
  infinity_over : infinity ≫ projection = 𝟙 D
  [zero_closed : IsClosedImmersion zero]
  [infinity_closed : IsClosedImmersion infinity]
  zero_cartier : CartierIdealModels.IsEffectiveCartier zero.ker
  infinity_cartier : CartierIdealModels.IsEffectiveCartier infinity.ker
  coordinateZero : Subline D N (Over.mk (𝟙 D))
  coordinateInfinity : Subline D N (Over.mk (𝟙 D))
  zero_module : coordinateZero.module ≅ structureModule D
  infinity_module : coordinateInfinity.module ≅ N
  zero_inclusion : coordinateZero.inclusion ≫ (Scheme.Modules.pullbackId D).hom.app (rulingModule D N) =
    zero_module.hom ≫ biprod.inl
  infinity_inclusion : coordinateInfinity.inclusion ≫
      (Scheme.Modules.pullbackId D).hom.app (rulingModule D N) = infinity_module.hom ≫ biprod.inr
  zero_point : points (Over.mk (𝟙 D)) (Over.homMk zero zero_over) = sublineClass D N coordinateZero
  infinity_point : points (Over.mk (𝟙 D)) (Over.homMk infinity infinity_over) =
    sublineClass D N coordinateInfinity
  zeroNormal : SchemeNormalBundleMaps.NormalBundleModel zero 1
  infinityNormal : SchemeNormalBundleMaps.NormalBundleModel infinity 1
  zero_normal : dualModule D zeroNormal.conormal ≅ N
  infinity_normal : dualModule D infinityNormal.conormal ≅ dualModule D N

attribute [instance] ProjectiveLine.zero_closed ProjectiveLine.infinity_closed

end MathlibExt.AlgebraicGeometry.RelativeProjectiveLineModels
