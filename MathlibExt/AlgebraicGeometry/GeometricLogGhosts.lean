/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EtaleLogDiagrams
public import MathlibExt.AlgebraicGeometry.RingedSiteLogMorphisms
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Actual geometric ghost fibres and normalized maps

Ghosts are the native site-point fibres of the actual characteristic sheaf.
A morphism's ghost map is characterized on every etale log section and
actual geometric lift into the scheme fibre product. This specifies the
canonical stalk map without replacing ghosts or their maps by named carriers.
References: Kato §1; Gross--Siebert arXiv:1102.4322v2, §1.5.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.GeometricLogGhosts
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.EtaleLogSchemes
open MathlibExt.AlgebraicGeometry.EtaleLogDiagrams
open MathlibExt.AlgebraicGeometry.SmallEtaleGeometry
open MathlibExt.AlgebraicGeometry.LogStructures

variable [InverseImageTheory.{0}]

/-- A geometric point of the actual small etale site. -/
abbrev point {X : Scheme.{0}} {Ω : Type} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :=
  Scheme.pointSmallEtale x

/-- The actual geometric characteristic monoid; the larger coefficient
universe supports sheafification on the genuine small etale category. -/
abbrev ghost (X : LogScheme.{0}) {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X.scheme) : CommMonCat.{1} :=
  ((point x).sheafFiber (A := CommMonCat.{1})).obj
    (characteristic X.scheme.smallEtaleTopology X.log)

/-- The canonical geometric lift into the actual base-changed etale scheme. -/
def geometricLift {X Y : Scheme.{0}} (f : X ⟶ Y) {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (U : Y.Etale) (a : (point (x ≫ f)).fiber.obj U) :
    (point x).fiber.obj ((etaleBaseChange f).obj U) :=
  Over.homMk (pullback.lift a.left x (Over.w a)) (by
    change pullback.lift a.left x (Over.w a) ≫ pullback.snd U.hom f = x
    simp)

/-- Source-normalized geometric ghost map of an actual log morphism.
Every defining colimit generator is tied to its actual local log section. -/
structure GhostMap {X Y : LogScheme.{0}} (f : Hom X Y)
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X.scheme) where
  map : ghost Y (x ≫ f.map) ⟶ ghost X x
  normalization : ∀ (U : Y.scheme.Etale) (a : (point (x ≫ f.map)).fiber.obj U)
    (m : (monoid Y.scheme.smallEtaleTopology Y.log).obj.obj (op U)),
    map.hom (((point (x ≫ f.map)).toPresheafFiber U a
      (characteristic Y.scheme.smallEtaleTopology Y.log).obj).hom
      ((LogStructures.characteristicMap Y.scheme.smallEtaleTopology Y.log).hom.app (op U) m)) =
    ((point x).toPresheafFiber ((etaleBaseChange f.map).obj U) (geometricLift f.map x U a)
      (characteristic X.scheme.smallEtaleTopology X.log).obj).hom
      ((LogStructures.characteristicMap X.scheme.smallEtaleTopology X.log).hom.app
        (op ((etaleBaseChange f.map).obj U)) ((monoidSharp f).hom.app (op U) m))

/-- Integral morphisms are tested by actual pushouts against integral monoids. -/
def IsIntegralMap {P Q : CommMonCat.{1}} (f : P ⟶ Q) : Prop :=
  IsIntegralMonoid P ∧ IsIntegralMonoid Q ∧
    ∀ (R : CommMonCat.{1}) (g : P ⟶ R), IsIntegralMonoid R →
      IsIntegralMonoid (pushout f g)

/-- The actual stalkwise integrality condition of a fine log morphism. -/
structure IntegralMorphism {X Y : LogScheme.{0}} (f : Hom X Y) where
  ghostMap : ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X.scheme), GhostMap f x
  integral : ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X.scheme),
    IsIntegralMap (ghostMap Ω x).map

end MathlibExt.AlgebraicGeometry.GeometricLogGhosts
