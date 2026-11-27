/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EtaleLogSchemes
public import MathlibExt.AlgebraicGeometry.EtaleBaseChangeCoherence

/-!
# Actual small-etale log diagrams and strictness

A commuting square is normalized on every actual local log section,
transported by native scheme pullback comparisons. Strictness uses the
actual associated inverse-image prelog comparison, including nonintegral
log structures. The inverse-image theory below supplies only continuity
and adjoint proofs for the fixed native site functors; it does not supply
an arbitrary geometric operation or any paper conclusion.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.EtaleLogDiagrams
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.EtaleLogSchemes
open MathlibExt.AlgebraicGeometry.SmallEtaleGeometry
open MathlibExt.AlgebraicGeometry.LogStructures
universe u

/-- Inverse images on small étale sites: an instance asserts that for every morphism of schemes
$f : X \to Y$, étale base change along $f$ is continuous for the small étale topologies and
pushforward along it of sheaves of commutative monoids is a right adjoint (that is, has an
inverse-image left adjoint), for commutative monoids in universe `u` (`HasInverseImage f`) and in
universe `u + 1`. -/
class InverseImageTheory where
  [along : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y), HasInverseImage f]
  [largeAdjoint : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
    ((etaleBaseChange f).sheafPushforwardContinuous CommMonCat.{u+1}
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]

attribute [instance] InverseImageTheory.along InverseImageTheory.largeAdjoint

variable [InverseImageTheory.{u}]

abbrev monoidSharp {X Y : LogScheme.{u}} (f : Hom X Y) := f.logMap.left

/-- Full sectionwise log compatibility on the native commuting square. -/
structure Square {X Y Z W : LogScheme.{u}}
    (f : Hom X Y) (g : Hom Y W) (h : Hom X Z) (k : Hom Z W) where
  commutes : f.map ≫ g.map = h.map ≫ k.map
  log_commutes : ∀ (U : W.scheme.Etale)
    (m : (monoid W.scheme.smallEtaleTopology W.log).obj.obj (op U)),
    (monoid X.scheme.smallEtaleTopology X.log).obj.map
      ((EtaleBaseChangeCoherence.composition f.map g.map).inv.app U).op
      ((monoidSharp f).hom.app (op ((etaleBaseChange g.map).obj U))
        ((monoidSharp g).hom.app (op U) m)) =
    (monoid X.scheme.smallEtaleTopology X.log).obj.map
      ((eqToIso (congrArg etaleBaseChange commutes)).hom.app U).op
      ((monoid X.scheme.smallEtaleTopology X.log).obj.map
        ((EtaleBaseChangeCoherence.composition h.map k.map).inv.app U).op
        ((monoidSharp h).hom.app (op ((etaleBaseChange k.map).obj U))
          ((monoidSharp k).hom.app (op U) m)))

abbrev largePullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (etaleBaseChange f).sheafPullback CommMonCat.{u+1}
    Y.smallEtaleTopology X.smallEtaleTopology

abbrev largeAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (etaleBaseChange f).sheafAdjunctionContinuous CommMonCat.{u+1}
    Y.smallEtaleTopology X.smallEtaleTopology

/-- The actual target log map into the source ring, before logification. -/
def ringPrelogMap (X Y : LogScheme.{u}) (f : X.scheme ⟶ Y.scheme) :
    monoid Y.scheme.smallEtaleTopology Y.log ⟶
      ((etaleBaseChange f).sheafPushforwardContinuous CommMonCat
        Y.scheme.smallEtaleTopology X.scheme.smallEtaleTopology).obj
        (ringMonoids X.scheme.smallEtaleTopology (structureRing X.scheme)) :=
  alpha Y.scheme.smallEtaleTopology Y.log ≫
    (ringMonoidsFunctor Y.scheme.smallEtaleTopology).map (ringSharp f) ≫
    (pushRingMonoidsIso X.scheme.smallEtaleTopology Y.scheme.smallEtaleTopology
      (etaleBaseChange f) (structureRing X.scheme)).hom

/-- The inverse-image prelog uses the native inverse-image adjunction. -/
def inversePrelog (X Y : LogScheme.{u}) (f : X.scheme ⟶ Y.scheme) :
    Prelog X.scheme.smallEtaleTopology (structureRing X.scheme) :=
  Over.mk (((largeAdjunction f).homEquiv _ _).symm (ringPrelogMap X Y f))

/-- The actual comparison from the inverse-image candidate to the source log. -/
def inverseCandidateMap {X Y : LogScheme.{u}} (f : Hom X Y) :
    inversePrelog X Y f.map ⟶ X.log.obj :=
  Over.homMk (((largeAdjunction f.map).homEquiv _ _).symm (monoidSharp f)) (by
    apply ((largeAdjunction f.map).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right]
    simpa [inversePrelog, ringPrelogMap, monoidSharp, LogStructures.alpha] using Over.w f.logMap)

def inverseComparison {X Y : LogScheme.{u}} (f : Hom X Y) :
    associatedPrelog X.scheme.smallEtaleTopology (inversePrelog X Y f.map) ⟶ X.log.obj :=
  associatedMap X.scheme.smallEtaleTopology X.log (inverseCandidateMap f)

/-- Actual log strictness; no characteristic-only replacement is used. -/
def IsStrict {X Y : LogScheme.{u}} (f : Hom X Y) : Prop :=
  IsIso (inverseComparison f).left

end MathlibExt.AlgebraicGeometry.EtaleLogDiagrams
