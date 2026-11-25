/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EtaleLogDiagrams
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Independent logarithmic infinitesimal lifting contracts

Formal log smoothness is the actual local lifting condition for strict
square-zero log thickenings. All maps are normalized small-etale log arrows,
all reductions are literal scheme fibre products, and local charts cover
the underlying test scheme. Log smoothness adds finite presentation.
This definition does not use a chart criterion as its own proof request.
Reference: Kato, Logarithmic structures of Fontaine--Illusie, §3.
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.FormalLogSmoothness
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.EtaleLogSchemes
open MathlibExt.AlgebraicGeometry.EtaleLogDiagrams
open MathlibExt.AlgebraicGeometry.LogStructures

variable [InverseImageTheory.{0}]

/-- Bundle an actual log arrow along a fixed scheme map. -/
def homOfAlong (X Y : LogScheme.{0}) (f : X.scheme ⟶ Y.scheme) (a : MorphismAlong X Y f) :
    EtaleLogSchemes.Hom X Y := { map := f, logMap := a }

/-- Strict square-zero thickenings retain the actual section-ring kernel.
Surjectivity records that the closed immersion has the same support. -/
structure SquareZeroThickening {Z₀ Z : LogScheme.{0}} (i : Hom Z₀ Z) where
  [closed : IsClosedImmersion i.map]
  surjective : Function.Surjective i.map
  strict : IsStrict i
  sourceFine : Z₀.IsFine
  targetFine : Z.IsFine
  squareZero : ∀ (U : Z.scheme.Opens) (a b : Γ(Z.scheme,U)),
    (i.map.app U).hom a = 0 → (i.map.app U).hom b = 0 → a*b = 0


/-- The literal lifting square for a prescribed log morphism. -/
structure LiftingDiagram {X Y : LogScheme.{0}} (f : Hom X Y) where
  Z₀ : LogScheme.{0}
  Z : LogScheme.{0}
  inclusion : Hom Z₀ Z
  thickening : SquareZeroThickening inclusion
  source : Hom Z₀ X
  base : Hom Z Y
  commutes : Square source f inclusion base

/-- One strict etale neighborhood with a genuine lift. Its reduction is
exactly the scheme-theoretic base change of the original thickening. -/
structure LocalLift {X Y : LogScheme.{0}} {f : Hom X Y} (D : LiftingDiagram f) where
  U : LogScheme.{0}
  neighborhood : Hom U D.Z
  [etale : Etale neighborhood.map]
  strict : IsStrict neighborhood
  fine : U.IsFine
  lift : Hom U X
  baseSquare : Square lift f neighborhood D.base
  reductionLog : LogStructure
    (pullback D.inclusion.map neighborhood.map).smallEtaleTopology
    (structureRing (pullback D.inclusion.map neighborhood.map))
  reductionToU : MorphismAlong ⟨pullback D.inclusion.map neighborhood.map,reductionLog⟩ U
    (pullback.snd D.inclusion.map neighborhood.map)
  reductionToSource : MorphismAlong ⟨pullback D.inclusion.map neighborhood.map,reductionLog⟩ D.Z₀
    (pullback.fst D.inclusion.map neighborhood.map)
  inclusionStrict : IsStrict (homOfAlong ⟨pullback D.inclusion.map neighborhood.map,reductionLog⟩ U
    (pullback.snd D.inclusion.map neighborhood.map)
    reductionToU)
  reductionStrict : IsStrict (homOfAlong ⟨pullback D.inclusion.map neighborhood.map,reductionLog⟩ D.Z₀
    (pullback.fst D.inclusion.map neighborhood.map)
    reductionToSource)
  reductionSquare : Square
    (homOfAlong ⟨pullback D.inclusion.map neighborhood.map,reductionLog⟩ U
    (pullback.snd D.inclusion.map neighborhood.map) reductionToU) neighborhood
    (homOfAlong ⟨pullback D.inclusion.map neighborhood.map,reductionLog⟩ D.Z₀
    (pullback.fst D.inclusion.map neighborhood.map) reductionToSource) D.inclusion
  extension : Square
    (homOfAlong ⟨pullback D.inclusion.map neighborhood.map,reductionLog⟩ U
    (pullback.snd D.inclusion.map neighborhood.map) reductionToU) lift
    (homOfAlong ⟨pullback D.inclusion.map neighborhood.map,reductionLog⟩ D.Z₀
    (pullback.fst D.inclusion.map neighborhood.map) reductionToSource) D.source

attribute [instance] LocalLift.etale

/-- The actual etale lifts cover the whole test scheme. -/
structure EtaleLifting {X Y : LogScheme.{0}} {f : Hom X Y} (D : LiftingDiagram f) where
  index : Type
  localLift : index → LocalLift D
  cover : (⋃ i : index, Set.range (localLift i).neighborhood.map) = Set.univ

def FormallyLogSmooth {X Y : LogScheme.{0}} (f : Hom X Y) : Prop :=
  ∀ D : LiftingDiagram f, Nonempty (EtaleLifting D)

def LogSmooth {X Y : LogScheme.{0}} (f : Hom X Y) : Prop :=
  LocallyOfFinitePresentation f.map ∧ FormallyLogSmooth f

end MathlibExt.AlgebraicGeometry.FormalLogSmoothness
