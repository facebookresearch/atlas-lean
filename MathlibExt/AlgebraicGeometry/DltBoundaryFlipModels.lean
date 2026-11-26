/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeProjectivity
public import MathlibExt.AlgebraicGeometry.RelativeMoriContracts
public import MathlibExt.AlgebraicGeometry.NormalCrossingsModels
public import MathlibExt.AlgebraicGeometry.RestrictedAdjointSections

/-!
# Actual dlt resolution witnesses and boundary-preserving flip models

Dlt is a smooth proper birational log-resolution witness, actual normal
crossings of the total boundary/exceptional support, and positivity of the
computed discrepancies of its exceptional prime divisors. Plt uses those
computed discrepancies on every genuine birational model. No singularity
score or arbitrary predicate is supplied.

The flip contract allows coefficient-one boundaries: its source is not
required to be klt. Its actual small projective map, codimension-one
identification, strict boundary transform and relative adjoint ampleness
are the same geometric data as the existing klt contract.

Native proper maps, normal crossings, canonical orders and restricted
section constructions are positively reused. Model-calculus and
resolution providers remain explicit completed-source integration.
Reference: Hacon--Xu, arXiv1302.0298v2, Theorem 1.1 and §2.1.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DltBoundaryFlipModels

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.RelativeMoriContracts
open MathlibExt.AlgebraicGeometry.RationalResolution
open MathlibExt.AlgebraicGeometry.MoriContractionModels
open MathlibExt.AlgebraicGeometry.RelativeProjectivity

variable {k : Type} [Field k] {n : ℕ}

/-- Actual closed support of the finite Weil boundary. -/
def boundarySupport (P : LogPair k n) : Closeds P.variety.X.left :=
  ⨆ p ∈ P.boundary.support, Closeds.closure ({p.val} : Set P.variety.X.left)

/-- All actual target opens on which this particular map is an isomorphism. -/
def modelIsomorphismOpen {P : LogPair k n} (M : BirationalModel P) :
    M.variety.X.left.Opens :=
  ⨆ (U : P.variety.X.left.Opens)
    (_ : IsIso (M.map.left.resLE U (M.map.left ⁻¹ᵁ U) le_rfl)), M.map.left ⁻¹ᵁ U

/-- Exceptional prime divisors are detected by the actual codimension of their image. -/
def IsExceptional {V W : NormalVariety k n} (f : V.X ⟶ W.X) (p : PrimePoint V) : Prop :=
  Order.coheight (f.left p.val) ≠ 1

/-- A genuine dlt log-resolution witness; its discrepancy values are computed from actual forms. -/
structure DltWitness (P : LogPair k n) where
  coefficients : ∀ p, P.boundary p ≤ 1
  model : BirationalModel P
  [smooth : Smooth model.variety.X.hom]
  crossings : NormalCrossingsModels.IsStrictNormalCrossings model.variety.X
    (Scheme.IdealSheafData.vanishingIdeal
      ((modelIsomorphismOpen model).compl ⊔
        ((Scheme.IdealSheafData.vanishingIdeal (boundarySupport P)).comap model.map.left).support))
  exceptional : ∀ p : PrimePoint model.variety,
    IsExceptional model.map p → 0 < logDiscrepancy model p

/-- A log pair $(X, Δ)$ is dlt if it has a `DltWitness`: its boundary coefficients are at most one,
and it has a proper birational model $Y → X$, with $Y$ smooth over $k$, on which the reduced union
of the locus where $Y → X$ is not an isomorphism over $X$ and the preimage of the support of $Δ$ has
strict normal crossings, and on which every exceptional prime divisor (one whose image does not have
codimension one) has positive log discrepancy. -/
def IsDlt (P : LogPair k n) : Prop := Nonempty (DltWitness P)

/-- Plt tests all actual exceptional divisors and retains coefficient-one original
divisors. As for `IsKlt`, the model calculus is part of the definition, so that
every proper birational normal model enters the quantifier. -/
def IsPlt (P : LogPair k n) : Prop :=
  (∀ p, P.boundary p ≤ 1) ∧ HasModelCalculus P ∧
    ∀ M : BirationalModel P, ∀ p : PrimePoint M.variety,
      IsExceptional M.map p → 0 < logDiscrepancy M p

/-- Actual boundary-preserving flip geometry, independent of a mandatory klt assumption. -/
structure BoundaryFlip {S : Over (Spec (.of k))} {P : LogPair k n}
    {q : P.variety.X ⟶ S} {v : RelativeN1 q} (C : RelativeContraction P q v) where
  source : LogPair k n
  calculus : HasModelCalculus source
  qfactorial : IsQFactorial source.variety
  map : source.variety.X ⟶ C.target
  [proper : IsProper map.left]
  projective : IsHProjectiveOver map
  unit : IsIso (structureUnit map.left)
  small : IsSmall map.left n
  identification : Scheme.PartialIso P.variety.X.left source.variety.X.left
  sourceBig : ∀ p : PrimePoint P.variety, p.val ∈ identification.source
  targetBig : ∀ p : PrimePoint source.variety, p.val ∈ identification.target
  over : identification.iso.hom ≫ identification.target.ι ≫ map.left =
    identification.source.ι ≫ C.map.left
  primeEquiv : PrimePoint P.variety ≃ PrimePoint source.variety
  primeNormalized : ∀ p, (primeEquiv p).val =
    identification.target.ι (identification.iso.hom ⟨p.val, sourceBig p⟩)
  boundary : ∀ p, source.boundary (primeEquiv p) = P.boundary p
  adjointAmple : IsRelativelyAmpleR map source.adjoint

/-- The boundary-preserving flip of `C` underlying a klt flip `F`: the same flipped pair, map,
identification and boundary data, with the model calculus of the flipped pair taken from its klt
condition. -/
def ofKltFlip {S : Over (Spec (.of k))} {P : LogPair k n}
    {q : P.variety.X ⟶ S} {v : RelativeN1 q} {C : RelativeContraction P q v}
    (F : RelativeFlip C) : BoundaryFlip C where
  source := F.source
  calculus := F.klt.1
  qfactorial := F.qfactorial
  map := F.map
  proper := F.proper
  projective := F.projective
  unit := F.unit
  small := F.small
  identification := F.identification
  sourceBig := F.sourceBig
  targetBig := F.targetBig
  over := F.over
  primeEquiv := F.primeEquiv
  primeNormalized := F.primeNormalized
  boundary := F.boundary
  adjointAmple := F.adjointAmple

end MathlibExt.AlgebraicGeometry.DltBoundaryFlipModels
