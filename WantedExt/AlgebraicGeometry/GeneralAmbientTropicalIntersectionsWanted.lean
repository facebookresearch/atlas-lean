/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GeneralAmbientTropicalIntersections

/-!
# General-ambient lifting and the weighted Tor comparison

Osserman--Payne, 1007.1314v3, Theorems 1.2 and 5.1.1, Corollary 5.1.3.
The ambient simple point, local properness, lattice displacement and relevant
minimal-prime components are fixed. Finite-Tor inputs concern only actual local
modules and their lengths; they do not contain the tropical comparison. The weighted comparisons
take `weightVector t` generic in the intersection facet: every minimal-prime component whose
tropicalization passes through it contains the whole facet, so no component meeting the facet only
at a special crossing point is omitted from the relevant components.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.GeneralAmbientTropicalIntersectionsWanted

open MathlibExt.AlgebraicGeometry.FiniteToricCoordinates
open MathlibExt.AlgebraicGeometry.IntegralTropicalCycles
open MathlibExt.AlgebraicGeometry.TropicalCycleIntersections
open MathlibExt.AlgebraicGeometry.TropicalTorIntersection
open MathlibExt.AlgebraicGeometry.GeneralAmbientTropicalIntersections
open MathlibExt.AlgebraicGeometry.ValuativeTropicalization

theorem_wanted proper_general_ambient_lifts
    (K : Type) [Field K] [Valued K NNReal] [IsAlgClosed K] [CompleteSpace K]
    (_nontrivial : NontrivialValuation K) (n : ℕ) (P : AmbientIdeals K n)
    (Y : Presentation K n P.ambient) (A : Presentation K n P.left)
    (B : Presentation K n P.right) (w : RealSpace n)
    (_simple : SimplePoint Y.cycle w) (_proper : ProperIn Y.cycle A.cycle B.cycle w) :
    w ∈ tropicalizationOver (L := K) (P.left ⊔ P.right)

theorem_wanted weighted_Tor_comparison
    (K : Type) [Field K] [Valued K NNReal] [IsAlgClosed K] [CompleteSpace K]
    (_nontrivial : NontrivialValuation K) (n : ℕ) (P : AmbientIdeals K n)
    [IsNoetherianRing P.ambientRing]
    (Y : Presentation K n P.ambient) (A : Presentation K n P.left)
    (B : Presentation K n P.right) (tau : Polyhedron n)
    (_facet : IntersectionFacet Y.cycle A.cycle B.cycle tau)
    (t : Fin n → Kˣ) (_interior : weightVector t ∈ intrinsicInterior ℝ tau.carrier)
    (_adapted : ∀ Z : P.Component,
      weightVector t ∈ tropicalizationOver (L := K) (componentIdeal K n P Z) →
        tau.carrier ⊆ tropicalizationOver (L := K) (componentIdeal K n P Z))
    (S : SimplePoint Y.cycle (weightVector t))
    (_proper : ProperIn Y.cycle A.cycle B.cycle (weightVector t))
    (T : ∀ Z : RelevantComponent K n P tau, P.LocalTor Z.val)
    (C : ∀ Z : RelevantComponent K n P tau,
      _root_.AlgebraicGeometry.IsNoetherian
        (geometricInitialScheme (componentIdeal K n P Z.val) t).left)
    [_root_.AlgebraicGeometry.IsNoetherian (geometricInitialScheme (P.left ⊔ P.right) t).left]
    (v : RealSpace n) (_generic : RelativeGeneric S A.cycle B.cycle v) :
    0 < relativeMultiplicity S A.cycle B.cycle v ∧
      relativeMultiplicity S A.cycle B.cycle v ≤ tropicalMultiplicity (P.left ⊔ P.right) t ∧
      relativeMultiplicity S A.cycle B.cycle v = weightedTorSum K n P tau t T C

theorem_wanted CohenMacaulay_multiplicity_comparison
    (K : Type) [Field K] [Valued K NNReal] [IsAlgClosed K] [CompleteSpace K]
    (_nontrivial : NontrivialValuation K) (n : ℕ) (P : AmbientIdeals K n)
    [IsNoetherianRing P.ambientRing]
    (Y : Presentation K n P.ambient) (A : Presentation K n P.left)
    (B : Presentation K n P.right) (tau : Polyhedron n)
    (_facet : IntersectionFacet Y.cycle A.cycle B.cycle tau)
    (t : Fin n → Kˣ) (_interior : weightVector t ∈ intrinsicInterior ℝ tau.carrier)
    (_adapted : ∀ Z : P.Component,
      weightVector t ∈ tropicalizationOver (L := K) (componentIdeal K n P Z) →
        tau.carrier ⊆ tropicalizationOver (L := K) (componentIdeal K n P Z))
    (S : SimplePoint Y.cycle (weightVector t))
    (_proper : ProperIn Y.cycle A.cycle B.cycle (weightVector t))
    (_CM : ∀ Z : RelevantComponent K n P tau,
      P.CohenMacaulayLeft Z.val ∧ P.CohenMacaulayRight Z.val)
    [_root_.AlgebraicGeometry.IsNoetherian (geometricInitialScheme (P.left ⊔ P.right) t).left]
    (v : RealSpace n) (_generic : RelativeGeneric S A.cycle B.cycle v) :
    tropicalMultiplicity (P.left ⊔ P.right) t = relativeMultiplicity S A.cycle B.cycle v

end WantedExt.AlgebraicGeometry.GeneralAmbientTropicalIntersectionsWanted
