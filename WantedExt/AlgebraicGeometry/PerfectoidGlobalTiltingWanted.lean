/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PerfectoidUntiltingSites

/-!
# Fixed relative tilting and rational/site comparison requests

All carriers, local ring maps, rational coefficient maps and sheaf
units/counits are already prescribed publicly. The source is a fixed
perfectoid field untilt for the equivalence statements. In particular,
no equivalence of sites or inverse global functor is assumed as input.

Sources: Scholze, arXiv:1111.4914v1, Theorems 1.7--1.11, 6.3 and 7.12;
arXiv:1709.07343v4, Theorem 3.12 and Definition 8.1.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.PerfectoidGlobalTilting

open CategoryTheory
open MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry
open MathlibExt.AlgebraicGeometry.PerfectoidRationalTilting
open MathlibExt.AlgebraicGeometry.PerfectoidUntiltingSites
open MathlibExt.AlgebraicGeometry.IntegralTiltModels
open MathlibExt.AlgebraicGeometry.AffinePerfectoidVSite

/-- Tilting a rational localization (Scholze, *Perfectoid spaces*, Theorem 6.3): let $p$ be a prime,
$P$ an affine perfectoid untilt, and $D$ a rational localization of $P$ whose numerators are the
images under $\sharp$ of a finite set $T$, and whose denominator is the image under $\sharp$ of an
element $s$, of the tilt of the ring of power-bounded elements of $P$ (`IntegralRing`). Then there
are a rational localization of the tilt of $P$ at the images of $T$ and $s$ in the tilt, and an
isomorphism from the tilt of $D$ to it compatible with the maps to the tilt of $P$
(`RationalTiltComparison`). -/
public def_wanted rationalTiltComparison (p : ℕ) [Fact p.Prime]
    (P : AffineUntilting p) (D : OriginalRationalModel p P)
    (T : Finset (IntegralRing p P.pair)) (s : IntegralRing p P.pair)
    (hT : (D.numerators : Set P.pair.ring) =
      sharp p P.pair '' (T : Set (IntegralRing p P.pair)))
    (hs : D.denominator = sharp p P.pair s) : RationalTiltComparison p P D T s

/-- The tilting equivalence over a perfectoid field: let $p$ be a prime and $K$ an affine perfectoid
untilt whose ring is a field. Then there is an equivalence of categories, from affine perfectoid
untilts over $K$ to affine perfectoid pairs of characteristic $p$ over the tilt of $K$, whose
functor is relative tilting (`relativeTilting`). -/
public def_wanted relativeTiltingEquivalence (p : ℕ) [Fact p.Prime]
    (K : AffineUntilting p) (_hK : IsField K.pair.ring) :
    {e : RelativeAffine p K ≌ Over K.tilt.pair // e.functor = relativeTilting p K}

/-- Relative tilting is continuous for the v-topologies: let $p$ be a prime and $K$ an affine
perfectoid untilt whose ring is a field. Then the relative tilting functor, from affine perfectoid
untilts over $K$, with the v-topology of covers of their original spaces, to affine perfectoid pairs
of characteristic $p$ over the tilt of $K$, with the v-topology, is continuous. -/
public theorem_wanted relativeTiltingContinuous (p : ℕ) [Fact p.Prime]
    (K : AffineUntilting p) (_hK : IsField K.pair.ring) :
    (relativeTilting p K).IsContinuous (relativeVTopology p K)
      ((topology p).over K.tilt.pair)

/-- Tilting preserves étale maps: for a prime $p$, the tilt of every étale map of affine perfectoid
untilts is étale. -/
public theorem_wanted tiltingPreservesEtale (p : ℕ) [Fact p.Prime] : PreservesEtale p

/-- Tilting preserves pro-étale maps: for a prime $p$, the tilt of every pro-étale map of affine
perfectoid untilts is pro-étale. -/
public theorem_wanted tiltingPreservesProEtale (p : ℕ) [Fact p.Prime] :
    PreservesProEtale p

/-- The tilting unit is an isomorphism: let $p$ be a prime and $K$ an affine perfectoid untilt whose
ring is a field, and assume the relative tilting functor continuous for the v-topologies and
restriction of sheaves along it (`untiltSheaves`) a right adjoint, with left adjoint `tiltSheaves`.
Then for every v-sheaf of sets $F$ on affine perfectoid untilts over $K$, the unit
$F \to \mathrm{untilt}(\mathrm{tilt}\,F)$ of this adjunction is an isomorphism. -/
public theorem_wanted globalTiltingUnitIsIso (p : ℕ) [Fact p.Prime]
    (K : AffineUntilting p) (_hK : IsField K.pair.ring)
    [(relativeTilting p K).IsContinuous (relativeVTopology p K)
      ((topology p).over K.tilt.pair)]
    [(untiltSheaves p K).IsRightAdjoint]
    (F : Sheaf (relativeVTopology p K) (Type 1)) : IsIso ((tiltingUnit p K).app F)

/-- The tilting counit is an isomorphism: let $p$ be a prime and $K$ an affine perfectoid untilt
whose ring is a field, and assume the relative tilting functor continuous for the v-topologies and
restriction of sheaves along it (`untiltSheaves`) a right adjoint, with left adjoint `tiltSheaves`.
Then for every v-sheaf of sets $F$ on affine perfectoid pairs of characteristic $p$ over the tilt of
$K$, the counit $\mathrm{tilt}(\mathrm{untilt}\,F) \to F$ of this adjunction is an isomorphism. -/
public theorem_wanted globalTiltingCounitIsIso (p : ℕ) [Fact p.Prime]
    (K : AffineUntilting p) (_hK : IsField K.pair.ring)
    [(relativeTilting p K).IsContinuous (relativeVTopology p K)
      ((topology p).over K.tilt.pair)]
    [(untiltSheaves p K).IsRightAdjoint]
    (F : Sheaf ((topology p).over K.tilt.pair) (Type 1)) :
    IsIso ((tiltingCounit p K).app F)

end WantedExt.AlgebraicGeometry.PerfectoidGlobalTilting
