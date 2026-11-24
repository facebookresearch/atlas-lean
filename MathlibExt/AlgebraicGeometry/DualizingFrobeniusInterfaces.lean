/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BoundaryFrobeniusTraces
public import MathlibExt.AlgebraicGeometry.QuasicoherentDualityReferences

/-!
# Dualizing canonical-divisor references and general Frobenius traces

A canonical divisor is a legitimate chosen divisor whose *actual* O(D)
is identified with restriction of the fixed proper H^(-n)(f!O_k)
from an actual normal compactification. Thus this interface also works
when Kähler top forms do not represent the canonical module over an
imperfect field. No canonical module or trace functional is freely named.

The Frobenius trace is the actual lowest-H0 finite-duality counit after
the prescribed divisorial identification. The boundary inclusion and
index coefficients are fixed actual O(D) operations. The identification
is legitimately defined up to units; its image is the geometric datum.
Generic duality/O(D)/Frobenius producers are completed source integration,
with these exact canonical/divisorial comparisons remaining dependencies.

Sources: Schwede arXiv0901.1154v4, §3 and Theorem 5.2;
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
AlgebraicGeometry/Duality/FiniteTwistedTrace.lean and
FiniteTraceDerivedInternalHomIso.lean, Apache 2.0.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DualizingFrobeniusInterfaces

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.TopologicalSpace
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.BirationalDualityReferences
open MathlibExt.AlgebraicGeometry.FiniteDualityModuleTrace
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.FrobeniusGeometry
open MathlibExt.AlgebraicGeometry.BoundaryFrobeniusTraces
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

open MathlibExt.AlgebraicGeometry.QuasicoherentDualityReferences

variable {k : Type} [Field k] {n : ℕ} (V : NormalVariety k n)
  [∀ p : PrimePoint V, IsDiscreteValuationRing (LocalRing V p.val)]
  [HasDerivedPushforwards.{0}]

/-- Canonical divisor choice tied to the fixed actual dualizing/canonical module. -/
structure CanonicalWeilReference where
  compactification : NormalVariety k n
  inclusion : V.X ⟶ compactification.X
  [openImmersion : IsOpenImmersion inclusion.left]
  dense : Dense (Set.range inclusion.left)
  properReference : ProperReference compactification.X.hom
  divisor : IntegerWeil V
  comparison : DivisorialModuleSheaves.sheaf V divisor ≅
    (Scheme.Modules.pullback inclusion.left).obj (properCanonicalModule properReference n)

/-- The actual untwisted Frobenius canonical divisor. -/
def canonicalTwist (C : CanonicalWeilReference V) (p e : ℕ) : IntegerWeil V :=
  ((1 : ℤ) - (p^e : ℤ)) • C.divisor

/-- Actual boundary-twist coefficients, with admissibility retaining exact integrality. -/
def boundaryTwist (C : CanonicalWeilReference V) (D : RealWeil V) (p e : ℕ) : IntegerWeil V :=
  Finsupp.mapRange Int.floor (by simp)
    (((1 : ℝ) - (p^e : ℝ)) • (realCast C.divisor + D))

variable (C : CanonicalWeilReference V) (p e : ℕ) [Fact p.Prime]
  (hp : IsInCharacteristic V.X.left p)
  [(derivedPushforward (iterated V.X.left p hp e)).IsLeftAdjoint]

/-- Exact source/native Frobenius-duality identification; no concentration is imposed. -/
structure FrobeniusIdentification where
  embedding : FiniteDualityEmbedding (iterated V.X.left p hp e)
  comparison : DivisorialModuleSheaves.sheaf V (canonicalTwist V C p e) ≅
    relativeCanonicalModule (iterated V.X.left p hp e) 0

/-- Exact admissible boundary and proof of local principality, with no new carrier. -/
structure BoundaryIndex (D : RealWeil V) where
  positive : 0 < e
  integral : realCast (boundaryTwist V C D p e) =
    ((1 : ℝ) - (p^e : ℝ)) • (realCast C.divisor + D)
  line : IsLineBundle (DivisorialModuleSheaves.sheaf V (boundaryTwist V C D p e))
  contained : ∀ x, boundaryTwist V C D p e x ≤ canonicalTwist V C p e x

/-- The literal untwisted finite-duality counit after the fixed canonical identification. -/
def untwisted (F : FrobeniusIdentification V C p e hp) :
    (Scheme.Modules.pushforward (iterated V.X.left p hp e)).obj
      (DivisorialModuleSheaves.sheaf V (canonicalTwist V C p e)) ⟶ structureModule V.X.left :=
  (Scheme.Modules.pushforward (iterated V.X.left p hp e)).map F.comparison.hom ≫
    moduleTrace _ F.embedding

/-- Actual boundary trace from the genuine O(D) inclusion and fixed duality counit. -/
def boundaryTrace (D : RealWeil V) (F : FrobeniusIdentification V C p e hp)
    (I : BoundaryIndex V C p e D) :
    (Scheme.Modules.pushforward (iterated V.X.left p hp e)).obj
      (DivisorialModuleSheaves.sheaf V (boundaryTwist V C D p e)) ⟶ structureModule V.X.left :=
  (Scheme.Modules.pushforward (iterated V.X.left p hp e)).map
    (DivisorialModuleSheaves.ofLE V I.contained) ≫ untwisted V C p e hp F

/-- The actual global-section image, including the absolute-Frobenius scalar twist. -/
def traceSectionImage (D : RealWeil V) (F : FrobeniusIdentification V C p e hp)
    (I : BoundaryIndex V C p e D) :=
  LinearMap.range ((GenericSectionMaps.sections V.X).map (boundaryTrace V C p e hp D F I)).hom

end MathlibExt.AlgebraicGeometry.DualizingFrobeniusInterfaces
