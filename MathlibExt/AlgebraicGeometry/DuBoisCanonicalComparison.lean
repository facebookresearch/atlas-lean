/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EmbeddedDuBoisZero
public import MathlibExt.AlgebraicGeometry.DerivedInternalHom
public import MathlibExt.AlgebraicGeometry.FiniteDualityModuleTrace
public import MathlibExt.AlgebraicGeometry.QuasicoherentDualityReferences
public import MathlibExt.AlgebraicGeometry.DivisorialModuleSheaves
public import MathlibExt.AlgebraicGeometry.NaturalPullbackMultiplierModules
public import MathlibExt.AlgebraicGeometry.DualizingFrobeniusInterfaces

/-!
# Actual Du Bois canonical comparison and log-resolution pushforward

The exceptional divisor is the reduced sum of actual exceptional prime
divisors, detected by codimension of their image. The log-canonical module
is the completed O_Y(K_Y+G), and its pushforward map is fixed on every
rational top-form section by the genuine generic field isomorphism.

The embedded Du Bois object/unit is transported through an actual
scheme isomorphism. Its dual-unit arrow is precomposition with that unit
on the derived internal Hom (`DerivedInternalHom.precomp`). Comparison is
requested only in degree -dim X, not as an unjustified isomorphism of
entire complexes.

Cohen--Macaulayness is `RationalResolution.IsCohenMacaulayStalkwise`
(local Ext-depth equals Krull dimension at every point).
The proper dualizing object is the fixed right adjoint on QCoh-derived,
with no all-module/nonproper dualizing shortcut.
Reference: Kovács--Schwede--Smith, arXiv0801.1541v3, §2.B and Theorem 1.1.
Generic duality and canonical/divisor constructions are completed
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b integration
(AlgebraicGeometry/Duality, Apache 2.0).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DuBoisCanonicalComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.RationalResolution
open MathlibExt.AlgebraicGeometry.PrincipalizationModels
open MathlibExt.AlgebraicGeometry.EmbeddedDuBoisZero
open MathlibExt.AlgebraicGeometry.BirationalDualityReferences
open MathlibExt.AlgebraicGeometry.FiniteDualityModuleTrace
open MathlibExt.AlgebraicGeometry.QuasicoherentDualityReferences
open MathlibExt.AlgebraicGeometry.RationalFunctionModules
open MathlibExt.AlgebraicGeometry.DerivedInternalHom
open MathlibExt.AlgebraicGeometry.NaturalPullbackMultiplierModules
open MathlibExt.AlgebraicGeometry.DualizingFrobeniusInterfaces
attribute [local instance] HasDerivedCategory.standard
open scoped BigOperators

variable {k : Type} [Field k] {n : ℕ}

/-- The reduced exceptional divisor contains exactly the actual exceptional prime points: the
prime divisors whose image is not a prime divisor, that is, has codimension other than one
(`Order.coheight` is codimension, since points of a scheme are ordered by specialization). -/
structure ReducedExceptional {V : NormalVariety k n} {KX : CanonicalData V}
    (M : CanonicalModel V KX) where
  support : Finset (PrimePoint M.variety)
  normalized : ∀ p, p ∈ support ↔ Order.coheight (M.map.left p.val) ≠ 1

def reducedExceptionalDivisor {V : NormalVariety k n} {KX : CanonicalData V}
    {M : CanonicalModel V KX}
    (G : ReducedExceptional M) : IntegerWeil M.variety :=
  ∑ p ∈ G.support, Finsupp.single p 1

variable [HasDerivedPushforwards.{0}] [HasDerivedPullbacks.{0}] [HasDerivedTensors.{0}]

def logCanonicalModule {V : NormalVariety k n} {KX : CanonicalData V}
    (M : CanonicalModel V KX) (G : ReducedExceptional M)
    [∀ p : PrimePoint M.variety, IsDiscreteValuationRing (LocalRing M.variety p.val)] :=
  DivisorialModuleSheaves.sheaf M.variety
    (canonicalDivisor M.canonical + reducedExceptionalDivisor G)

/-- The log-canonical pushforward map is fixed by rational section inclusion, not a free trace. -/
structure LogCanonicalPushforward (V : NormalVariety k n) (KX : CanonicalData V)
    (M : CanonicalModel V KX)
    (G : ReducedExceptional M)
    [∀ p : PrimePoint V, IsDiscreteValuationRing (LocalRing V p.val)]
    [∀ p : PrimePoint M.variety, IsDiscreteValuationRing (LocalRing M.variety p.val)] where
  map : (Scheme.Modules.pushforward M.map.left).obj (logCanonicalModule M G) ⟶
    DivisorialModuleSheaves.sheaf V (canonicalDivisor KX)
  normalized : ∀ (U : V.X.left.Opens) [Nonempty U]
    (s : Γ((Scheme.Modules.pushforward M.map.left).obj (logCanonicalModule M G),U)),
    letI := fractionAlgebra V
    letI := fractionAlgebra M.variety
    letI : Nonempty (M.map.left ⁻¹ᵁ U) :=
      ⟨⟨genericPoint M.variety.X.left, by
        change M.map.left (genericPoint M.variety.X.left) ∈ U
        rw [M.generic]
        exact genericPoint_mem U⟩⟩
    rationalFunctionsEquiv U
      ((DivisorialModuleSheaves.inclusion V (canonicalDivisor KX)).app U
        (map.app U s)) =
    M.fieldIso.symm
      (rationalFunctionsEquiv (M.map.left ⁻¹ᵁ U)
        ((DivisorialModuleSheaves.inclusion M.variety
          (canonicalDivisor M.canonical + reducedExceptionalDivisor G)).app
            (M.map.left ⁻¹ᵁ U) s))

/-- Actual identification of an embedded reduced scheme with the normal variety. -/
abbrev EmbeddedIdentification (V : NormalVariety k n) {S : Over (Spec (.of k))}
    (I : S.left.IdealSheafData) := V.X ≅ Over.mk (I.subschemeι ≫ S.hom)

def embeddedObject (V : NormalVariety k n) {S : Over (Spec (.of k))}
    {I : S.left.IdealSheafData} {R : Principalization S I}
    (F : ExceptionalMap R) (e : EmbeddedIdentification V I) : D V.X.left :=
  (derivedPushforward e.inv.left).obj (duBoisZero F)

def embeddedUnit (V : NormalVariety k n) {S : Over (Spec (.of k))}
    {I : S.left.IdealSheafData} {R : Principalization S I}
    (F : ExceptionalMap R) (e : EmbeddedIdentification V I) :
    derivedUnit V.X.left ⟶ embeddedObject V F e :=
  (DerivedCategory.singleFunctor V.X.left.Modules 0).map (structureUnit e.inv.left) ≫
    sheafPushforwardUnit e.inv.left (structureModule I.subscheme) ≫
      (derivedPushforward e.inv.left).map (duBoisUnit F)

/-- Actual dualizing complex restricted from the fixed proper normal compactification. -/
def canonicalDualizing (V : NormalVariety k n)
    [∀ p : PrimePoint V, IsDiscreteValuationRing (LocalRing V p.val)]
    (D : CanonicalWeilReference V) : FourierMukai.D V.X.left :=
  (derivedPullback D.inclusion.left).obj (properDuality D.properReference)

/-- Desired normalized degree-minus-dimension dual-unit comparison on the actual modules. -/
structure CanonicalComparison (V : NormalVariety k n) (KX : CanonicalData V)
    (M : CanonicalModel V KX)
    (G : ReducedExceptional M)
    [∀ p : PrimePoint V, IsDiscreteValuationRing (LocalRing V p.val)]
    [∀ p : PrimePoint M.variety, IsDiscreteValuationRing (LocalRing M.variety p.val)]
    (C : LogCanonicalPushforward V KX M G)
    {S : Over (Spec (.of k))} {I : S.left.IdealSheafData} {R : Principalization S I}
    (F : ExceptionalMap R) (e : EmbeddedIdentification V I)
    (D : CanonicalWeilReference V) (canonicalNormalized : D.divisor = canonicalDivisor KX)
    [((derivedTensor V.X.left).obj (embeddedObject V F e)).IsLeftAdjoint]
    [((derivedTensor V.X.left).obj (derivedUnit V.X.left)).IsLeftAdjoint] where
  source : (Scheme.Modules.pushforward M.map.left).obj (logCanonicalModule M G) ≅
    (DerivedCategory.homologyFunctor V.X.left.Modules (-(n : ℤ))).obj
      (internalHom V.X.left (embeddedObject V F e) (canonicalDualizing V D))
  target : DivisorialModuleSheaves.sheaf V (canonicalDivisor KX) ≅
    (DerivedCategory.homologyFunctor V.X.left.Modules (-(n : ℤ))).obj
      (internalHom V.X.left (derivedUnit V.X.left) (canonicalDualizing V D))
  unit_normalized : C.map ≫ target.hom =
    source.hom ≫ (DerivedCategory.homologyFunctor V.X.left.Modules (-(n : ℤ))).map
      (precomp (embeddedUnit V F e) (canonicalDualizing V D))

end MathlibExt.AlgebraicGeometry.DuBoisCanonicalComparison
