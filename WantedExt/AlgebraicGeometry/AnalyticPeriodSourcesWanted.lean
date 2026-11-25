/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AnalyticBaseWittScalarSources
public import MathlibExt.AlgebraicGeometry.AnalyticCoefficientPeriodScalars
public import MathlibExt.CategoryTheory.StructuralPeriodConnectionSources

/-!
# Direct construction and proof requests for actual analytic period sources

Each request is a direct Batteries Wanted declaration for one original
object, map or source theorem. All period rings and filtrations are the
constructed native sheaves in MathlibExt. Provider proofs are deferred;
there is no request for a replacement period ring or a final comparison
oracle, and no global theta generator or integral rational-system lattice. The pro-object point
realization and the continuity of the étale inclusion are requested by
`AnalyticProObjectSitesWanted` (`actualProObjectPoints`, `etaleInclusionContinuous`), not again
here.

Sources: Scholze, arXiv:1205.3463v2, Definitions 3.9, 6.1, 6.8 and 8.1;
Bhatt--Morrow--Scholze, arXiv:1602.03148v3, Section 5.1.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AnalyticPeriodSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MathlibExt.AlgebraicGeometry
open AnalyticTateAdicModels AnalyticProperSmoothSources GeneralPadicCoefficientFields
open AnalyticProEtaleCoefficientSources AnalyticCoefficientPeriodScalars AnalyticBaseWittScalarSources
open MathlibExt.CategoryTheory
open UntiltingSheafSources WittStructuralScalarBindings SheafLocalGeneratorLocalization

variable (p : ℕ) [Fact p.Prime]

/-- Realize the original field, integers, topology and all-rank Spa points. -/
public def_wanted baseRealization (K : BaseField p) : BaseRealization p K

/-- The actual finite restricted-series Tate algebra and its coefficient-uniform topology. -/
public def_wanted tatePowerSeries (P : TatePair p) (n : ℕ) : TatePowerSeries p P n

section AnalyticSpace

variable (X : AnalyticAdicSpace p) (hX : AnalyticProObjectSites.IsLocallyNoetherian p X)

include hX

public def_wanted integralStructure (hNoeth : AnalyticProObjectSites.IsLocallyNoetherian p X) : IntegralStructure p X

public theorem_wanted regularEtaleSheaf (hNoeth : AnalyticProObjectSites.IsLocallyNoetherian p X) :
  Presheaf.IsSheaf (AnalyticDiamondEtaleSites.analyticEtaleTopology p X) (etaleRingsLarge p X)

public theorem_wanted positiveEtaleSheaf (hNoeth : AnalyticProObjectSites.IsLocallyNoetherian p X) (I : IntegralStructure p X) :
  Presheaf.IsSheaf (AnalyticDiamondEtaleSites.analyticEtaleTopology p X) (I.presheaf ⋙ liftRings)

variable (P : AnalyticProObjectSites.PointRealization p X)

section RingSources

variable [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X) CommRingCat.{1}]
  [HasSheafify (proTopology p X P) CommRingCat.{1}]
  [(etaleInclusion p X).IsContinuous
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X) (proTopology p X P)]
  [((etaleInclusion p X).sheafPushforwardContinuous CommRingCat.{1}
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X) (proTopology p X P)).IsRightAdjoint]

/-- The native constant inverse-image map; its construction already lives in MathlibExt. -/
public theorem_wanted constantInverseImageIso (hNoeth : AnalyticProObjectSites.IsLocallyNoetherian p X) (R : Type) [CommRing R] :
  IsIso (NativeRingInverseImages.constantInverseMap
    (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p X) (T := proTopology p X P)
      (etaleInclusion p X) R)

variable (I : IntegralStructure p X)
  (hI : Presheaf.IsSheaf (AnalyticDiamondEtaleSites.analyticEtaleTopology p X) (I.presheaf ⋙ liftRings))

/-- Sharp/theta on the actual original positive ring, normalized by all local lifts and Witt coordinates. -/
public def_wanted untiltingSource (hNoeth : AnalyticProObjectSites.IsLocallyNoetherian p X) : UntiltingData p (originalPositive p X P I hI)

public def_wanted primeTiltSource (hNoeth : AnalyticProObjectSites.IsLocallyNoetherian p X) : PrimeTiltSource p X P (originalPositive p X P I hI)

public def_wanted integralWittSource (hNoeth : AnalyticProObjectSites.IsLocallyNoetherian p X) (S : PrimeTiltSource p X P (originalPositive p X P I hI)) :
  IntegralWittSource p X P (originalPositive p X P I hI) S

/-- Full Qhat is the sheafified p-inversion; no global lattice is a parameter. -/
public def_wanted rationalInversionSource (hNoeth : AnalyticProObjectSites.IsLocallyNoetherian p X) : RationalInversionSource p X P

public theorem_wanted absoluteThetaLine (hNoeth : AnalyticProObjectSites.IsLocallyNoetherian p X)
    (A : UntiltingData p (originalPositive p X P I hI)) :
  IsLocallyThetaLine A.deRhamPositive (completedRegular p (originalPositive p X P I hI)) A.completedTheta

end RingSources

end AnalyticSpace

section BaseScalars

variable (K : BaseField p) (B : BaseRealization p K) (Z : Over B.analytic)
  (Q : AnalyticProObjectSites.PointRealization p Z.left)
  (I : IntegralStructure p Z.left)
  (hI : Presheaf.IsSheaf (AnalyticDiamondEtaleSites.analyticEtaleTopology p Z.left) (I.presheaf ⋙ liftRings))
  [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p Z.left) CommRingCat.{1}]
  [HasSheafify (proTopology p Z.left Q) CommRingCat.{1}]
  [(etaleInclusion p Z.left).IsContinuous
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p Z.left) (proTopology p Z.left Q)]
  [((etaleInclusion p Z.left).sheafPushforwardContinuous CommRingCat.{1}
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p Z.left) (proTopology p Z.left Q)).IsRightAdjoint]

public def_wanted cohenWittSource : CohenWittSource p K

public def_wanted cohenEtaleSource (C : CohenWittSource p K) :
  CohenEtaleSource p K B Z I hI C

variable [IsIso (NativeRingInverseImages.constantInverseMap
  (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p Z.left) (T := proTopology p Z.left Q)
  (etaleInclusion p Z.left) (WittVector p (BaseField.residueField p K)))]
  (C : CohenWittSource p K) (S : CohenEtaleSource p K B Z I hI C)

public def_wanted qualifiedResidueSource
    (hZ : AnalyticProObjectSites.IsLocallyNoetherian p Z.left) :
  QualifiedResidueSource p K B Z Q I hI C S

public def_wanted originalRegularLocalization
    (hO : Presheaf.IsSheaf (AnalyticDiamondEtaleSites.analyticEtaleTopology p Z.left) (etaleRingsLarge p Z.left)) :
  RegularLocalizationSource p (originalStructure p Z.left Q hO) (originalPositive p Z.left Q I hI)
    (AnalyticBaseWittScalarSources.positiveInclusion p K B Z Q I hI hO)

public theorem_wanted originalWittThetaSquare
    (hO : Presheaf.IsSheaf (AnalyticDiamondEtaleSites.analyticEtaleTopology p Z.left) (etaleRingsLarge p Z.left))
    (R : QualifiedResidueSource p K B Z Q I hI C S)
    (L : RegularLocalizationSource p (originalStructure p Z.left Q hO) (originalPositive p Z.left Q I hI)
      (AnalyticBaseWittScalarSources.positiveInclusion p K B Z Q I hI hO))
    (A : UntiltingData p (originalPositive p Z.left Q I hI)) :
  ResidueScalarSource.ScalarSquare (p := p) (K := K)
    (O := originalStructure p Z.left Q hO) (Rplus := originalPositive p Z.left Q I hI)
    (positiveInclusion := AnalyticBaseWittScalarSources.positiveInclusion p K B Z Q I hI hO)
    (S := R.residue) L A

end BaseScalars

end WantedExt.AlgebraicGeometry.AnalyticPeriodSources
