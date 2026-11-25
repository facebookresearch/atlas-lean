/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GlobalFFCurveModels
public import MathlibExt.AlgebraicGeometry.GlobalUntiltingDivisorModels
public import MathlibExt.AlgebraicGeometry.AnalyticBundleModifications

/-!
# Normalized relative FF geometry construction requests

All output spaces, sites, rings, section maps, bundle pullbacks and
gluing diagrams are the actual public constructions. Source adapters
reuse the completed generic rational and ringed-gluing primitives.
No v-stack or B(G) classification is supplied as an input.
Source: Fargues--Scholze, arXiv:2102.13459v4, Sections I.2, III.1 and VI.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RelativeFFCurves

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LocalWittCoefficientFields
open MathlibExt.AlgebraicGeometry.LocalCoefficientScalarFrames
open MathlibExt.AlgebraicGeometry.RelativeFarguesFontaineRings
open MathlibExt.AlgebraicGeometry.RelativeFarguesFontaineMaps
open MathlibExt.AlgebraicGeometry.RelativeFFCurveFamilies

variable (p : ℕ) [Fact p.Prime] {E : MixedField p} (C : CoefficientData p E)

/-- The original complete valuation field is the actual uniformizer localization of O_E. -/
public def_wanted localFieldIntegers : IntegerPresentation p C

/-- Integrate actual annular ring/sheaf/Frobenius source maps over the original perfectoid base. -/
public def_wanted annularSource (S : Base p C) : Source p C S

/-- Construct the family on its exact relative annular rings and all original base maps. -/
public def_wanted affineCurveFamily (I : IntegerPresentation p C) : Family p C I

/-- The affine space is the original sheafified representable with its actual residue scalars. -/
public def_wanted affineRelativeBase (S : Base p C) :
    MathlibExt.AlgebraicGeometry.RelativePerfectoidBases.AffineModel p C S

/-- Label the original small open atlas by the same original residue-linear affine pairs. -/
public def_wanted labelledAtlas
    (S : MathlibExt.AlgebraicGeometry.RelativePerfectoidBases.Space p C) :
    MathlibExt.AlgebraicGeometry.RelativePerfectoidBases.LabelledAtlas p C S

/-- Generic source gluing realizes the fixed affine-overlap colimit and every normalized map. -/
public def_wanted globalCurveFamily (I : IntegerPresentation p C) (A : Family p C I) :
    MathlibExt.AlgebraicGeometry.GlobalFFCurveModels.Family p C I A

end WantedExt.AlgebraicGeometry.RelativeFFCurves

namespace WantedExt.AlgebraicGeometry.AnalyticBundlePrestack

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AnalyticGroupTorsorSites
open MathlibExt.AlgebraicGeometry.AnalyticBundlePrestackModels

variable (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
  (G : Over (Spec (.of E))) [GrpObj G]

/-- Actual affine group-scheme points satisfy the original analytic etale sheaf condition. -/
public theorem_wanted groupDescent [IsAffine G.left] (X : ESpace p E) : GroupDescent p E G X

/-- Native restriction on the Over site preserves actual torsor actions. -/
public theorem_wanted torsorRestriction (H : ∀ X : ESpace p E, GroupDescent p E G X) :
    PullbackPreservation p E G H

/-- Bundle the fixed native torsors and pullbacks, with the specified forgetting coherence. -/
public def_wanted bundlePrestack (H : ∀ X : ESpace p E, GroupDescent p E G X)
    (P : PullbackPreservation p E G H) : BundlePrestack p E G H P

end WantedExt.AlgebraicGeometry.AnalyticBundlePrestack

namespace WantedExt.AlgebraicGeometry.UntiltingDivisors

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LocalWittCoefficientFields
open MathlibExt.AlgebraicGeometry.LocalCoefficientScalarFrames
open MathlibExt.AlgebraicGeometry.RelativeFarguesFontaineRings
open MathlibExt.AlgebraicGeometry.RelativeFFCurveFamilies
open MathlibExt.AlgebraicGeometry.AnalyticTateAdicModels
open MathlibExt.AlgebraicGeometry.MarkedUntiltingPeriodModels

variable (p : ℕ) [Fact p.Prime] {E : MixedField p} (C : CoefficientData p E)
  (R : AffineRealization p) {S : Base p C} (T : Untilting p C S)

/-- The actual perfectoid diamond comparison fixes the original marked Kan-unit point. -/
public def_wanted untiltTiltComparison :
    MathlibExt.AlgebraicGeometry.UntiltingCartierModels.TiltComparison p C R T

/-- The original finite local-field scalars have their theta- and Cohen-normalized lift. The
untilt lies over `E`: its integral `E`-action agrees after theta with the marked residue action on
the Cohen--Witt scalars (`Untilting.residue_compatible`), which the lift extends. -/
public def_wanted scalarLift : ScalarLift p C S T

/-- Compare the actual relative theta-kernel completion to native B_dR-plus at every level. -/
public def_wanted relativePeriodCompletion (L : ScalarLift p C S T) :
    MathlibExt.AlgebraicGeometry.MarkedUntiltingPeriodModels.CompletionComparison p C T L

/-- The modification parameter generates the actual first filtration ideal and is regular. -/
public def_wanted filtrationParameter (L : ScalarLift p C S T) : Parameter p C T L

variable (I : IntegerPresentation p C) (A : Family p C I)

/-- Divisor of an untilt on a relative Fargues–Fontaine curve: for a prime $p$, a
mixed-characteristic local field $E$ with coefficient data $C$ and integer presentation $I$, a
given realization $R$ of affinoid perfectoid spaces as analytic adic spaces
(`AffineRealization`), a family $A$ of relative curves over perfectoid bases (`Family`), a
perfectoid base $S$ of characteristic $p$ and an untilt $T$ of $S$: a closed Cartier map from the
untilt to the relative curve of $A$ over $S$ (`UntiltingCartierModels.Divisor`), together with a
cover of the untilt by period charts in each of which the completion along the divisor is
identified with $B_{dR}^+$ compatibly with the coefficients, with θ and with the filtration
(`SourceDivisor`). -/
public def_wanted affineUntiltingDivisor
    (p : ℕ) [Fact p.Prime] {E : MixedField p} (C : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p C) (A : Family p C I)
    {S : Base p C} (T : Untilting p C S) :
    MathlibExt.AlgebraicGeometry.UntiltingCartierChartModels.SourceDivisor p C R I A T

private def check_affineUntiltingDivisor :
    DefWanted
      (MathlibExt.AlgebraicGeometry.UntiltingCartierChartModels.SourceDivisor p C R I A T) :=
  affineUntiltingDivisor p C R I A T

variable (F : MathlibExt.AlgebraicGeometry.GlobalFFCurveModels.Family p C I A)
  (B : MathlibExt.AlgebraicGeometry.RelativePerfectoidBases.Space p C)

/-- An existing actual global untilt determines its degree-one Cartier divisor. -/
public def_wanted globalUntiltingDivisor
    (U : MathlibExt.AlgebraicGeometry.GlobalUntiltingDivisorModels.UntiltingModel p C R I A F B) :
    MathlibExt.AlgebraicGeometry.GlobalUntiltingDivisorModels.UntiltingImage p C R I A F B U

private def check_globalUntiltingDivisor
    (U : MathlibExt.AlgebraicGeometry.GlobalUntiltingDivisorModels.UntiltingModel p C R I A F B) :
    DefWanted
      (MathlibExt.AlgebraicGeometry.GlobalUntiltingDivisorModels.UntiltingImage p C R I A F B U) :=
  globalUntiltingDivisor p C R I A F B U

end WantedExt.AlgebraicGeometry.UntiltingDivisors

namespace WantedExt.AlgebraicGeometry.AnalyticCartierPunctures

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AnalyticGroupTorsorSites

/-- Complement of a closed subspace: for a prime $p$, a field $E$ and a morphism $d : D → X$ of
analytic adic spaces over $E$ whose underlying map is a closed embedding: a puncture of $d$
(`Puncture`), that is, a space over $E$ with a map to $X$ that is an open embedding inducing
isomorphisms on stalks, whose image is the complement of the image of $d$. -/
public def_wanted puncture (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] {X D : ESpace p E} (d : D ⟶ X)
    (h : Topology.IsClosedEmbedding d.left.hom.val.base) :
    MathlibExt.AlgebraicGeometry.AnalyticBundleModifications.Puncture p E d

end WantedExt.AlgebraicGeometry.AnalyticCartierPunctures
