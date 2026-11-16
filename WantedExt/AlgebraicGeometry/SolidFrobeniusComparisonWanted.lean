/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Condensed.SolidOverconvergentRHModels
public import MathlibExt.Condensed.DiamondEtaleCoefficientOperations

/-!
# Actual Frobenius and overconvergent coefficient construction requests

The residue ring is the given untilt's A-plus/pi, with pi dividing p.
Frobenius is its literal p-th-power map. Geometric extension, the
coefficient unit, all module actions, full mapping fibres and the Hom
adjunction are normalized against the prescribed native source maps.

The local source is the actual Fp function ring on a strictly totally
disconnected original chart. Full faithfulness and the perfect-object
equivalence are separate theorem requests. Overconvergence uses the
actual geometric-point derived adjunction unit.

Sources: Mann, arXiv:2206.02022v1, Theorem 1.2.7,
Definitions 3.7.1(c), 3.9.10, 3.9.17 and 3.9.21;
Anschuetz--Mann, arXiv:2403.01951v2, Remark 4.5.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.SolidFrobeniusComparison

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry
open MathlibExt.Condensed.LocalSolidCoefficientModels
open MathlibExt.Condensed.SolidTorsionFrobeniusModels
open MathlibExt.Condensed.SolidWeakPerfectModels
open MathlibExt.Condensed.FrobeniusModuleHomModels
open MathlibExt.Condensed.FrobeniusCoefficientUnit
open MathlibExt.Condensed.SolidFpScalarModels
open MathlibExt.Condensed.SolidOverconvergentRHModels

variable (p : ℕ) [Fact p.Prime] (P : AffineUntilting p)
  (π : Pseudouniformizer p P) (h : π.element ∣ (p : P.pair.plus))

/-- The actual torsion analytic compact model, with no additional completed-modification layer. -/
public def_wanted torsionCoefficients : TorsionModel p P π

/-- Frobenius scalar extension is normalized against actual native derived geometric extension. -/
public def_wanted normalizedFrobenius (M : TorsionModel p P π) :
    {F : FrobeniusModel p P π h M // IsGeometricallyNormalized p P π F}

/-- The discrete unit induction has the actual coefficient-unit
realization and full Hom adjunction. -/
public def_wanted discreteUnitInduction (M : TorsionModel p P π) :
    UnitInductionModel p P π M

/-- The compact linearization is fixed by the actual geometric unit mate. -/
public def_wanted compactFrobeniusUnit (M : TorsionModel p P π)
    (F : FrobeniusModel p P π h M) (hF : IsGeometricallyNormalized p P π F)
    (U : UnitInductionModel p P π M) : CompactUnit p P π h M F U

/-- The actual almost-local coefficient phi unit retains its
localization and linearization square. -/
public def_wanted almostFrobeniusUnit (M : TorsionModel p P π)
    (F : FrobeniusModel p P π h M) (U : UnitInductionModel p P π M)
    (A : CompactUnit p P π h M F U) : AlmostUnit p P π h M F U A

/-- The enhancement fixes complete native fibre Homs and every signed composition component. -/
public def_wanted phiEnhancement (M : TorsionModel p P π)
    (F : FrobeniusModel p P π h M) : Enhancement p P π h M F

/-- The actual clopen-idempotent coefficient map on a qualified disconnected chart. -/
public def_wanted localFpScalars (hP : IsStrictlyTotallyDisconnected p P) :
    FpScalarModel p P π

variable (M : TorsionModel p P π) (F : FrobeniusModel p P π h M)
  (E : Enhancement p P π h M F) (U : UnitInductionModel p P π M)
  (A : CompactUnit p P π h M F U) (V : AlmostUnit p P π h M F U A)
  (S : FpScalarModel p P π)

/-- The coefficient-unit functor has its actual scalar first component
and zero homotopy component. -/
public def_wanted fpUnitFunctor : UnitFunctor p P π h M F E U A V S

variable (B : UnitFunctor p P π h M F E U A V S)

/-- The right adjoint is literal Hom from the fixed unit, with all original postcomposition maps. -/
public def_wanted fpUnitHomFunctor : UnitHomFunctor p P π h M F B

variable (R : UnitHomFunctor p P π h M F B)

/-- Construct the full local RH adjunction to the prescribed unit-Hom functor. -/
public def_wanted localRH (hP : IsStrictlyTotallyDisconnected p P) :
    RHPModel p P π h M F B R

variable (L : RHPModel p P π h M F B R)

/-- The actual local RH Hom maps are quasi-isomorphisms in all degrees. -/
public theorem_wanted localRHFullyFaithful (hP : IsStrictlyTotallyDisconnected p P) :
    IsFullyFaithful p P π h M F L

/-- Perfect discrete local Fp modules have weakly almost perfect actual underlying phi modules. -/
public theorem_wanted localRHPerfect (hP : IsStrictlyTotallyDisconnected p P) :
    PreservesPerfect p P π h M F L

/-- Every source-perfect phi object is in the actual perfect Fp comparison image. -/
public theorem_wanted localRHEssentiallyPerfect (hP : IsStrictlyTotallyDisconnected p P) :
    IsEssentiallyPerfect p P π h M F L

/-- Native etale operations retain the full original cochain unit square. -/
public def_wanted etaleCoefficientOperations
    {X Y : MathlibExt.AlgebraicGeometry.AffinePerfectoidVSite.VSheaf p} (f : X ⟶ Y) :
    MathlibExt.Condensed.DiamondEtaleCoefficientOperations.OperationModel p f

end WantedExt.AlgebraicGeometry.SolidFrobeniusComparison
