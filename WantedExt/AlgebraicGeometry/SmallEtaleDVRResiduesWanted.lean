/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SmallEtaleDVRResidues
public import Batteries.Util.ProofWanted

/-!
# Geometric DVR purity with actual Tate coefficients and Kummer orientation

Schreieder, arXiv1801.05397v5, §2.3.
The coefficient prime is invertible in the actual DVR. All localization
models represent the computed native restriction. The constructor
returns actual mapping-cone comparisons, not an arbitrary residue map.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.SmallEtaleDVRResidues

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.SmallEtaleTorsionCoefficients
open MathlibExt.AlgebraicGeometry.SmallEtaleCohomologySystem

def_wanted geometricDvrPurity
    [AllSheafificationSources] [AllContinuousSources]
    [AllDerivedSectionsSources] [AllDerivedPushSources]
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [HasExt.{2} (Coefficients (Spec (.of K)))]
    (l : ℕ) [Fact l.Prime] (invertible : IsUnit (l : R)) (S : Data l)
    (M : ∀ j : ℕ, LocalizationModel S (genericMap (R := R) (K := K)) (j+1)) :
    OrientedResidues S M

end MathlibExt.AlgebraicGeometry.SmallEtaleDVRResidues
