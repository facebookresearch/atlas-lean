/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AnalyticAdicDiamondification
public import MathlibExt.AlgebraicGeometry.PerfectoidSliceSites

/-!
# Normalized analytic-adic diamondification requests

The raw functor, marked-untilt comparison, v-sheafification and relation
kernel map are native prescribed constructions. Requests prove descent,
the exact marked-untilt formula, and a diamond presentation of that
actual sheaf. They do not assume an arbitrary analytic/diamond equivalence.

Source: Scholze, arXiv:1709.07343v4, Proposition 11.3(ii),
Definition 15.5 and Lemma 15.6.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AnalyticDiamondification

open CategoryTheory
open MathlibExt.AlgebraicGeometry.AffinePerfectoidVSite
open MathlibExt.AlgebraicGeometry.AnalyticTateAdicModels
open MathlibExt.AlgebraicGeometry.AnalyticAdicDiamondification
open MathlibExt.AlgebraicGeometry.PerfectoidDiamondModels
open MathlibExt.AlgebraicGeometry.PerfectoidSliceSites

/-- The actual relation-to-quotient-kernel-pair map is invertible. -/
public theorem_wanted relationToKernelIsIso (p : ℕ) [Fact p.Prime] (R : Relation p) :
    IsIso (relationToKernel p R)

/-- The fixed Kan-unit comparison is exactly the marked-untilt isomorphism-class formula. -/
public theorem_wanted markedUntiltingFormula (p : ℕ) [Fact p.Prime]
    (R : AffineRealization p) (Y : AnalyticAdicSpace p) (P : Affine p) :
    Function.Bijective (classComparison (R := R) (Y := Y) P)

/-- The prescribed raw mapping/Kan-extension presheaf already satisfies v-descent. -/
public theorem_wanted rawDiamondIsVSheaf (p : ℕ) [Fact p.Prime]
    (R : AffineRealization p) (Y : AnalyticAdicSpace p) :
    Presheaf.IsSheaf (topology p) ((rawDiamondFunctor p R).obj Y)

/-- Construct a pro-etale relation presentation of the actual fixed diamondification sheaf. -/
public def_wanted analyticDiamondPresentation (p : ℕ) [Fact p.Prime]
    (R : AffineRealization p) (Y : AnalyticAdicSpace p) :
    {D : Diamond p // D.sheaf = (diamondFunctor p R).obj Y}

end WantedExt.AlgebraicGeometry.AnalyticDiamondification
