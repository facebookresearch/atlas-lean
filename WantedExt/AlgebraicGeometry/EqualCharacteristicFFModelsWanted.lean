/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.EqualCharacteristicFFAnalyticModels

/-!
# Native equal-characteristic relative FF construction requests

Fargues--Scholze, arXiv:2102.13459v4, Definition I.2.2 and Section II.1.
The source coefficient field is the actual k((t)) for finite k, and
the original integral period ring is R+[[t]]. Actual t, varpi, q-power
coefficient Frobenius, rational maps and all-rank valuation spectra are
fixed by the public definitions. The annular/quotient sheaf dictionaries
retain every original coefficient, open and native structure-presheaf map.

These requests do not replace the remaining relative family, marked
untilt/meromorphic Hecke, reflex-extension or native B(G) comparisons.
The coefficient field and period-ring diagrams are actual construction
inputs, with no mixed Witt substitute for this equal-characteristic case.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.EqualCharacteristicFFModels

open MathlibExt.AlgebraicGeometry.EqualCharacteristicCoefficientModels
open MathlibExt.AlgebraicGeometry.EqualCharacteristicFFRingModels
open MathlibExt.AlgebraicGeometry.EqualCharacteristicFFSheafModels
open MathlibExt.AlgebraicGeometry.EqualCharacteristicFFAnalyticModels

/-- The actual finite-residue Laurent-series field is a nonarchimedean local field. -/
public theorem_wanted laurentSeriesLocalField
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Fintype k] :
    letI := valuativeRelation k
    IsNonarchimedeanLocalField (CoefficientField k)

/-- Construct the original coefficient-normalized equal-characteristic rational maps. -/
public def_wanted rationalRestrictionDictionary
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Fintype k]
    (C : ResidueData p k) (S : Base p k C) : RationalRestrictions p k C S

/-- Construct actual point Frobenius on the original all-rank annular spectrum. -/
public def_wanted annularFrobeniusPoints
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Fintype k]
    (C : ResidueData p k) (S : Base p k C) : FrobeniusPoints p k C S

/-- Construct the real annular sheaf of the actual completed rational rings. -/
public def_wanted annularPeriodSheaf
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Fintype k]
    (C : ResidueData p k) (S : Base p k C) [D : RationalRestrictions p k C S] :
    PeriodSheaf p k C S

/-- Construct Frobenius on all original rational-chart rings and restrictions. -/
public def_wanted annularFrobeniusCharts
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Fintype k]
    (C : ResidueData p k) (S : Base p k C) [D : RationalRestrictions p k C S]
    (F : FrobeniusPoints p k C S) : FrobeniusCharts p k C S F

/-- Construct the original coefficient-normalized map on the actual annular sheaf. -/
public def_wanted annularSheafFrobenius
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Fintype k]
    (C : ResidueData p k) (S : Base p k C) [D : RationalRestrictions p k C S]
    (F : FrobeniusPoints p k C S) (O : PeriodSheaf p k C S)
    (A : FrobeniusCharts p k C S F) : SheafFrobenius p k C S F O A

/-- Construct the real annulus/quotient with full original E coefficient normalization. -/
public def_wanted analyticCurveConstruction
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Fintype k]
    (C : ResidueData p k) (S : Base p k C) [D : RationalRestrictions p k C S]
    (F : FrobeniusPoints p k C S) (O : PeriodSheaf p k C S)
    (A : FrobeniusCharts p k C S F) (G : SheafFrobenius p k C S F O A) :
    AnalyticConstruction p k C S F O A G

end WantedExt.AlgebraicGeometry.EqualCharacteristicFFModels
