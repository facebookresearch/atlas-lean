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

/-- For a prime $p$ and a finite field $k$ of characteristic $p$, the Laurent-series field $k((t))$,
with the valuative relation of its $t$-adic valuation, is a nonarchimedean local field. -/
public theorem_wanted laurentSeriesLocalField
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Fintype k] :
    letI := valuativeRelation k
    IsNonarchimedeanLocalField (CoefficientField k)

/-- Restriction maps of the rational charts of the annulus: for a prime $p$, a finite field $k$ of
characteristic $p$ with $\#k = p^f$ (`C`) and a perfectoid base `S` (a characteristic-$p$ perfectoid
pair $(R, R^+)$ with $R^+$ a perfect $k$-algebra and a pseudo-uniformizer $\varpi \in R^+$), on the
annulus $Y_S$ (the points of $\operatorname{Spa} R^+[[t]]$ at which $t$ and $\varpi$ do not vanish),
a topology on each completed rational chart ring with the ideal-filtration basis of neighbourhoods
of zero, and continuous restriction ring maps from a rational chart to every smaller one that are
compatible with the coefficient maps from $R^+[[t]]$; continuous ring maps between chart rings that
agree on these coefficients are equal, and rational opens form a basis of the topology of $Y_S$. -/
public def_wanted rationalRestrictionDictionary
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Fintype k]
    (C : ResidueData p k) (S : Base p k C) : RationalRestrictions p k C S

/-- Frobenius on the points of the annulus: for a prime $p$, a finite field $k$ of characteristic
$p$ with $\#k = p^f$ (`C`) and a perfectoid base `S` (a characteristic-$p$ perfectoid pair
$(R, R^+)$ with $R^+$ a perfect $k$-algebra and a pseudo-uniformizer $\varpi \in R^+$), a
self-homeomorphism of the annulus $Y_S$ (the points of $\operatorname{Spa} R^+[[t]]$ at which $t$
and $\varpi$ do not vanish) that sends each point to its pullback along the Frobenius of $R^+[[t]]$
(the coefficientwise $\#k$-th power, fixing $t$). -/
public def_wanted annularFrobeniusPoints
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Fintype k]
    (C : ResidueData p k) (S : Base p k C) : FrobeniusPoints p k C S

/-- The structure sheaf of the annulus: for a prime $p$, a finite field $k$ of characteristic $p$
with $\#k = p^f$ (`C`) and a perfectoid base `S` (a characteristic-$p$ perfectoid pair $(R, R^+)$
with $R^+$ a perfect $k$-algebra and a pseudo-uniformizer $\varpi \in R^+$), with restriction maps
`D` on the rational charts of the annulus $Y_S$ (the points of $\operatorname{Spa} R^+[[t]]$ at
which $t$ and $\varpi$ do not vanish), a sheaf of rings on $Y_S$ with an identification of its
sections over rational opens with the completed rational chart rings, compatible with the
restriction maps of `D`, such that the sheaf is the right Kan extension of these values. -/
public def_wanted annularPeriodSheaf
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Fintype k]
    (C : ResidueData p k) (S : Base p k C) [D : RationalRestrictions p k C S] :
    PeriodSheaf p k C S

/-- Frobenius on the rational charts of the annulus: for a prime $p$, a finite field $k$ of
characteristic $p$ with $\#k = p^f$ (`C`) and a perfectoid base `S` (a characteristic-$p$ perfectoid
pair $(R, R^+)$ with $R^+$ a perfect $k$-algebra and a pseudo-uniformizer $\varpi \in R^+$), with
restriction maps `D` and the point Frobenius `F` of the annulus $Y_S$ (the points of
$\operatorname{Spa} R^+[[t]]$ at which $t$ and $\varpi$ do not vanish), a functor on rational
presentations applying the Frobenius of $R^+[[t]]$ to numerators and denominator, whose rational
open is the preimage of the original one under `F`, with continuous ring maps between the chart
rings that extend the Frobenius on coefficients and commute with the restriction maps of `D`. -/
public def_wanted annularFrobeniusCharts
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Fintype k]
    (C : ResidueData p k) (S : Base p k C) [D : RationalRestrictions p k C S]
    (F : FrobeniusPoints p k C S) : FrobeniusCharts p k C S F

/-- Frobenius on the structure sheaf of the annulus: for a prime $p$, a finite field $k$ of
characteristic $p$ with $\#k = p^f$ (`C`) and a perfectoid base `S` (a characteristic-$p$ perfectoid
pair $(R, R^+)$ with $R^+$ a perfect $k$-algebra and a pseudo-uniformizer $\varpi \in R^+$), with
restriction maps `D`, point Frobenius `F`, structure sheaf `O` and chart Frobenius `A` on the
annulus $Y_S$ (the points of $\operatorname{Spa} R^+[[t]]$ at which $t$ and $\varpi$ do not vanish),
a morphism from `O` to its pushforward along `F` that, on every rational open, is the chart
Frobenius of `A` under the identification of sections with the completed rational chart rings. -/
public def_wanted annularSheafFrobenius
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Fintype k]
    (C : ResidueData p k) (S : Base p k C) [D : RationalRestrictions p k C S]
    (F : FrobeniusPoints p k C S) (O : PeriodSheaf p k C S)
    (A : FrobeniusCharts p k C S F) : SheafFrobenius p k C S F O A

/-- Analytic realizations of the annulus and of the curve: for a prime $p$, a finite field $k$ of
characteristic $p$ with $\#k = p^f$ (`C`) and a perfectoid base `S` (a characteristic-$p$ perfectoid
pair $(R, R^+)$ with $R^+$ a perfect $k$-algebra and a pseudo-uniformizer $\varpi \in R^+$), with
restriction maps `D`, point Frobenius `F`, structure sheaf `O`, chart Frobenius `A` and sheaf
Frobenius `G` on the annulus $Y_S$ (the points of $\operatorname{Spa} R^+[[t]]$ at which $t$ and
$\varpi$ do not vanish): an analytic adic space $Y$ with a homeomorphism to $Y_S$ identifying its
structure sheaf with `O` and its valuations on chart coefficients with the points of $Y_S$; an
analytic adic space $X$ with a homeomorphism to the quotient of $Y_S$ by `F` and an étale morphism
$Y \to X$ lying over the quotient map, whose structure sheaf is identified with the Frobenius
invariants of the pushed-forward sheaf `O`, compatibly with $Y \to X$; and structures of $E$-spaces
on $Y$ and $X$ for $E = k((t))$, compatible with the coefficient maps of $E$ into the chart rings,
for which $Y \to X$ is a map of $E$-spaces. -/
public def_wanted analyticCurveConstruction
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Fintype k]
    (C : ResidueData p k) (S : Base p k C) [D : RationalRestrictions p k C S]
    (F : FrobeniusPoints p k C S) (O : PeriodSheaf p k C S)
    (A : FrobeniusCharts p k C S F) (G : SheafFrobenius p k C S F O A) :
    AnalyticConstruction p k C S F O A G

end WantedExt.AlgebraicGeometry.EqualCharacteristicFFModels
