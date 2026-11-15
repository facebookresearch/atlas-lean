/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.BasicLogCurves
public import MathlibExt.AlgebraicGeometry.BasicLogMapFamilies
public import MathlibExt.AlgebraicGeometry.LogMapBasicMonoids
public import Mathlib.Basic.Complex.Basic

/-!
# Canonical log-curve and stable-log-map basicization requests

Inputs and outputs are actual small-etale log structures, scheme maps and
sheaf comparisons. The curve output is initial among log structures on the
same marked nodal family. Stable-map basicization is initial in the actual
category of enhancements of an already given stable log map, retaining its
underlying ordinary map. Fine/fs and characteristic-zero finite-type scope
are explicit on each geometric request.

Sources: F. Kato, log smooth curves; Gross--Siebert,
https://arxiv.org/abs/1102.4322v2, §1.2, Construction1.16,
Proposition1.19, Lemma1.23 and Proposition1.24. Stack algebraicity and
properness use their additional source hypotheses and are separate goals.
The displayed relation/root-closure definition has no automatic sharpness
claim before a geometric log-map realization is supplied.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.EtaleLogSchemes
open MathlibExt.AlgebraicGeometry.EtaleLogDiagrams
open MathlibExt.AlgebraicGeometry.GeometricLogGhosts
open MathlibExt.AlgebraicGeometry.BasicLogCurves
open MathlibExt.AlgebraicGeometry.BasicLogMapFamilies
open MathlibExt.AlgebraicGeometry.MarkedCurveStabilization

/-- The actual stalk map is fixed on every etale log-section generator. -/
def_wanted geometricGhostMap [InverseImageTheory.{0}] (X Y : LogScheme.{0})
    (f : MathlibExt.AlgebraicGeometry.EtaleLogSchemes.Hom X Y) (Ω : Type) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X.scheme) : GhostMap f x

/-- The actual universal basic log curve, with native node/marking maps. -/
def_wanted basicLogCurve [InverseImageTheory.{0}] (T : Scheme.{0})
    [IsNoetherian T] (c : T ⟶ Spec (.of ℂ)) [LocallyOfFiniteType c] [QuasiCompact c]
    (n g : ℕ) (F : MarkedFamily T n g) : BasicLogCurve F

/-- Canonical comparison from a basic enhancement; input M carries the
actual original stable log map and its log-curve geometry. -/
def_wanted basicization [InverseImageTheory.{0}] (X S : LogScheme.{0})
    (hX : X.IsFineSaturated) (hS : S.IsFineSaturated)
    (q : MathlibExt.AlgebraicGeometry.EtaleLogSchemes.Hom X S) [LocallyOfFiniteType q.map] [QuasiCompact q.map]
    (c : S.scheme ⟶ Spec (.of ℂ)) [LocallyOfFiniteType c] [QuasiCompact c]
    (n g : ℕ) (T : Scheme.{0}) [IsNoetherian T]
    (b : T ⟶ S.scheme) [LocallyOfFiniteType b] [QuasiCompact b]
    (M : StableLogMap q n g T b) : Basicization M
