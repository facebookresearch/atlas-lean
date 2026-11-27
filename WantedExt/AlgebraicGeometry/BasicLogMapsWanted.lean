/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.BasicLogCurves
public import Mathlib.Basic.Complex.Basic

/-!
# Canonical log-curve and stable-log-map basicization requests

Inputs and outputs are actual small-etale log structures, scheme maps and
sheaf comparisons. The curve output is initial among log structures on the
same marked nodal family. Stable-map basicization is initial in the actual
category of enhancements of an already given stable log map, retaining its
underlying ordinary map. Fine/fs and characteristic-zero finite-type scope
are explicit on each geometric request, and stable-map basicization keeps the
source's standing assumption that the target and base log structures are
Zariski: fs charts exist on Zariski open neighbourhoods of every point.

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
open MathlibExt.AlgebraicGeometry.MarkedCurveStabilization

/-- The actual stalk map is fixed on every etale log-section generator. -/
def_wanted geometricGhostMap [InverseImageTheory.{0}] (X Y : LogScheme.{0})
    (f : MathlibExt.AlgebraicGeometry.EtaleLogSchemes.Hom X Y) (Ω : Type) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X.scheme) : GhostMap f x

/-- The basic log curve of a marked nodal family: for a Noetherian scheme $T$ of finite type over
$\mathbb{C}$ (locally of finite type and quasi-compact) and a marked family $F$ over $T$ (proper,
flat and of finite presentation, with $n$ disjoint markings in the smooth locus and connected nodal
fibres of genus $g$), a log curve structure on $F$ that is initial among the log curve structures on
$F$ (`BasicLogCurve F`). Log structures are on small étale sites, with the inverse images of the
given `InverseImageTheory`. -/
def_wanted basicLogCurve [InverseImageTheory.{0}] (T : Scheme.{0})
    [IsNoetherian T] (c : T ⟶ Spec (.of ℂ)) [LocallyOfFiniteType c] [QuasiCompact c]
    (n g : ℕ) (F : MarkedFamily T n g) : BasicLogCurve F

/-! The basicization of a stable log map is requested once, over every field of characteristic
zero, by `WantedExt.AlgebraicGeometry.BasicLogGhostNormalizations.geometricBasicization`; its first
component is the basicization (for `k = ℂ` this is the complex case). -/
