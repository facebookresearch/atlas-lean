/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.LogStructures
public import MathlibExt.AlgebraicGeometry.LogarithmicGeometryAssociatedLogUnitCondition

/-!
# Shared log-association and characteristic contracts

These requests concern arbitrary actual ringed Grothendieck sites. Their
sheaves, unit pullbacks, characteristic pushouts, site points and chart
covering families are the native constructions in the completed core.
The associated prelog is a fixed sheaf pushout; its log unit condition
`associated_log_unit_condition`, which chooses no new log carrier, is now
proved in `MathlibExt.AlgebraicGeometry.LogarithmicGeometryAssociatedLogUnitCondition`.
The characteristic comparison is fixed on
the actual quotient map, and fine/fs conclusions use genuine local charts.

Sources: Kato, *Logarithmic structures of Fontaine--Illusie*, §1;
Nakayama--Ogus, *Relative rounding in toric and logarithmic geometry*,
Definition 3.4 and the following associated-log/chart construction,
https://math.berkeley.edu/~ogus/preprints/nakayamaogus.pdf;
Achinger--Ogus, *Monodromy and log geometry*, §3.1,
https://arxiv.org/abs/1802.02234.

Generic monoid limits/colimits, groupification, exact concrete sheafification,
continuous-site restriction and site-point fibers are covered source support.
Log-smooth lifting/chart criteria, root stacks and log modifications, global
Kato--Nakayama/étale/de Rham/Chow comparisons remain separate shared contracts.
The Zariski log-scheme category in the core is an explicit specialization;
it does not replace small-étale charts or unsplit normal crossings.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.LogarithmicGeometryWanted

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.LogStructures

universe u v

/-- Fibers of the actual characteristic sheaf agree with the actual
unit quotient of the log-monoid fiber through its normalized quotient map. -/
public def_wanted characteristic_fiber_comparison
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (O : RingSheaf J) (L : LogStructure J O) (p : J.Point.{max u v}) :
    CharacteristicFiberComparison J L p

/-- Local fine charts give fine sharp characteristic monoids at site points. -/
public theorem_wanted fine_characteristic
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (O : RingSheaf J) (L : LogStructure J O) (fine : HasFineCharts J L)
    (p : J.Point.{max u v}) :
    IsFineMonoid (characteristicAt J L p) ∧ IsSharpMonoid (characteristicAt J L p)

/-- Local fs charts give fine saturated sharp characteristic monoids. -/
public theorem_wanted fs_characteristic
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (O : RingSheaf J) (L : LogStructure J O) (fs : HasFineSaturatedCharts J L)
    (p : J.Point.{max u v}) :
    IsFineSaturatedMonoid (characteristicAt J L p) ∧ IsSharpMonoid (characteristicAt J L p)

end WantedExt.AlgebraicGeometry.LogarithmicGeometryWanted
