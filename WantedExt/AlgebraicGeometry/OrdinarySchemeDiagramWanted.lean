/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.OrdinarySchemeTorModels

/-!
# Native ordinary categorical diagram and Tor-comparison source laws

The entire indexing category, constant coefficients, native section
limits, actual balanced Tor tests and source reindexing maps are fixed.
There is no cover or descent assumption in these generic source requests.

Sources: HTT Section3.3.3; Bhatt--Mathew1807.04725v4, Section5.4.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicGeometry.OrdinarySchemeDiagramModels

open _root_.CategoryTheory
open GeneralArcCoverModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle

variable {N : ShuffleAlgebraFunctor ℤ} {S : AffineScalarSystem N}
  (M : AffineModuleFibration N S) {J : Type} [Category.{0} J] {X : QcqsScheme} (H : J ⥤ Over X)

theorem_wanted ordinary_qcoh_diagram_quasicategory : SSet.Quasicategory (qcohLimit H M)

theorem_wanted ordinary_perf_diagram_quasicategory : SSet.Quasicategory (perfLimit H M)

end MathlibExt.AlgebraicGeometry.OrdinarySchemeDiagramModels

namespace MathlibExt.AlgebraicGeometry.OrdinarySchemeTorModels

open _root_.CategoryTheory
open GeneralArcCoverModels OrdinaryConstantCoefficientModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle

variable {N : ShuffleAlgebraFunctor ℤ} {S : AffineScalarSystem N}
  (M : AffineModuleFibration N S) (T : OrdinaryTorSystem N)
  {J : Type} [Category.{0} J] {X : QcqsScheme} (H : J ⥤ Over X)

def_wanted ordinary_tor_diagram_comparison (a b : ℤ) : TorComparison M T H a b

def_wanted ordinary_tor_pullback {X Y : QcqsScheme} (f : X ⟶ Y) (a b : ℤ) :
  TorPullback M T f a b

end MathlibExt.AlgebraicGeometry.OrdinarySchemeTorModels
