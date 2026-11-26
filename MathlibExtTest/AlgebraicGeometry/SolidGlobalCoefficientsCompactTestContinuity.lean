/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.SolidGlobalCoefficientsCompactTestContinuity

/-!
# Sheaf restriction to compact tests

Restricting a sheaf on the coefficient site to compact tests over a fixed affine test gives a
sheaf for the coherent topology.

Source: Anschuetz--Mann, arXiv:2403.01951v2, Theorems 1.1 and 4.7,
Definitions 2.3--2.4 and 4.2.
-/

namespace MathlibExtTest.AlgebraicGeometry.SolidGlobalCoefficientsCompactTestContinuity

open CategoryTheory
open MathlibExt.AlgebraicGeometry.AffinePerfectoidVSite
open MathlibExt.AlgebraicGeometry.PerfectoidSliceSites
open MathlibExt.Condensed.PerfectoidIntegralVSites

example (p : ℕ) [Fact p.Prime] (F : VSheaf p) (T : AffineTest p F)
    (P : (CondensedTest p F)ᵒᵖ ⥤ Type 1) (hP : Presheaf.IsSheaf (coefficientTopology F) P) :
    Presheaf.IsSheaf (coherentTopology CompHaus.{0}) ((compactTests T).op ⋙ P) := by
  let := WantedExt.AlgebraicGeometry.SolidGlobalCoefficients.compactTestContinuity p F T
  exact (compactTests T).op_comp_isSheaf_of_isSheaf
    (coherentTopology CompHaus.{0}) (coefficientTopology F) P hP

end MathlibExtTest.AlgebraicGeometry.SolidGlobalCoefficientsCompactTestContinuity
