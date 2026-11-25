/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PDivisibleGeometricTateModels

/-!
# The actual geometric finite-level dictionary

The source generic Tate inverse limit, Z_p action and maps are already
ported and completed. This request is only the geometric kernel/filtered
colimit comparison for the original finite-flat scheme levels. It does
not request another Tate constructor or a linear-map construction.

Source: Scholze--Weinstein, arXiv:1211.6357v2, Section 3.3.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.PDivisibleGeometricTate

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PDivisibleGroupSchemes
open MathlibExt.AlgebraicGeometry.PDivisibleGeometricTateModels

/-- Actual scheme p^n-level points are exactly the p^n-torsion of the original point colimit. -/
public theorem_wanted finite_to_torsion_bijective
    (p : ℕ) [Fact p.Prime] (S : Scheme.{0}) (G : PDivisibleGroup S p)
    (T : Over S) (n : ℕ) : Function.Bijective (finiteToTorsion p S G T n)

end WantedExt.AlgebraicGeometry.PDivisibleGeometricTate
