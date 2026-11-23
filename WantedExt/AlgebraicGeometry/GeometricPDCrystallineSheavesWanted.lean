/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GeometricPDCrystallineSheaves

/-!
# The geometric crystalline structure-sheaf dictionary

The source site consists of actual nilpotent PD thickenings and open
covers of their ambient schemes. The normalized statement below says
that their ring presheaf already satisfies descent, so its completed
sheafification construction has exactly the original rings on tests.

The Dieudonné finite-projective crystal, F/V, A_cris/B_cris⁺ and formal
Lie/Hodge--Tate realization remain further required interfaces.

References: Berthelot--Ogus, *Notes on crystalline cohomology*, Chapter III;
Scholze--Weinstein, arXiv:1211.6357v2, Sections 3.2 and 4.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.GeometricPDCrystallineSheaves

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GeometricPDCrystallineTests
open MathlibExt.AlgebraicGeometry.GeometricPDCrystallineSheaves

/-- Descent on every genuine PD thickening open cover. -/
public theorem_wanted crystalline_structure_descent
    (p : ℕ) [Fact p.Prime] (A : PDBase) (S : Over A.reduction) :
    Presheaf.IsSheaf (topology p A S) (structureRingPresheaf p A S)

end WantedExt.AlgebraicGeometry.GeometricPDCrystallineSheaves
