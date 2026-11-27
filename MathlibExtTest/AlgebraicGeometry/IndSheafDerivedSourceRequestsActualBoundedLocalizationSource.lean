/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.IndSheafDerivedSourceRequestsActualBoundedLocalizationSource

/-!
# Tests for bounded Ind-sheaf localization

The localization theorem inverts bounded quasi-isomorphisms and gives
bounded cochain representatives of bounded derived objects.

Source: Andrea D'Agnolo and Masaki Kashiwara, Riemann-Hilbert correspondence
for holonomic D-modules, arXiv:1311.2374v2, Sections 2.2, 3.2--3.3 and 4.4;
Masaki Kashiwara and Pierre Schapira, Ind-sheaves and Categories and Sheaves.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace MathlibExtTest.AlgebraicGeometry
namespace IndSheafDerivedSourceRequestsActualBoundedLocalizationSource

open CategoryTheory
open MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
open MathlibExt.AlgebraicGeometry.IndSheafBoundedTensorModels
open WantedExt.AlgebraicGeometry.IndSheafDerivedSourceRequests

private instance sourceAbelianPreadditive (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] : Preadditive (IndSheaf k X) := Abelian.toPreadditive

attribute [local instance] HasDerivedCategory.standard

private theorem inverts_bounded_quasiIso (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X]
    (R : BoundedCohomologySource k X) {K L : BoundedIndComplex k X}
    (f : K ⟶ L) (hf : boundedQuasiIso k X f) : IsIso ((boundedQ k X R).map f) := by
  let := (actual_bounded_localization_source k X R).isLocalization
  exact Localization.inverts (boundedQ k X R) (boundedQuasiIso k X) f hf

private theorem exists_bounded_representative (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X]
    (R : BoundedCohomologySource k X) (F : BoundedIndDerived k X) :
    ∃ K : BoundedIndComplex k X, Nonempty ((boundedQ k X R).obj K ≅ F) := by
  let := (actual_bounded_localization_source k X R).isLocalization
  exact (Localization.essSurj (boundedQ k X R) (boundedQuasiIso k X)).mem_essImage F

end IndSheafDerivedSourceRequestsActualBoundedLocalizationSource
end MathlibExtTest.AlgebraicGeometry
