/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.EnhancedConvolutionSourceRequestsActualBoundedInverseImageSource
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Tests for boundedness of the actual Ind inverse image

The inverse image of an Ind sheaf concentrated in one degree has bounded cohomology: the
boundedness consequence for the model's given exact inverse image.

Source: D'Agnolo--Kashiwara, arXiv:1311.2374v2, Section 2 conventions and Proposition 3.4.4(ii).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace MathlibExtTest.AlgebraicGeometry.EnhancedConvolutionSourceRequestsActualBoundedInverseImageSource

open CategoryTheory
open MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
open MathlibExt.AlgebraicGeometry.IndSheafCoefficientModels
open MathlibExt.AlgebraicGeometry.IndSheafInverseImageModels
open MathlibExt.AlgebraicGeometry.BoundedIndImageModels
open WantedExt.AlgebraicGeometry.EnhancedConvolutionSourceRequests

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] requestAbelianPreadditive

example (k : Type) [Field k] (X Y : TopCat.{0})
    [CompactSheafSource k X] [CompactSheafSource k Y]
    (f : X ⟶ Y) (S : OrdinaryIndSource k X) (D : IndInverseImageSource k f S)
    [(indInverseImage k f S D).Additive] (E : ExactIndInverseImageSource k f S D)
    (A : IndSheaf k Y) (m : ℤ) :
    IsBounded k X ((derivedIndInverseImage k f S D E).obj
      ((DerivedCategory.singleFunctor (IndSheaf k Y) m).obj A)) := by
  have hA : IsBounded k Y ((DerivedCategory.singleFunctor (IndSheaf k Y) m).obj A) := by
    refine ⟨m, m, fun n hn => ?_⟩
    rcases hn with hn | hn
    · exact DerivedCategory.isZero_of_isGE _ m n hn
    · exact DerivedCategory.isZero_of_isLE _ m n hn
  exact (actual_bounded_inverse_image_source k X Y f S D E).bounded ⟨_, hA⟩

end MathlibExtTest.AlgebraicGeometry.EnhancedConvolutionSourceRequestsActualBoundedInverseImageSource
