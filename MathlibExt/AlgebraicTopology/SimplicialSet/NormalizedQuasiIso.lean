/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate

/-!
# Normalized quasi-isomorphism with minimal assumptions
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomologicalComplex

namespace SSet

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- The canonical homotopy equivalence from the normalized chain complex to the
unnormalized chain complex, as the symmetric of Mathlib's
`X.homotopyEquivNormalizedChainComplex`. Its forward map is definitionally
`X.fromNormalizedChainComplex`. -/
noncomputable def homotopyEquivFromNormalizedChainComplex (X : SSet.{w}) (R : C) :
    HomotopyEquiv (X.normalizedChainComplex R) (X.chainComplex R) :=
  (X.homotopyEquivNormalizedChainComplex R).symm

@[simp]
theorem homotopyEquivFromNormalizedChainComplex_hom (X : SSet.{w}) (R : C) :
    (homotopyEquivFromNormalizedChainComplex C X R).hom = X.fromNormalizedChainComplex R :=
  rfl

variable [CategoryWithHomology C] in
theorem quasiIso_fromNormalizedChainComplex (X : SSet.{w}) (R : C) :
    QuasiIso (X.fromNormalizedChainComplex (C := C) R) :=
  inferInstance

end SSet
