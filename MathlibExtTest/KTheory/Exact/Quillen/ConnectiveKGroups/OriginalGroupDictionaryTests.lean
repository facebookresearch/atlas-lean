/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Exact.Quillen.ConnectiveKGroups.OriginalGroupDictionary

/-!
# Original current group dictionary tests

The direct clients retain separate category object and Hom worlds and
the existing current group / exact K-zero maps.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicKTheory AlgebraicKTheory AlgebraicKTheory.ConnectiveKGroups

universe uC vC uD vD

variable (C : Type uC) [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

example (F : C ⥤ D) [F.Additive] [F.IsExact] (g : groupCarrier C 0) :
    groupExactK0MulEquiv D (groupMap C F 0 g) =
      (K0.map F).toMultiplicative (groupExactK0MulEquiv C g) :=
  groupExactK0MulEquiv_naturality C F g

example (g : groupCarrier C 0) :
    groupExactK0MulEquiv C g =
      Multiplicative.ofAdd (groupExactK0Equiv C (Additive.ofMul g)) :=
  groupExactK0MulEquiv_apply C g
