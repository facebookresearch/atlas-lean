/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic

@[expose] public section

/-!
# Singular Kan polymorphic client

Minimal public client for `TopCat.toSSet_obj_kanComplex` at universe 1.
No filling, anodyne, or model-category claim beyond the provider.
-/

set_option autoImplicit false

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.SingularKanPolymorphicTests

theorem singularKan_client (X : TopCat.{1}) :
    SSet.KanComplex (TopCat.toSSet.obj X) :=
  TopCat.toSSet_obj_kanComplex X

#print axioms TopCat.toSSet_obj_kanComplex

#print axioms singularKan_client

end MathlibExtTest.AlgebraicTopology.ModelCategory.SingularKanPolymorphicTests
