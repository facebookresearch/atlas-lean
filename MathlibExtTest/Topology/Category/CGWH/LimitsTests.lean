/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Limits
public import MathlibExt.Topology.Category.CGWH.Products

/-!
# Tests for scoped limits in CGWH
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace MathlibExtTest.CGWH.LimitsTests

section ScopeOff

#synth HasProducts.{v} CGWH.{u, v}
#synth HasFiniteProducts CGWH.{u, v}

example : True := by
  fail_if_success
    let _ : HasLimitsOfSize.{v, v} CGWH.{u, v} := inferInstance
  fail_if_success
    let _ : HasFiniteLimits CGWH.{u, v} := inferInstance
  fail_if_success
    let _ : HasPullbacks CGWH.{u, v} := inferInstance
  trivial

end ScopeOff

section ScopeOn

open scoped CGWH.limits

#check CGWH.limits.instHasLimitsOfSize

#synth HasLimitsOfSize.{v, v} CGWH.{u, v}
#synth HasFiniteLimits CGWH.{u, v}
#synth HasPullbacks CGWH.{u, v}
#synth HasEqualizers CGWH.{u, v}
#synth HasTerminal CGWH.{u, v}

#synth HasLimitsOfSize.{0, 0} CGWH.{0, 0}
#synth HasLimitsOfSize.{1, 1} CGWH.{1, 1}
#synth HasLimitsOfSize.{1, 1} CGWH.{0, 1}
#synth HasLimitsOfSize.{0, 0} CGWH.{1, 0}

#synth HasPullbacks CGWH.{0, 0}
#synth HasPullbacks CGWH.{1, 1}
#synth HasPullbacks CGWH.{0, 1}
#synth HasPullbacks CGWH.{1, 0}

example : (inferInstance : HasProducts.{v} CGWH.{u, v}) =
    CGWH.instHasProducts := rfl

example : (inferInstance : HasFiniteProducts CGWH.{u, v}) =
    CGWH.instHasFiniteProducts := rfl

end ScopeOn

section InstanceDeletion

open scoped CGWH.limits

attribute [-instance] CGWH.limits.instHasLimitsOfSize in
example : True := by
  fail_if_success
    let _ : HasLimitsOfSize.{v, v} CGWH.{u, v} := inferInstance
  fail_if_success
    let _ : HasPullbacks CGWH.{u, v} := inferInstance
  let _ : HasProducts.{v} CGWH.{u, v} := inferInstance
  let _ : HasFiniteProducts CGWH.{u, v} := inferInstance
  trivial

end InstanceDeletion

section ScopeTeardown

#synth HasProducts.{v} CGWH.{u, v}
#synth HasFiniteProducts CGWH.{u, v}

example : True := by
  fail_if_success
    let _ : HasLimitsOfSize.{v, v} CGWH.{u, v} := inferInstance
  fail_if_success
    let _ : HasPullbacks CGWH.{u, v} := inferInstance
  trivial

end ScopeTeardown

#print axioms CGWH.limits.instHasLimitsOfSize

end MathlibExtTest.CGWH.LimitsTests
