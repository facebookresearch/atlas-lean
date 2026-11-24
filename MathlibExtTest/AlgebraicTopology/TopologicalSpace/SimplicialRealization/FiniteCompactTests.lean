/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.FiniteCompact

/-!
# Finite realization compactness and separation tests

These owners isolate the finite-topology provider from the neutral quotient
presentation and the legacy generatedness specialization.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialRealization
namespace FiniteCompactTests

section Finite

variable (K : SSet.{u}) [K.Finite]

example : CompactSpace (SSet.toTop.obj K) := inferInstance
example : T2Space (SSet.toTop.obj K) := inferInstance
example : T1Space (SSet.toTop.obj K) := inferInstance

end Finite

section ExplicitUniverses

variable (K₀ : SSet.{0}) [K₀.Finite]
variable (K₁ : SSet.{1}) [K₁.Finite]

example : CompactSpace (SSet.toTop.obj K₀) := inferInstance
example : T2Space (SSet.toTop.obj K₀) := inferInstance
example : CompactSpace (SSet.toTop.obj K₁) := inferInstance
example : T2Space (SSet.toTop.obj K₁) := inferInstance

end ExplicitUniverses

section MissingFiniteness

variable (K : SSet.{u})

example : True := by
  fail_if_success
    let _ : CompactSpace (SSet.toTop.obj K) := inferInstance
  fail_if_success
    let _ : T2Space (SSet.toTop.obj K) := inferInstance
  trivial

end MissingFiniteness

end FiniteCompactTests
end MathlibExtTest.AlgebraicTopology.SimplicialRealization

end
