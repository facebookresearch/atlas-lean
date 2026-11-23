/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.CGWH.FiniteRealization

/-!
# Tests for finite realizations in CGWH

The owners exercise independent probe/carrier universes, literal CGWH
bundling, the underlying compactly-generated object and topology, premise
deletion, and trust.
-/

set_option autoImplicit false

noncomputable section

universe u v

namespace MathlibExtTest.SSet.CGWHFiniteRealization

#check @SSet.toCGWHOfFinite

section Generic

variable (K : SSet.{v}) [K.Finite]

example : CGWH.{u, v} := SSet.toCGWHOfFinite K

example : (SSet.toCGWHOfFinite.{u, v} K).toCompactlyGenerated =
    SSet.toCompactlyGeneratedOfFinite K := rfl

example : (SSet.toCGWHOfFinite.{u, v} K).toTop =
    SSet.toTop.obj K := rfl

example :
    (inferInstance : TopologicalSpace (SSet.toCGWHOfFinite.{u, v} K)) =
      (inferInstance : TopologicalSpace (SSet.toTop.obj K)) := rfl

end Generic

section ExplicitUniverses

variable (K₀ : SSet.{0}) [K₀.Finite]
variable (K₁ : SSet.{1}) [K₁.Finite]

example : CGWH.{0, 0} := SSet.toCGWHOfFinite.{0, 0} K₀
example : CGWH.{1, 1} := SSet.toCGWHOfFinite.{1, 1} K₁
example : CGWH.{0, 1} := SSet.toCGWHOfFinite.{0, 1} K₁
example : CGWH.{1, 0} := SSet.toCGWHOfFinite.{1, 0} K₀

end ExplicitUniverses

section MissingFiniteness

variable (K : SSet.{v})

example : True := by
  fail_if_success
    let _ : CGWH.{u, v} := SSet.toCGWHOfFinite K
  trivial

end MissingFiniteness

#print axioms SSet.toCGWHOfFinite

end MathlibExtTest.SSet.CGWHFiniteRealization
