/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Rep.ZModRestrict
public import Mathlib.RepresentationTheory.Rep.Res

/-!
# Integral scalar restriction and acting-group restriction

Let `r : J →* G` be a homomorphism of groups and `A` a representation of `G`
over `ZMod n`, for any natural number `n`. Restricting the acting group along `r`
and restricting scalars to `ℤ` commute. The comparison is the identity on the
coefficient module, and both actions send `j` to the original action of `r(j)`.
The modulus `n = 0`, for which `ZMod n` is `ℤ`, is included.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace groupCohomology

variable {G : Type} [Group G]

/-- Let `r : J →* G` be a group homomorphism, `n : ℕ`, and `A` a representation
of `G` over `ZMod n`. Restricting `A` to `J` and then restricting scalars to `ℤ`
gives a representation isomorphic to the one obtained in the reverse order.
The isomorphism is the identity on coefficients, and both `J`-actions are the
original action precomposed with `r`. This includes `n = 0`. -/
noncomputable def zmodRestrictIntResIso
    {J : Type} [Group J] (n : ℕ) (r : J →* G)
    (A : Rep (ZMod n) G) :
    Rep.zmodRestrictInt n (Rep.res r A) ≅
      Rep.res r (Rep.zmodRestrictInt n A) :=
  eqToIso (by rfl)

end groupCohomology
