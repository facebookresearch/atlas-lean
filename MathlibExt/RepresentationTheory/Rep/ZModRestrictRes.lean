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

This comparison uses the identity on coefficient carriers. It is shared by
all cohomological degrees and includes ZMod zero.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace groupCohomology

variable {G : Type} [Group G]

/-- Restricting the acting group and restricting `ZMod n` scalars commute,
with an identity-on-carriers comparison. -/
noncomputable def zmodRestrictIntResIso
    {J : Type} [Group J] (n : ℕ) (r : J →* G)
    (A : Rep (ZMod n) G) :
    Rep.zmodRestrictInt n (Rep.res r A) ≅
      Rep.res r (Rep.zmodRestrictInt n A) :=
  eqToIso (by rfl)

end groupCohomology
