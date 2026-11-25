/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.GroupTheory.Generators

@[expose] public section

namespace Group.Generators

universe u v w

variable {G : Type u} {H : Type v} {ι : Type w} [Group G] [Group H]
variable (P : Group.Generators G ι)
variable (f : FreeGroup ι →* H) (hker : P.lift.ker ≤ f.ker)

example : (P.desc f hker).comp P.lift = f :=
  P.desc_comp_lift f hker

example (x : FreeGroup ι) : P.desc f hker (P.lift x) = f x :=
  P.desc_lift f hker x

example (i : ι) : P.desc f hker (P.val i) = f (FreeGroup.of i) :=
  P.desc_val f hker i

example (g : G →* H) (hg : g.comp P.lift = f) :
    g = P.desc f hker :=
  P.desc_unique f hker g hg

example (g : G →* H) :
    g = P.desc f hker ↔ g.comp P.lift = f :=
  P.eq_desc_iff_comp_lift_eq f hker g

end Group.Generators
