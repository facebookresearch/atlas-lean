/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.GroupTheory.Abelianization.MapBijective

universe v w

#check @MonoidHom.bijective_of_abelianization_map
#print axioms MonoidHom.bijective_of_abelianization_map

example {G : Type v} {H : Type w} [Group G] [Group H]
    [IsMulCommutative G] [IsMulCommutative H] (f : G →* H)
    (hf : Function.Bijective (Group.Abelianization.map f)) : Function.Bijective f :=
  MonoidHom.bijective_of_abelianization_map f hf
