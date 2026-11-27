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

public import MathlibExt.GroupTheory.GroupExtension.Pullback

/-!
# Tests for functorial pullbacks of group extensions
-/

@[expose] public section

set_option autoImplicit false

namespace GroupExtension

variable {N E G H N' E' G' H' N'' E'' G'' H'' : Type*}
variable [Group N] [Group E] [Group G] [Group H]
variable [Group N'] [Group E'] [Group G'] [Group H']
variable [Group N''] [Group E''] [Group G''] [Group H'']
variable {S : GroupExtension N E G} {T : GroupExtension N' E' G'}
variable {U : GroupExtension N'' E'' G''}
variable (m : S.Hom T) {f : H →* G} {g : H' →* G'}
variable (h : H →* H') (h_comm : m.quotientHom.comp f = g.comp h)

example : PullbackTotal S f →* PullbackTotal T g :=
  pullbackMap m h h_comm

example :
    (pullbackFst T g).comp (pullbackMap m h h_comm) =
      m.totalHom.comp (pullbackFst S f) := by
  simp

example :
    (pullbackSnd T g).comp (pullbackMap m h h_comm) =
      h.comp (pullbackSnd S f) := by
  simp

example :
    (pullbackMap m h h_comm).comp (pullbackInl S f) =
      (pullbackInl T g).comp m.kernelHom := by
  simp

example :
    (pullbackExtension S f).Hom (pullbackExtension T g) :=
  pullbackExtensionHom m h h_comm

example (k : PullbackTotal S f →* PullbackTotal T g)
    (hfst : (pullbackFst T g).comp k =
      m.totalHom.comp (pullbackFst S f))
    (hsnd : (pullbackSnd T g).comp k =
      h.comp (pullbackSnd S f)) :
    k = pullbackMap m h h_comm :=
  pullbackMap_unique m h h_comm k hfst hsnd

example :
    pullbackMap (Hom.id S) (MonoidHom.id H) (by simp) =
      MonoidHom.id (PullbackTotal S f) := by
  simp

example (n : T.Hom U) {k : H'' →* G''} (i : H' →* H'')
    (i_comm : n.quotientHom.comp g = k.comp i) :
    pullbackMap (n.comp m) (i.comp h) (by
        calc
          (n.comp m).quotientHom.comp f =
              n.quotientHom.comp (m.quotientHom.comp f) := by
            rw [Hom.comp_quotientHom, MonoidHom.comp_assoc]
          _ = n.quotientHom.comp (g.comp h) := by rw [h_comm]
          _ = (n.quotientHom.comp g).comp h := by
            rw [MonoidHom.comp_assoc]
          _ = (k.comp i).comp h := by rw [i_comm]
          _ = k.comp (i.comp h) := by rw [MonoidHom.comp_assoc]) =
      (pullbackMap n i i_comm).comp (pullbackMap m h h_comm) :=
  pullbackMap_comp m n h i h_comm i_comm

end GroupExtension
