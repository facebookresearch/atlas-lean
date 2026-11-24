/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

import MathlibExt.GroupTheory.GroupExtension.UniversalRecognition

universe u v w x

open GroupExtension

section IndependentUniverses

variable {N : Type u} {E : Type v} {G : Type w} {H : Type x}
variable [Group N] [Group E] [Group G] [Group H]

-- The source of the lifted map has a fourth, independent universe.
example (S : GroupExtension N E G) (f : H →* G)
    (σ : (pullbackExtension S f).Splitting) :
    ∃ g : H →* E, S.rightHom.comp g = f :=
  (S.nonempty_splitting_pullback_iff_exists_lift f).mp ⟨σ⟩

example (S : GroupExtension N E G) (f : H →* G)
    (g : H →* E) (hg : S.rightHom.comp g = f) :
    Nonempty (pullbackExtension S f).Splitting :=
  (S.nonempty_splitting_pullback_iff_exists_lift f).mpr ⟨g, hg⟩

-- Only target centrality and source perfectness are needed for unique lifting.
example (S : GroupExtension N E G) (hS : S.IsCentral)
    [Group.IsPerfect H] (f : H →* G)
    (hsplit : Nonempty (pullbackExtension S f).Splitting) :
    ∃! g : H →* E, S.rightHom.comp g = f := by
  obtain ⟨g, hg⟩ := (S.nonempty_splitting_pullback_iff_exists_lift f).mp hsplit
  refine ⟨g, hg, fun k hk ↦ ?_⟩
  exact MonoidHom.eq_of_comp_eq_of_ker_le_center hS (hk.trans hg.symm)

end IndependentUniverses

section Recognition

variable {N : Type u} {E : Type v} {G : Type w}
variable [Group N] [Group E] [Group G] [Group.IsPerfect E]

-- Kernel, total and base universes remain separate in recognition.
example (S : GroupExtension N E G) (hS : S.IsCentral)
    (hsplit : ∀ {N' : Type u} {E' : Type v} [Group N'] [Group E']
      (T : GroupExtension N' E' E), T.IsCentral → Nonempty T.Splitting) :
    S.IsUniversal :=
  hS.isUniversal_of_splits hsplit

example (S : GroupExtension N E G) (hS : S.IsCentral)
    (hsplit : ∀ {N' : Type u} {E' : Type v} [Group N'] [Group E']
      (T : GroupExtension N' E' E), T.IsCentral → Nonempty T.Splitting)
    {N' : Type u} {E' : Type v} [Group N'] [Group E']
    (T : GroupExtension N' E' G) (hT : T.IsCentral) :
    ∃! f : E →* E', T.rightHom.comp f = S.rightHom :=
  (hS.isUniversal_of_splits hsplit).2 T hT

end Recognition

#print axioms GroupExtension.nonempty_splitting_pullback_iff_exists_lift
#print axioms GroupExtension.IsCentral.isUniversal_of_splits
