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

public import MathlibExt.GroupTheory.GroupExtension.Pullback

/-!
# Recognition of universal central extensions

A homomorphism lifts through a group extension exactly when the corresponding
pullback extension splits. The kernel, total group, base group and source of
the homomorphism may lie in independent universes. A central extension with
perfect total group is universal when every central extension of its total
group splits in the kernel and total universes of the original extension.
-/

@[expose] public section

universe u v w x

namespace GroupExtension

variable {N : Type u} {E : Type v} {G : Type w}
variable [Group N] [Group E] [Group G]

/-- The pullback of a group extension along `f` splits if and only if `f`
lifts through its original projection. -/
theorem nonempty_splitting_pullback_iff_exists_lift
    {H : Type x} [Group H] (S : GroupExtension N E G) (f : H →* G) :
    Nonempty (pullbackExtension S f).Splitting ↔
      ∃ g : H →* E, S.rightHom.comp g = f := by
  constructor
  · rintro ⟨σ⟩
    refine ⟨(pullbackFst S f).comp σ.toMonoidHom, ?_⟩
    ext h
    change S.rightHom (pullbackFst S f (σ h)) = f h
    calc
      S.rightHom (pullbackFst S f (σ h)) =
          f (pullbackSnd S f (σ h)) := pullback_condition S f (σ h)
      _ = f h := congrArg f (σ.rightHom_splitting h)
  · rintro ⟨g, hg⟩
    refine ⟨Splitting.mk
      (pullbackLift S g (MonoidHom.id H) (by simpa only [MonoidHom.comp_id] using hg)) ?_⟩
    intro h
    rfl

/-- A central extension with perfect total group is universal if every central
extension of its total group in the same kernel and total universes splits. -/
theorem IsCentral.isUniversal_of_splits {S : GroupExtension N E G}
    (hS : S.IsCentral) [Group.IsPerfect E]
    (hsplit : ∀ {N' : Type u} {E' : Type v} [Group N'] [Group E']
      (T : GroupExtension N' E' E), T.IsCentral → Nonempty T.Splitting) :
    S.IsUniversal := by
  refine ⟨hS, ?_⟩
  intro N' E' _ _ T hT
  obtain ⟨f, hf⟩ := (T.nonempty_splitting_pullback_iff_exists_lift S.rightHom).mp
    (hsplit (pullbackExtension T S.rightHom) (pullback_isCentral T S.rightHom hT))
  refine ⟨f, hf, fun g hg ↦ ?_⟩
  exact MonoidHom.eq_of_comp_eq_of_ker_le_center hT (hg.trans hf.symm)

end GroupExtension
