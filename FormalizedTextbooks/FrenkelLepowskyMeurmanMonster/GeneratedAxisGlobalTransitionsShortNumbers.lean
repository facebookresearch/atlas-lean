/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonShortData

/-! Injective arithmetic labels for every original preferred short coordinate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- The three actual preferred short families occupy disjoint original finite coordinate intervals. -/
def generatedAxisGlobalShortNumber : GriessShortIndex → ℕ
  | Sum.inl (s, p) => 276 * s.val + p.val
  | Sum.inr (Sum.inl (o, e)) => 552 + 64 * o.val + e.val
  | Sum.inr (Sum.inr (d, i)) => 49128 + 24 * d.val + i.val

/-- These exact arithmetic coordinate labels distinguish every original preferred short unit. -/
theorem generatedAxisGlobalShortNumber_injective :
    Function.Injective generatedAxisGlobalShortNumber := by
  intro a b h
  rcases a with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  all_goals rcases b with ⟨s', p'⟩ | (⟨o', e'⟩ | ⟨d', i'⟩)
  all_goals simp only [generatedAxisGlobalShortNumber] at h
  all_goals try omega
  · have hs : s = s' := Fin.ext (by omega)
    have hp : p = p' := Fin.ext (by omega)
    simp [hs, hp]
  · have ho : o = o' := Fin.ext (by omega)
    have he : e = e' := Fin.ext (by omega)
    simp [ho, he]
  · have hd : d = d' := Fin.ext (by omega)
    have hi : i = i' := Fin.ext (by omega)
    simp [hd, hi]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
