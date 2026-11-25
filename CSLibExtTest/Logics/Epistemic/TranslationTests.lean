/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Epistemic.Translation
public import CSLibExtTest.Logics.Epistemic.PublicAnnouncementTests

namespace Cslib.Epistemic.TranslationTests

open Cslib.Epistemic

/-- The concrete announcement-language formula "announce heads, then
agent `1` knows heads". -/
def headsThenKnows : AnnFormula Unit (Fin 2) :=
  .announce (.atom ()) (.know 1 (.atom ()))

/-- Evaluating the translation itself at `true` in the two-agent coin
model: the guarded knowledge body holds. -/
example : Sat muddy (translateTop headsThenKnows) true := by
  intro _ v _ hv
  cases v with
  | false => exact False.elim (Bool.false_ne_true ((((sat_and (M := muddy)).mp hv).2) id))
  | true => rfl

/-- At `false` the same translation is vacuously true: its ambient
condition (heads, after the trivial announcement) fails there. -/
example : Sat muddy (translateTop headsThenKnows) false :=
  fun h => (Bool.false_ne_true ((((sat_and (M := muddy)).mp h).2) id)).elim

/-- The translated formula is free of announcements and common
knowledge, checked by computation. -/
example : (translateTop headsThenKnows).AnnCommonFree := by
  simp [translateTop, translate, headsThenKnows, Formula.and, Formula.AnnCommonFree]

/-- Order matters for nested announcements: after heads is announced,
agent `1` knows heads, so "`1` does not know heads" cannot be announced
afterwards; `[!p][!¬K₁p]⊥` holds vacuously at `true`. -/
example :
    Sat muddy (translateTop
      (.announce (.atom ())
        (.announce (.imp (.know 1 (.atom ())) .bot) .bot))) true := by
  rw [sat_translateTop]
  intro _ hχ
  exact hχ (fun v hv _ => hv)

/-- The other order fails at `true`: first announcing that agent `1`
does not know heads (true before any announcement) and then heads
leaves the body `⊥` to hold at `true`, which it does not. -/
example :
    ¬ Sat muddy (translateTop
      (.announce (.imp (.know 1 (.atom ())) .bot)
        (.announce (.atom ()) .bot))) true := by
  intro h
  have hg : Sat muddy (.imp (.know 1 (.atom ())) .bot) true :=
    fun hk => Bool.false_ne_true (hk false trivial)
  exact (sat_translateTop muddy _).mp h hg rfl

end Cslib.Epistemic.TranslationTests
