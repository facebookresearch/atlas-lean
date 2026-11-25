/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

-- BACKPORT: Adapted from PR `leanprover-community/mathlib4#41750` head
-- `78cb073b61a059e5450d7763216c398c12d8c89f`, path
-- `Mathlib/CategoryTheory/MorphismProperty/TrivialBundles.lean`,
-- blob `3a9698748c747784c77b34a8d306c6f68bf0a9bd`.
-- See `BACKPORTS.md` for the extracted surface, local adaptations, and removal condition.

public import MathlibExt.CategoryTheory.TrivialBundleWithFiber

/-!
# Fixed-fiber trivial bundles over terminal bases

This file supplies the two terminal-base constructions needed by the
minimal-fibration development. A map to a terminal object is a trivial bundle
with its source as fiber. Consequently, a pullback along a map which factors
through a terminal object is a trivial bundle with the canonical fiber over
that terminal object.

No morphism property, gluing result, chart, or model-category structure is
introduced here.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

namespace TrivialBundleWithFiber

variable {C : Type u} [Category.{v} C]

/-- A map `p : E ⟶ B` to a terminal object is a trivial bundle with fiber `E`.
The second projection is the identity of `E`. -/
def ofIsTerminal {E B : C} (p : E ⟶ B) (hB : IsTerminal B) :
    TrivialBundleWithFiber E p where
  r := 𝟙 E
  isLimit :=
    BinaryFan.isLimitMk (fun s ↦ s.snd) (fun s ↦ hB.hom_ext _ _)
      (fun s ↦ by simp) (fun s m _ hm ↦ by simpa using hm)

set_option backward.isDefEq.respectTransparency false in
/-- A pullback along a map which factors through a terminal object is a
trivial bundle with the canonical fiber over that terminal object.

Given a pullback presentation of `p : E ⟶ B` along `f : B' ⟶ B` and a
factorization `f = a ≫ b` through a terminal object `T`, the fixed fiber is
exactly `Limits.pullback p b`. -/
noncomputable def ofIsPullbackOfFac {E E' B B' : C} {p' : E' ⟶ B'}
    {p : E ⟶ B} {f : B' ⟶ B} {f' : E' ⟶ E}
    (sq : IsPullback f' p' p f) {T : C} (hT : IsTerminal T)
    (a : B' ⟶ T) (b : T ⟶ B) (fac : a ≫ b = f) [HasPullback p b] :
    TrivialBundleWithFiber (Limits.pullback p b) p' := by
  have sq' :
      IsPullback
        (Limits.pullback.lift f' (p' ≫ a) (by simp [fac, sq.w])) p'
        (Limits.pullback.snd p b) a :=
    .of_right (by simpa [fac]) (by simp) (.of_hasPullback p b)
  exact (ofIsTerminal (Limits.pullback.snd p b) hT).pullback sq'

end TrivialBundleWithFiber

end CategoryTheory
