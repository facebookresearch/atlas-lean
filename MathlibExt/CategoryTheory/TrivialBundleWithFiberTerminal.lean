/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
See NOTICE in the repository root for the original Mathlib attribution.
-/

module

-- BACKPORT: Terminal-base constructors adapted from Mathlib PR #41750,
-- head `78cb073b61a059e5450d7763216c398c12d8c89f`,
-- `Mathlib/CategoryTheory/MorphismProperty/TrivialBundles.lean`,
-- blob `3a9698748c747784c77b34a8d306c6f68bf0a9bd`.
-- The local fixed-fiber record is retained; see `BACKPORTS.md`.

public import MathlibExt.CategoryTheory.TrivialBundleWithFiber

/-!
# Fixed-fiber trivial bundles over terminal bases

A map to a terminal object has a product presentation with its original source as fiber. Pulling
a map back along a base map factored through a terminal object gives a product presentation with
the canonical fiber over that terminal point. The original factorization, pullback and second
projection are retained.

The compatibility scope against Mathlib 4.35.0 (`56a005855ea17e0b0958f73ec801ae140b0a1679`) and
its removal conditions are recorded in `BACKPORTS.md`.
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
