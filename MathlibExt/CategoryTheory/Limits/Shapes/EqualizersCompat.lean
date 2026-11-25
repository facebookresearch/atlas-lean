/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Markus Himmel
-/
module

-- BACKPORT: Extracted from PR #42860 head `4d9c97ac1bb4deb8ce8e6005aca99087372c2d77`,
-- path `Mathlib/CategoryTheory/Limits/Shapes/Equalizers.lean`,
-- blob `64f06b77f71c1de40d4fe678dbb6ee4702bed3fc`, authors Junyan Xu.
-- See `BACKPORTS.md` for copied surface, adaptations, and upgrade-removal steps.

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Limits of forks from monomorphisms, colimits of coforks from epimorphisms (backport)

Backports `Fork.IsLimit.ofMono` and `Cofork.IsColimit.ofEpi` from upstream
PR #42860 (head `4d9c97ac1bb4deb8ce8e6005aca99087372c2d77`,
path `Mathlib/CategoryTheory/Limits/Shapes/Equalizers.lean`,
blob `64f06b77f71c1de40d4fe678dbb6ee4702bed3fc`).
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {X Y : C} {f g : X ⟶ Y}

/-- The `uniq` condition in `Fork.IsLimit.mk` can be replaced by `Fork.ι` being a monomorphism. -/
def Fork.IsLimit.ofMono (t : Fork f g) [Mono t.ι] (lift : ∀ s : Fork f g, s.pt ⟶ t.pt)
    (fac : ∀ s : Fork f g, lift s ≫ Fork.ι t = Fork.ι s) : IsLimit t :=
  Fork.IsLimit.mk t lift fac fun _ _ eq ↦ (cancel_mono t.ι).mp <| by rw [eq, fac]

/-- The `uniq` condition in `Cofork.IsColimit.mk` can be replaced by `Cofork.π` being an
epimorphism. -/
def Cofork.IsColimit.ofEpi (t : Cofork f g) [Epi t.π] (desc : ∀ s : Cofork f g, t.pt ⟶ s.pt)
    (fac : ∀ s : Cofork f g, t.π ≫ desc s = Cofork.π s) : IsColimit t :=
  Cofork.IsColimit.mk t desc fac fun _ _ eq ↦ (cancel_epi t.π).mp <| by rw [eq, fac]

end CategoryTheory.Limits

end
