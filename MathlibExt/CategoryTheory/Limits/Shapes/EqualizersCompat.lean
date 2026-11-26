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
# Universal fork and cofork constructions by cancellation

Let f,g : X ⟶ Y be parallel arrows in a category C. For a fork t with monic leg t.ι : t.pt →
X, a lift of every fork s satisfying lift(s) ≫ t.ι = s.ι is automatically unique, so it
defines a limiting fork. Dually, for a cofork t with epic leg t.π : Y → t.pt, descendants
satisfying t.π ≫ desc(s) = s.π are automatically unique and define a colimiting cofork.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {X Y : C} {f g : X ⟶ Y}

/-- Limiting fork from factorization through a monic leg.

For parallel arrows f,g : X → Y, let t be a fork with monic leg t.ι. Suppose every fork s has
a map lift(s) : s.pt → t.pt satisfying lift(s) ≫ t.ι = s.ι. Cancellation of t.ι gives
uniqueness of each lift, and these data make t a limit fork. -/
def Fork.IsLimit.ofMono (t : Fork f g) [Mono t.ι] (lift : ∀ s : Fork f g, s.pt ⟶ t.pt)
    (fac : ∀ s : Fork f g, lift s ≫ Fork.ι t = Fork.ι s) : IsLimit t :=
  Fork.IsLimit.mk t lift fac fun _ _ eq ↦ (cancel_mono t.ι).mp <| by rw [eq, fac]

/-- Colimiting cofork from factorization through an epic leg.

For parallel arrows f,g : X → Y, let t be a cofork with epic leg t.π. Suppose every cofork s
has a map desc(s) : t.pt → s.pt satisfying t.π ≫ desc(s) = s.π. Cancellation of t.π gives
uniqueness of each descendant, and these data make t a colimit cofork. -/
def Cofork.IsColimit.ofEpi (t : Cofork f g) [Epi t.π] (desc : ∀ s : Cofork f g, t.pt ⟶ s.pt)
    (fac : ∀ s : Cofork f g, t.π ≫ desc s = Cofork.π s) : IsColimit t :=
  Cofork.IsColimit.mk t desc fac fun _ _ eq ↦ (cancel_epi t.π).mp <| by rw [eq, fac]

end CategoryTheory.Limits

end
