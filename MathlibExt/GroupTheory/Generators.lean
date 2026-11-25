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

public import Mathlib.GroupTheory.Generators

/-!
# Descent from free groups along generating families

A generating family `P : Group.Generators G ι` presents `G` as a quotient of
the free group on `ι` through the canonical surjection `P.lift`.  A homomorphism
out of that free group therefore descends to `G` whenever it kills the kernel
of `P.lift`.
-/

@[expose] public section

namespace Group.Generators

universe u v w

variable {G : Type u} {H : Type v} {ι : Type w} [Group G] [Group H]

/-- Descend a homomorphism from the free group on a generating family to the
generated group. -/
noncomputable def desc (P : Group.Generators G ι)
    (f : FreeGroup ι →* H) (hker : P.lift.ker ≤ f.ker) : G →* H :=
  P.lift.liftOfSurjective P.lift_surjective ⟨f, hker⟩

/-- Descending and then precomposing with the canonical free-group lift
recovers the original homomorphism. -/
@[simp]
theorem desc_comp_lift (P : Group.Generators G ι)
    (f : FreeGroup ι →* H) (hker : P.lift.ker ≤ f.ker) :
    (P.desc f hker).comp P.lift = f := by
  apply MonoidHom.ext
  intro x
  simp [desc, MonoidHom.liftOfSurjective]

/-- Pointwise computation of descent after the canonical free-group lift. -/
@[simp]
theorem desc_lift (P : Group.Generators G ι)
    (f : FreeGroup ι →* H) (hker : P.lift.ker ≤ f.ker)
    (x : FreeGroup ι) :
    P.desc f hker (P.lift x) = f x := by
  have h := DFunLike.congr_fun (P.desc_comp_lift f hker) x
  exact h

/-- Descent computes on a named generator by evaluating the original
free-group homomorphism on the corresponding free generator. -/
@[simp]
theorem desc_val (P : Group.Generators G ι)
    (f : FreeGroup ι →* H) (hker : P.lift.ker ≤ f.ker) (i : ι) :
    P.desc f hker (P.val i) = f (FreeGroup.of i) := by
  simpa only [Group.Generators.lift, FreeGroup.lift_apply_of] using
    P.desc_lift f hker (FreeGroup.of i)

/-- A homomorphism out of the generated group is the descent of its composite
with the canonical free-group lift. -/
theorem desc_unique (P : Group.Generators G ι)
    (f : FreeGroup ι →* H) (hker : P.lift.ker ≤ f.ker)
    (g : G →* H) (hg : g.comp P.lift = f) :
    g = P.desc f hker := by
  apply P.hom_ext
  intro i
  calc
    g (P.val i) = f (FreeGroup.of i) := by
      have hi := DFunLike.congr_fun hg (FreeGroup.of i)
      simpa using hi
    _ = P.desc f hker (P.val i) := (P.desc_val f hker i).symm

/-- Characterization of the descended homomorphism by its composite with the
canonical free-group lift. -/
theorem eq_desc_iff_comp_lift_eq (P : Group.Generators G ι)
    (f : FreeGroup ι →* H) (hker : P.lift.ker ≤ f.ker)
    (g : G →* H) :
    g = P.desc f hker ↔ g.comp P.lift = f := by
  constructor
  · rintro rfl
    exact P.desc_comp_lift f hker
  · exact P.desc_unique f hker g

end Group.Generators
