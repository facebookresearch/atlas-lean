/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
Author: @toskua, Avocado

Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Copyright (c) 2026 @junekim623, Muse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent, @junekim623, Muse

The cokernel comparison follows the short-exact-sequence argument in
Hartshorne, *Algebraic Geometry* (1977).
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Exactness transport and cokernel comparisons

Exactness transports along compatible isomorphisms of the three objects,
including the zero-composite witness needed to form the target short complex.
For an exact short complex in an abelian category whose second map is epi,
the universal map from the cokernel of its first map is an isomorphism.
-/

@[expose] public section

namespace CategoryTheory.ShortComplex

open Category Limits

/-- Transport exactness and the zero-composite witness along three compatible isomorphisms. -/
lemma exists_exact_of_iso {E : Type*} [Category E] [HasZeroMorphisms E]
    (S : ShortComplex E) (hS : S.Exact) {A B C : E}
    (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ C)
    (f : A ⟶ B) (g : B ⟶ C)
    (hf : e₁.hom ≫ f = S.f ≫ e₂.hom)
    (hg : e₂.hom ≫ g = S.g ≫ e₃.hom) :
    ∃ w : f ≫ g = 0, (ShortComplex.mk f g w).Exact := by
  have hw : f ≫ g = 0 := by
    apply (cancel_epi e₁.hom).mp
    calc
      e₁.hom ≫ (f ≫ g) = S.f ≫ (e₂.hom ≫ g) := by
        rw [← Category.assoc, hf, Category.assoc]
      _ = S.f ≫ (S.g ≫ e₃.hom) := by rw [hg]
      _ = 0 := by rw [← Category.assoc, S.zero, zero_comp]
      _ = e₁.hom ≫ 0 := (comp_zero).symm
  exact ⟨hw, ShortComplex.exact_of_iso (ShortComplex.isoMk e₁ e₂ e₃ hf hg) hS⟩

/-- The universal cokernel map of an exact complex with epi second map is an isomorphism. -/
lemma Exact.isIso_cokernel_desc {E : Type*} [Category E] [Abelian E]
    {S : ShortComplex E} (hS : S.Exact) [Epi S.g] :
    IsIso (cokernel.desc S.f S.g S.zero) := by
  exact (IsColimit.nonempty_isColimit_iff_isIso_desc (cokernelIsCokernel S.f)).mp
    ⟨hS.gIsCokernel⟩

/-- The cokernel of the incoming map identifies with the target when the
short complex is exact and the outgoing map is epi. -/
noncomputable def cokernelDescIsoOfExactOfEpi {E : Type*} [Category E]
    [Abelian E] {S : ShortComplex E} (hS : S.Exact) [Epi S.g] :
    cokernel S.f ≅ S.X₃ :=
  @asIso _ _ _ _ (cokernel.desc S.f S.g S.zero) hS.isIso_cokernel_desc

@[simp]
theorem cokernelDescIsoOfExactOfEpi_hom {E : Type*} [Category E]
    [Abelian E] {S : ShortComplex E} (hS : S.Exact) [Epi S.g] :
    (cokernelDescIsoOfExactOfEpi hS).hom =
      cokernel.desc S.f S.g S.zero :=
  rfl

end CategoryTheory.ShortComplex
