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
# Exactness transport and universal cokernel comparisons

Let S be an exact short complex in a category with zero morphisms. Three object isomorphisms
compatible with two specified target arrows transport both their zero composite and exactness to
the target complex.

In an abelian category, if S₁ → S₂ → S₃ is exact and its second arrow is an epimorphism, then
the universal map coker(S₁ → S₂) → S₃ is an isomorphism.
-/

@[expose] public section

namespace CategoryTheory.ShortComplex

open Category Limits

/-- Let E have zero morphisms and let S be an exact short complex. Suppose e₁ : S₁ ≅ A, e₂ : S₂ ≅ B
and e₃ : S₃ ≅ D satisfy e₂ ∘ S.f = f ∘ e₁ and e₃ ∘ S.g = g ∘ e₂ for f : A → B and g : B → D.
Then g ∘ f=0 and the resulting short complex A → B → D is exact. -/
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

/-- Let E be abelian and let S₁ → S₂ → S₃ be exact. If S₂ → S₃ is an epimorphism, the universal
cokernel map coker(S₁ → S₂) → S₃ induced by the second arrow is an isomorphism. -/
lemma Exact.isIso_cokernel_desc {E : Type*} [Category E] [Abelian E]
    {S : ShortComplex E} (hS : S.Exact) [Epi S.g] :
    IsIso (cokernel.desc S.f S.g S.zero) := by
  exact (IsColimit.nonempty_isColimit_iff_isIso_desc (cokernelIsCokernel S.f)).mp
    ⟨hS.gIsCokernel⟩

/-- Let E be abelian and let S₁ → S₂ → S₃ be exact with the second arrow an epimorphism. The
canonical isomorphism coker(S₁ → S₂) ≅ S₃ is the one induced by the universal cokernel
factorization of S₂ → S₃. -/
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
