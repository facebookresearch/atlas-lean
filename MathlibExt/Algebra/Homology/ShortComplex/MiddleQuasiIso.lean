/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Middle-term quasi-isomorphisms of short exact complexes

For a morphism between short exact short complexes of homological
complexes over an abelian category, quasi-isomorphisms on the two
outer terms imply a quasi-isomorphism on the middle term.
-/

@[expose] public section

open CategoryTheory ComposableArrows Abelian

namespace HomologicalComplex

namespace HomologySequence

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

include hS₁ hS₂

lemma mono_homologyMap_τ₂ (i : ι)
    (h₁ : ∀ j, c.Rel j i → Epi (homologyMap φ.τ₃ j))
    (h₂ : Mono (homologyMap φ.τ₁ i))
    (h₃ : Mono (homologyMap φ.τ₃ i)) :
    Mono (homologyMap φ.τ₂ i) := by
  by_cases hi : ∃ j, c.Rel j i
  · obtain ⟨j, hji⟩ := hi
    exact mono_of_epi_of_mono_of_mono'' (show 2 + 3 ≤ 5 by omega)
      (composableArrows₅_exact hS₁ j i hji) (composableArrows₅_exact hS₂ j i hji)
      (mapComposableArrows₅ φ hS₁ hS₂ j i hji) 2 3 4 5 rfl rfl rfl rfl
      (h₁ j hji) h₂ h₃
  · have : Mono S₂.f := hS₂.mono_f
    have : Mono (S₂.f.f i) := inferInstance
    have h_mono_f : Mono (homologyMap S₂.f i) :=
      HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S₂.f i (by simpa using hi)
    exact mono_of_mono_of_mono_of_mono (mapComposableArrows₂ φ i)
      (composableArrows₂_exact hS₁ i) h_mono_f h₂ h₃

lemma epi_homologyMap_τ₂ (i : ι)
    (h₁ : Epi (homologyMap φ.τ₁ i))
    (h₂ : Epi (homologyMap φ.τ₃ i))
    (h₃ : ∀ j, c.Rel i j → Mono (homologyMap φ.τ₁ j)) :
    Epi (homologyMap φ.τ₂ i) := by
  by_cases hi : ∃ j, c.Rel i j
  · obtain ⟨j, hij⟩ := hi
    exact epi_of_epi_of_epi_of_mono'' (show 0 + 3 ≤ 5 by omega)
      (composableArrows₅_exact hS₁ i j hij) (composableArrows₅_exact hS₂ i j hij)
      (mapComposableArrows₅ φ hS₁ hS₂ i j hij) 0 1 2 3 rfl rfl rfl rfl
      h₁ h₂ (h₃ j hij)
  · have : Epi S₁.g := hS₁.epi_g
    have : Epi (S₁.g.f i) := inferInstance
    have h_epi_g : Epi (homologyMap S₁.g i) :=
      HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S₁.g i (by simpa using hi)
    exact epi_of_epi_of_epi_of_epi (mapComposableArrows₂ φ i)
      (composableArrows₂_exact hS₂ i) h_epi_g h₁ h₂

lemma isIso_homologyMap_τ₂ (i : ι)
    (h₁ : IsIso (homologyMap φ.τ₁ i))
    (h₂ : IsIso (homologyMap φ.τ₃ i))
    (h₃ : ∀ j, c.Rel j i → IsIso (homologyMap φ.τ₃ j))
    (h₄ : ∀ j, c.Rel i j → IsIso (homologyMap φ.τ₁ j)) :
    IsIso (homologyMap φ.τ₂ i) := by
  have hMono : Mono (homologyMap φ.τ₂ i) := by
    apply mono_homologyMap_τ₂ φ hS₁ hS₂ i
    · intro j hj
      have := h₃ j hj
      infer_instance
    · infer_instance
    · infer_instance
  have hEpi : Epi (homologyMap φ.τ₂ i) := by
    apply epi_homologyMap_τ₂ φ hS₁ hS₂ i
    · infer_instance
    · infer_instance
    · intro j hj
      have := h₄ j hj
      infer_instance
  exact isIso_of_mono_of_epi _

/-- Five-lemma adapter: in a morphism between short exact short complexes of
homological complexes over an abelian category, if the outer vertical maps
`τ₁` and `τ₃` are quasi-isomorphisms, then so is the middle `τ₂`. Same
generality and notation as Mathlib's `quasiIso_τ₃`. -/
theorem quasiIso_τ₂ (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply isIso_homologyMap_τ₂ φ hS₁ hS₂
  all_goals infer_instance

end HomologySequence

end HomologicalComplex
