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

public import Mathlib.CategoryTheory.Abelian.Exact
public import MathlibExt.CategoryTheory.ExactCategory.Basic

/-!
# Abelian categories are exact categories

Every abelian category is canonically an exact category by taking the admissible exact
sequences to be all short exact sequences.

-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Any monomorphism is admissible via its cokernel -/
lemma admissibleMono_of_mono {X Y : C} (i : X ⟶ Y) [Mono i] :
    admissibleMonosOf C (fun S => S.ShortExact) i :=
  ⟨cokernel i, cokernel.π i, by simp,
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i) inferInstance inferInstance
  ⟩

/-- Any epimorphism is admissible via its kernel -/
lemma admissibleEpi_of_epi {Y Z : C} (p : Y ⟶ Z) [Epi p] :
    admissibleEpisOf C (fun S => S.ShortExact) p :=
  ⟨kernel p, kernel.ι p, by simp,
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p) inferInstance inferInstance
  ⟩

lemma admissibleMonosOf_shortExact_eq :
    admissibleMonosOf C (fun S : ShortComplex C => S.ShortExact)
      = MorphismProperty.monomorphisms C := by
  ext X Y i
  constructor
  · rintro ⟨Z, g, w, h⟩
    exact h.mono_f
  · intro hi
    have : Mono i := hi
    exact admissibleMono_of_mono i

lemma admissibleEpisOf_shortExact_eq :
    admissibleEpisOf C (fun S : ShortComplex C => S.ShortExact)
      = MorphismProperty.epimorphisms C := by
  ext Y Z p
  constructor
  · rintro ⟨X, f, w, h⟩
    exact h.epi_g
  · intro hp
    have : Epi p := hp
    exact admissibleEpi_of_epi p

/-- Every abelian category is an exact category where the admissible exact sequences
are all short exact sequences. -/
instance (priority := 100) Abelian.instExactCategory : ExactCategory C where
  IsAdmissibleExact S := S.ShortExact
  shortExact_of_isAdmissibleExact _ h := h
  isLimit_kernelFork := fun {S} hS => ⟨hS.fIsKernel⟩
  isColimit_cokernelCofork := fun {S} hS => ⟨hS.gIsCokernel⟩
  isAdmissibleExact_of_iso := fun {_ _} e h => ShortComplex.shortExact_of_iso e h
  isAdmissibleExact_split X Y :=
    (⟨biprod.fst, biprod.inr, by simp, by simp, by simp⟩ :
      (ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Y) biprod.snd (by simp)).Splitting).shortExact
  admissibleMono_comp := by rw [admissibleMonosOf_shortExact_eq]; infer_instance
  admissibleEpi_comp := by rw [admissibleEpisOf_shortExact_eq]; infer_instance
  admissibleMono_pushout := by
    rintro X Y i ⟨Z, g, w, h⟩ X' f
    have : Mono i := h.mono_f
    exact ⟨pushout f i, pushout.inl f i, pushout.inr f i, IsPushout.of_hasPushout f i,
      admissibleMono_of_mono (pushout.inl f i)⟩
  admissibleEpi_pullback := by
    rintro Y Z p ⟨X, f, w, h⟩ Z' g
    have : Epi p := h.epi_g
    exact ⟨pullback g p, pullback.fst g p, pullback.snd g p, IsPullback.of_hasPullback g p,
      admissibleEpi_of_epi (pullback.fst g p)⟩

end CategoryTheory
