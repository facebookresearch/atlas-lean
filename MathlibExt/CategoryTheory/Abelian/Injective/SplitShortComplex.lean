/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Injective split short complexes

A split short exact complex with injective endpoints is injective in the
category of short complexes. Its lifting property extends commutative
diagrams across monomorphisms.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A split exact short complex with injective endpoints extends every diagram
morphism through a monomorphism of short complexes. -/
theorem Splitting.injective {T : ShortComplex C} (s : T.Splitting)
    [Injective T.X₁] [Injective T.X₃] : Injective T where
  factors {A B} φ m := by
    intro hm
    let : Mono m := hm
    have hm₂ : Mono m.τ₂ := (ShortComplex.π₂ : ShortComplex C ⥤ C).map_mono m
    have hm₃ : Mono m.τ₃ := (ShortComplex.π₃ : ShortComplex C ⥤ C).map_mono m
    let u : B.X₂ ⟶ T.X₁ := Injective.factorThru (φ.τ₂ ≫ s.r) m.τ₂
    let v : B.X₃ ⟶ T.X₃ := Injective.factorThru φ.τ₃ m.τ₃
    have hu : m.τ₂ ≫ u = φ.τ₂ ≫ s.r := Injective.comp_factorThru _ _
    have hv : m.τ₃ ≫ v = φ.τ₃ := Injective.comp_factorThru _ _
    let ψ : B ⟶ T :=
      { τ₁ := B.f ≫ u
        τ₂ := u ≫ T.f + B.g ≫ v ≫ s.s
        τ₃ := v
        comm₁₂ := by
          simp only [Preadditive.comp_add, ← Category.assoc,
            B.zero, zero_comp, add_zero]
        comm₂₃ := by
          simp only [Preadditive.add_comp, Category.assoc, T.zero, comp_zero,
            s.s_g, Category.comp_id, zero_add] }
    refine ⟨ψ, ?_⟩
    apply ShortComplex.hom_ext
    · change m.τ₁ ≫ B.f ≫ u = φ.τ₁
      rw [← Category.assoc, m.comm₁₂, Category.assoc, hu, ← Category.assoc,
        ← φ.comm₁₂, Category.assoc, s.f_r, Category.comp_id]
    · change m.τ₂ ≫ (u ≫ T.f + B.g ≫ v ≫ s.s) = φ.τ₂
      simp only [Preadditive.comp_add]
      rw [reassoc_of% hu, reassoc_of% m.comm₂₃, reassoc_of% hv,
        ← reassoc_of% φ.comm₂₃, ← Preadditive.comp_add, s.id, Category.comp_id]
    · exact hv

end CategoryTheory.ShortComplex
