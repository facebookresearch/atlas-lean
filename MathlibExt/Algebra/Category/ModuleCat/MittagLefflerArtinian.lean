/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: @toskua
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Artinian.Module

/-!
# Artinian images and Mittag–Leffler module diagrams

For a cofiltered-or-empty diagram of R-modules, suppose each object receives a transition map
with Artinian image. Descending submodules inside that image then stabilize, giving the
Mittag–Leffler condition for the underlying diagram of sets.

In particular, diagrams of Artinian modules, finitely generated modules over an Artinian ring,
and finite-dimensional vector spaces over a division ring satisfy this condition. Finiteness
is imposed separately at each object; the category, morphism, ring and coefficient universes
remain as stated.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v w t

namespace ModuleCat

variable {J : Type v} [Category.{t} J] [IsCofilteredOrEmpty J]
variable {R : Type u} [Ring R]

/-- Artinian incoming images imply the Mittag–Leffler condition.

For each j, assume some map i → j has Artinian linear range in A_j. Then the underlying-set
diagram of the cofiltered module diagram A is Mittag–Leffler. -/
theorem isMittagLeffler_of_exists_artinian_range
    (A : J ⥤ ModuleCat.{w} R)
    (hA : ∀ j : J, ∃ (i : J) (f : i ⟶ j),
      IsArtinian R (LinearMap.range (A.map f).hom)) :
    (A ⋙ forget (ModuleCat.{w} R)).IsMittagLeffler := by
  rw [Functor.isMittagLeffler_iff_subset_range_comp]
  intro j
  obtain ⟨i, f, hf⟩ := hA j
  let I : Submodule R (A.obj j) := LinearMap.range (A.map f).hom
  have : IsArtinian R I := hf
  let fI : A.obj i →ₗ[R] I := (A.map f).hom.rangeRestrict
  let images : Set (Submodule R I) :=
    {N | ∃ (k : J) (g : k ⟶ i), N = LinearMap.range (fI.comp (A.map g).hom)}
  have hnonempty : images.Nonempty :=
    ⟨LinearMap.range (fI.comp (A.map (𝟙 i)).hom), i, 𝟙 i, rfl⟩
  obtain ⟨N, ⟨k, g, rfl⟩, hmin⟩ :=
    IsArtinian.set_has_minimal (R := R) (M := I) images hnonempty
  refine ⟨k, g ≫ f, ?_⟩
  intro l h
  have hcomp :
      fI.comp (A.map (h ≫ g)).hom =
        (fI.comp (A.map g).hom).comp (A.map h).hom := by
    simp only [A.map_comp, ModuleCat.hom_comp, LinearMap.comp_assoc]
  have hle :
      LinearMap.range (fI.comp (A.map (h ≫ g)).hom) ≤
        LinearMap.range (fI.comp (A.map g).hom) := by
    rw [hcomp]
    rintro _ ⟨x, rfl⟩
    exact ⟨(A.map h).hom x, rfl⟩
  have heq :
      LinearMap.range (fI.comp (A.map (h ≫ g)).hom) =
        LinearMap.range (fI.comp (A.map g).hom) :=
    eq_of_le_of_not_lt hle (hmin _ ⟨l, h ≫ g, rfl⟩)
  rintro _ ⟨x, rfl⟩
  have hx :
      fI ((A.map g).hom x) ∈ LinearMap.range (fI.comp (A.map (h ≫ g)).hom) := by
    rw [heq]
    exact ⟨x, rfl⟩
  obtain ⟨x', hx'⟩ := hx
  refine ⟨x', ?_⟩
  have hval := congrArg Subtype.val hx'
  change (A.map f).hom ((A.map (h ≫ g)).hom x') =
    (A.map f).hom ((A.map g).hom x) at hval
  change (A.map (h ≫ (g ≫ f))).hom x' = (A.map (g ≫ f)).hom x
  simpa only [A.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] using hval

/-- A cofiltered diagram of Artinian modules is Mittag–Leffler.

If every module A_j is Artinian, the underlying-set diagram satisfies eventual stabilization
of the incoming images. -/
theorem isMittagLeffler_of_isArtinian
    (A : J ⥤ ModuleCat.{w} R) (hA : ∀ j : J, IsArtinian R (A.obj j)) :
    (A ⋙ forget (ModuleCat.{w} R)).IsMittagLeffler := by
  apply isMittagLeffler_of_exists_artinian_range
  intro j
  have : IsArtinian R (A.obj j) := hA j
  exact ⟨j, 𝟙 j, inferInstance⟩

/-- Finite modules over an Artinian ring form a Mittag–Leffler diagram.

For an Artinian ring R, if each coefficient module A_j is finitely generated, the cofiltered
underlying-set diagram is Mittag–Leffler. -/
theorem isMittagLeffler_of_moduleFinite [IsArtinianRing R]
    (A : J ⥤ ModuleCat.{w} R) (hA : ∀ j : J, Module.Finite R (A.obj j)) :
    (A ⋙ forget (ModuleCat.{w} R)).IsMittagLeffler := by
  apply isMittagLeffler_of_isArtinian
  intro j
  have : Module.Finite R (A.obj j) := hA j
  infer_instance

section DivisionRing

variable {K : Type u} [DivisionRing K]

/-- Finite-dimensional vector-space diagrams are Mittag–Leffler.

For a division ring K and a cofiltered-or-empty diagram of finite-dimensional K-modules, the
underlying-set diagram is Mittag–Leffler. -/
theorem isMittagLeffler_of_finiteDimensional
    (A : J ⥤ ModuleCat.{w} K) (hA : ∀ j : J, FiniteDimensional K (A.obj j)) :
    (A ⋙ forget (ModuleCat.{w} K)).IsMittagLeffler :=
  isMittagLeffler_of_moduleFinite A hA

end DivisionRing

end ModuleCat
