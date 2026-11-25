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

public import MathlibExt.KTheory.Ring.K2.SteinbergPresentation
public import MathlibExt.KTheory.Ring.K2.StableElementaryRelations

/-! # Steinberg-to-elementary homomorphism

The stable Steinberg group maps to the stable elementary group via
`x_{ij}(a) ↦ e_{ij}(a)` on `ℕ`-indexed generators.
-/

namespace AlgebraicKTheory

namespace StableSteinberg

open scoped commutatorElement

universe u

private def steinbergToElementaryAssignment {R : Type u} [Ring R] :
    SteinbergGenerator R → StableE R
  | ⟨i, j, hij, a⟩ => StableE.natElementary i j hij a

private theorem steinbergToElementaryAssignment_free {R : Type u} [Ring R]
    (i j : ℕ) (hij : i ≠ j) (a : R) :
    FreeGroup.lift steinbergToElementaryAssignment
        (SteinbergGenerator.free (R := R) i j hij a) =
      StableE.natElementary (R := R) i j hij a := by
  simp [SteinbergGenerator.free, steinbergToElementaryAssignment,
    FreeGroup.lift_apply_of]

private theorem toStableE_addRel {R : Type u} [Ring R]
    {r : FreeGroup (SteinbergGenerator R)} (hr : r ∈ steinbergAddRel R) :
    FreeGroup.lift steinbergToElementaryAssignment r = 1 := by
  obtain ⟨i, j, hij, a, b, rfl⟩ := hr
  have h1 := steinbergToElementaryAssignment_free (R := R) i j hij a
  have h2 := steinbergToElementaryAssignment_free (R := R) i j hij b
  have h3 := steinbergToElementaryAssignment_free (R := R) i j hij (a + b)
  have hAdd : StableE.natElementary (R := R) i j hij a *
      StableE.natElementary (R := R) i j hij b =
      StableE.natElementary (R := R) i j hij (a + b) :=
    StableE.natElementary_add i j hij a b
  calc FreeGroup.lift steinbergToElementaryAssignment
        (SteinbergGenerator.free (R := R) i j hij a *
          SteinbergGenerator.free (R := R) i j hij b *
            (SteinbergGenerator.free (R := R) i j hij (a + b))⁻¹)
      = StableE.natElementary (R := R) i j hij a *
          StableE.natElementary (R := R) i j hij b *
            (StableE.natElementary (R := R) i j hij (a + b))⁻¹ := by
        simp [h1, h2, h3]
    _ = 1 := by
        calc StableE.natElementary (R := R) i j hij a *
              StableE.natElementary (R := R) i j hij b *
                (StableE.natElementary (R := R) i j hij (a + b))⁻¹
            = StableE.natElementary (R := R) i j hij (a + b) *
                (StableE.natElementary (R := R) i j hij (a + b))⁻¹ := by
              rw [← hAdd]
          _ = 1 := mul_inv_cancel _

private theorem toStableE_commRel {R : Type u} [Ring R]
    {r : FreeGroup (SteinbergGenerator R)} (hr : r ∈ steinbergCommRel R) :
    FreeGroup.lift steinbergToElementaryAssignment r = 1 := by
  obtain ⟨i, j, k, l, hij, hkl, hil, hjk, a, b, rfl⟩ := hr
  have h1 := steinbergToElementaryAssignment_free (R := R) i j hij a
  have h2 := steinbergToElementaryAssignment_free (R := R) k l hkl b
  have hComm : ⁅StableE.natElementary (R := R) i j hij a,
      StableE.natElementary (R := R) k l hkl b⁆ = 1 :=
    StableE.natElementary_comm i j k l hij hkl hil hjk a b
  calc FreeGroup.lift steinbergToElementaryAssignment
        (⁅SteinbergGenerator.free (R := R) i j hij a,
          SteinbergGenerator.free (R := R) k l hkl b⁆)
      = ⁅FreeGroup.lift steinbergToElementaryAssignment
            (SteinbergGenerator.free (R := R) i j hij a),
          FreeGroup.lift steinbergToElementaryAssignment
            (SteinbergGenerator.free (R := R) k l hkl b)⁆ := by
        simp [commutatorElement_def]
    _ = ⁅StableE.natElementary (R := R) i j hij a,
          StableE.natElementary (R := R) k l hkl b⁆ := by
        simp [h1, h2]
    _ = 1 := hComm

private theorem toStableE_chevRel {R : Type u} [Ring R]
    {r : FreeGroup (SteinbergGenerator R)} (hr : r ∈ steinbergChevRel R) :
    FreeGroup.lift steinbergToElementaryAssignment r = 1 := by
  obtain ⟨i, j, k, hij, hjk, hik, a, b, rfl⟩ := hr
  have h1 := steinbergToElementaryAssignment_free (R := R) i j hij a
  have h2 := steinbergToElementaryAssignment_free (R := R) j k hjk b
  have h3 := steinbergToElementaryAssignment_free (R := R) i k hik (a * b)
  have hChev : ⁅StableE.natElementary (R := R) i j hij a,
      StableE.natElementary (R := R) j k hjk b⁆ =
      StableE.natElementary (R := R) i k hik (a * b) :=
    StableE.natElementary_chev i j k hij hjk hik a b
  calc FreeGroup.lift steinbergToElementaryAssignment
        (⁅SteinbergGenerator.free (R := R) i j hij a,
            SteinbergGenerator.free (R := R) j k hjk b⁆ *
          (SteinbergGenerator.free (R := R) i k hik (a * b))⁻¹)
      = ⁅FreeGroup.lift steinbergToElementaryAssignment
            (SteinbergGenerator.free (R := R) i j hij a),
          FreeGroup.lift steinbergToElementaryAssignment
            (SteinbergGenerator.free (R := R) j k hjk b)⁆ *
        (FreeGroup.lift steinbergToElementaryAssignment
            (SteinbergGenerator.free (R := R) i k hik (a * b)))⁻¹ := by
        simp [commutatorElement_def]
    _ = ⁅StableE.natElementary (R := R) i j hij a,
          StableE.natElementary (R := R) j k hjk b⁆ *
        (StableE.natElementary (R := R) i k hik (a * b))⁻¹ := by
        simp [h1, h2, h3, commutatorElement_def]
    _ = 1 := by
        rw [hChev, mul_inv_cancel]

private theorem toStableE_satisfies {R : Type u} [Ring R]
    {r : FreeGroup (SteinbergGenerator R)} (hr : r ∈ steinbergRelations R) :
    FreeGroup.lift steinbergToElementaryAssignment r = 1 := by
  simp only [steinbergRelations, Set.mem_union] at hr
  rcases hr with (hr | hr) | hr
  · exact toStableE_addRel hr
  · exact toStableE_commRel hr
  · exact toStableE_chevRel hr

/-- Canonical map `St(R) →* stable E∞(R)` sending `x_{ij}(a)` to `e_{ij}(a)`. -/
public noncomputable def toStableE {R : Type u} [Ring R] :
    StableSteinberg R →* StableE R :=
  PresentedGroup.toGroup (f := steinbergToElementaryAssignment (R := R))
    (fun _ hr => toStableE_satisfies (R := R) hr)

@[simp]
public theorem toStableE_x {R : Type u} [Ring R] (i j : ℕ) (hij : i ≠ j) (a : R) :
    toStableE (R := R) (x i j hij a) =
      StableE.natElementary (R := R) i j hij a := by
  change PresentedGroup.toGroup (f := steinbergToElementaryAssignment (R := R))
      (fun _ hr => toStableE_satisfies (R := R) hr) (PresentedGroup.of ⟨i, j, hij, a⟩) =
      StableE.natElementary (R := R) i j hij a
  rw [PresentedGroup.toGroup.of]
  rfl

public theorem toStableE_mapRingHom {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    (toStableE (R := S)).comp (mapRingHom f) =
      (StableE.mapRingHom f).comp (toStableE (R := R)) := by
  apply PresentedGroup.ext
  intro g
  cases g with
  | mk i j hij a =>
    change toStableE (mapRingHom f (x i j hij a)) =
      StableE.mapRingHom f (toStableE (x i j hij a))
    simp only [mapRingHom_x, toStableE_x, StableE.mapRingHom_natElementary]

/-! ## Composite to the stable general linear group -/

/-- Canonical homomorphism `St(R) →* GL∞(R)`, obtained by composing
`toStableE` with the subgroup inclusion `E∞(R) ↪ GL∞(R)`. -/
@[expose] public noncomputable def toStableGL {R : Type u} [Ring R] :
    StableSteinberg R →* StableGL R :=
  (stableElementarySubgroup R).subtype.comp (toStableE (R := R))

@[simp]
public theorem toStableGL_apply {R : Type u} [Ring R] (z : StableSteinberg R) :
    toStableGL (R := R) z = ((toStableE (R := R) z : StableE R) : StableGL R) :=
  rfl

@[simp]
public theorem toStableGL_x {R : Type u} [Ring R]
    (i j : ℕ) (hij : i ≠ j) (a : R) :
    toStableGL (R := R) (x i j hij a) =
      (StableE.natElementary (R := R) i j hij a : StableGL R) := by
  rw [toStableGL, MonoidHom.comp_apply, toStableE_x]
  rfl

/-- Naturality of `toStableGL` for unital ring homomorphisms. -/
public theorem toStableGL_mapRingHom {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) :
    (toStableGL (R := S)).comp (mapRingHom f) =
      ((StableGL.functor.map (SemiRingCat.ofHom f)).hom).comp
        (toStableGL (R := R)) := by
  apply MonoidHom.ext
  intro z
  change ((toStableE (R := S) (mapRingHom f z) : StableE S) : StableGL S) =
    (StableGL.functor.map (SemiRingCat.ofHom f)).hom
      ((toStableE (R := R) z : StableE R) : StableGL R)
  have h := DFunLike.congr_fun (toStableE_mapRingHom f) z
  change toStableE (R := S) (mapRingHom f z) =
    StableE.mapRingHom f (toStableE (R := R) z) at h
  rw [h]
  exact StableE.coe_mapRingHom f (toStableE (R := R) z)

end StableSteinberg

end AlgebraicKTheory
