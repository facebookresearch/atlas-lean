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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergLiftRelations
public import MathlibExt.KTheory.Ring.K2.StableSteinbergToElementary

/-! # Stable Steinberg lifts to central extensions -/

@[expose] public section

namespace AlgebraicKTheory

namespace StableSteinberg

universe u v w

variable {R : Type u} [Ring R] {N : Type v} {E : Type w} [Group N] [Group E]

open scoped commutatorElement

private theorem lift_addRel {S : GroupExtension N E (StableE R)} (hS : S.IsCentral)
    {r : FreeGroup (SteinbergGenerator R)} (hr : r ∈ steinbergAddRel R) :
    FreeGroup.lift (centralLiftGenerator S) r = 1 := by
  obtain ⟨i, j, hij, a, b, rfl⟩ := hr
  have h1 : FreeGroup.lift (centralLiftGenerator S)
      (SteinbergGenerator.free (R := R) i j hij a) =
      centralLiftGenerator S ⟨i, j, hij, a⟩ := by
    simp [SteinbergGenerator.free]
  have h2 : FreeGroup.lift (centralLiftGenerator S)
      (SteinbergGenerator.free (R := R) i j hij b) =
      centralLiftGenerator S ⟨i, j, hij, b⟩ := by
    simp [SteinbergGenerator.free]
  have h3 : FreeGroup.lift (centralLiftGenerator S)
      (SteinbergGenerator.free (R := R) i j hij (a + b)) =
      centralLiftGenerator S ⟨i, j, hij, a + b⟩ := by
    simp [SteinbergGenerator.free]
  have hAdd := centralLiftGenerator_add hS i j hij a b
  calc FreeGroup.lift (centralLiftGenerator S)
        (SteinbergGenerator.free (R := R) i j hij a *
          SteinbergGenerator.free (R := R) i j hij b *
            (SteinbergGenerator.free (R := R) i j hij (a + b))⁻¹)
      = centralLiftGenerator S ⟨i, j, hij, a⟩ * centralLiftGenerator S ⟨i, j, hij, b⟩ *
          (centralLiftGenerator S ⟨i, j, hij, a + b⟩)⁻¹ := by
        simp [h1, h2, h3]
    _ = 1 := by
        rw [hAdd, mul_inv_cancel]

private theorem lift_commRel {S : GroupExtension N E (StableE R)} (hS : S.IsCentral)
    {r : FreeGroup (SteinbergGenerator R)} (hr : r ∈ steinbergCommRel R) :
    FreeGroup.lift (centralLiftGenerator S) r = 1 := by
  obtain ⟨i, j, k, l, hij, hkl, hil, hjk, a, b, rfl⟩ := hr
  have h1 : FreeGroup.lift (centralLiftGenerator S)
      (SteinbergGenerator.free (R := R) i j hij a) =
      centralLiftGenerator S ⟨i, j, hij, a⟩ := by
    simp [SteinbergGenerator.free]
  have h2 : FreeGroup.lift (centralLiftGenerator S)
      (SteinbergGenerator.free (R := R) k l hkl b) =
      centralLiftGenerator S ⟨k, l, hkl, b⟩ := by
    simp [SteinbergGenerator.free]
  have hComm := centralLiftGenerator_comm hS i j k l hij hkl hil hjk a b
  calc FreeGroup.lift (centralLiftGenerator S)
        (⁅SteinbergGenerator.free (R := R) i j hij a,
          SteinbergGenerator.free (R := R) k l hkl b⁆)
      = ⁅FreeGroup.lift (centralLiftGenerator S)
            (SteinbergGenerator.free (R := R) i j hij a),
          FreeGroup.lift (centralLiftGenerator S)
            (SteinbergGenerator.free (R := R) k l hkl b)⁆ := by
        simp [commutatorElement_def]
    _ = ⁅centralLiftGenerator S ⟨i, j, hij, a⟩,
          centralLiftGenerator S ⟨k, l, hkl, b⟩⁆ := by
        simp [h1, h2]
    _ = 1 := hComm

private theorem lift_chevRel {S : GroupExtension N E (StableE R)} (hS : S.IsCentral)
    {r : FreeGroup (SteinbergGenerator R)} (hr : r ∈ steinbergChevRel R) :
    FreeGroup.lift (centralLiftGenerator S) r = 1 := by
  obtain ⟨i, j, k, hij, hjk, hik, a, b, rfl⟩ := hr
  have h1 : FreeGroup.lift (centralLiftGenerator S)
      (SteinbergGenerator.free (R := R) i j hij a) =
      centralLiftGenerator S ⟨i, j, hij, a⟩ := by
    simp [SteinbergGenerator.free]
  have h2 : FreeGroup.lift (centralLiftGenerator S)
      (SteinbergGenerator.free (R := R) j k hjk b) =
      centralLiftGenerator S ⟨j, k, hjk, b⟩ := by
    simp [SteinbergGenerator.free]
  have h3 : FreeGroup.lift (centralLiftGenerator S)
      (SteinbergGenerator.free (R := R) i k hik (a * b)) =
      centralLiftGenerator S ⟨i, k, hik, a * b⟩ := by
    simp [SteinbergGenerator.free]
  have hChev := centralLiftGenerator_chev hS i j k hij hjk hik a b
  calc FreeGroup.lift (centralLiftGenerator S)
        (⁅SteinbergGenerator.free (R := R) i j hij a,
            SteinbergGenerator.free (R := R) j k hjk b⁆ *
          (SteinbergGenerator.free (R := R) i k hik (a * b))⁻¹)
      = ⁅FreeGroup.lift (centralLiftGenerator S)
            (SteinbergGenerator.free (R := R) i j hij a),
          FreeGroup.lift (centralLiftGenerator S)
            (SteinbergGenerator.free (R := R) j k hjk b)⁆ *
        (FreeGroup.lift (centralLiftGenerator S)
            (SteinbergGenerator.free (R := R) i k hik (a * b)))⁻¹ := by
        simp [commutatorElement_def]
    _ = ⁅centralLiftGenerator S ⟨i, j, hij, a⟩,
          centralLiftGenerator S ⟨j, k, hjk, b⟩⁆ *
        (centralLiftGenerator S ⟨i, k, hik, a * b⟩)⁻¹ := by
        simp [h1, h2, h3, commutatorElement_def]
    _ = 1 := by
        rw [hChev, mul_inv_cancel]

/-- Lift `StableSteinberg R →* E` for a central extension `S` of `StableE R`,
sending `x i j hij a` to `centralLiftGenerator S ⟨i, j, hij, a⟩`. -/
public noncomputable def liftToCentralExtension (S : GroupExtension N E (StableE R))
    (hS : S.IsCentral) : StableSteinberg R →* E :=
  PresentedGroup.toGroup (f := centralLiftGenerator S) (fun r hr => by
    simp only [steinbergRelations, Set.mem_union] at hr
    rcases hr with (hr | hr) | hr
    · exact lift_addRel hS hr
    · exact lift_commRel hS hr
    · exact lift_chevRel hS hr)

@[simp]
public theorem liftToCentralExtension_x (S : GroupExtension N E (StableE R))
    (hS : S.IsCentral) (i j : ℕ) (hij : i ≠ j) (a : R) :
    liftToCentralExtension S hS (StableSteinberg.x i j hij a) =
      centralLiftGenerator S ⟨i, j, hij, a⟩ := by
  change PresentedGroup.toGroup (f := centralLiftGenerator S) _ (PresentedGroup.of ⟨i, j, hij, a⟩) =
    centralLiftGenerator S ⟨i, j, hij, a⟩
  rw [PresentedGroup.toGroup.of]

/-- The central lift covers `toStableE`: `S.rightHom ∘ lift = toStableE`. -/
public theorem rightHom_comp_liftToCentralExtension
    (S : GroupExtension N E (StableE R)) (hS : S.IsCentral) :
    S.rightHom.comp (liftToCentralExtension S hS) = StableSteinberg.toStableE := by
  apply PresentedGroup.ext
  intro g
  cases g with
  | mk i j hij a =>
    change S.rightHom (liftToCentralExtension S hS (StableSteinberg.x i j hij a)) =
      StableSteinberg.toStableE (StableSteinberg.x i j hij a)
    simp [liftToCentralExtension_x, rightHom_centralLiftGenerator, toStableE_x]

end StableSteinberg

end AlgebraicKTheory

end
