/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.OrderedAffineCover.Cech
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Pulling back structure-sheaf cochains along a refinement map

Let `h : X ⟶ Y`, let `𝒲` and `𝒦` be ordered affine covers of `X` and `Y`, and let
`lam : 𝒲.ι → 𝒦.ι` satisfy `𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)`. A cochain `z` of the structure
presheaf of `Y` on `𝒦` pulls back to a cochain of the structure presheaf of `X` on `𝒲`: on a
tuple `s` with `lam ∘ s` injective, sort `lam ∘ s` increasingly, pull back the value of `z`
there and multiply by the sign of the sorting permutation; on other tuples the value is `0`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.OrderedAffineCover

open CategoryTheory Opposite TopologicalSpace

variable {X Y : Scheme.{u}} (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover)
  (lam : 𝒲.ι → 𝒦.ι)

/-- The increasing rearrangement of `lam ∘ s`, when it is injective. -/
def sortIdx {n : ℕ} (s : 𝒲.Idx n) (hinj : Function.Injective (lam ∘ s.1)) : 𝒦.Idx n :=
  ⟨(lam ∘ s.1) ∘ (Tuple.sort (lam ∘ s.1)),
    (Tuple.monotone_sort (lam ∘ s.1)).strictMono_of_injective
      (hinj.comp (Tuple.sort (lam ∘ s.1)).injective)⟩

theorem sortIdx_val {n : ℕ} (s : 𝒲.Idx n) (hinj : Function.Injective (lam ∘ s.1)) :
    (𝒲.sortIdx 𝒦 lam s hinj).1 = (lam ∘ s.1) ∘ (Tuple.sort (lam ∘ s.1)) :=
  rfl

theorem inter_le_preimage_inter_sortIdx (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w))
    {n : ℕ} (s : 𝒲.Idx n) (hinj : Function.Injective (lam ∘ s.1)) :
    𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj) := by
  change 𝒲.inter s ≤ h ⁻¹ᵁ (⨅ j, 𝒦.U ((𝒲.sortIdx 𝒦 lam s hinj).1 j))
  rw [Scheme.OrderedAffineCover.preimage_iInf_fin]
  refine le_iInf fun j => ?_
  exact (iInf_le (fun i => 𝒲.U (s.1 i)) (Tuple.sort (lam ∘ s.1) j)).trans (hlam _)

end AlgebraicGeometry.Scheme.OrderedAffineCover

namespace AlgebraicGeometry.OModulePresheaf

open CategoryTheory Opposite TopologicalSpace

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
variable {X Y : Scheme.{u}} {πX : X ⟶ Spec (.of R')} {πY : Y ⟶ Spec (.of R)}

/-- Pullback of an alternating structure-sheaf cochain along `h : X ⟶ Y` and an index map
`lam` refining the covers. -/
def unitPullback (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover)
    (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ)
    (z : (unit πY).cochain 𝒦 n) : (unit πX).cochain 𝒲 n :=
  fun s => by
    classical
    exact if hinj : Function.Injective (lam ∘ s.1) then
      ((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) •
        (X.presheaf.map (homOfLE (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam s hinj)).op).hom
          ((h.app (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))).hom (z (𝒲.sortIdx 𝒦 lam s hinj)))
    else 0

theorem unitPullback_apply_of_injective (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover)
    (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w))
    (n : ℕ) (z : (unit πY).cochain 𝒦 n) (s : 𝒲.Idx n) (hinj : Function.Injective (lam ∘ s.1)) :
    unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z s =
      ((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) •
        (X.presheaf.map (homOfLE (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam s hinj)).op).hom
          ((h.app (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))).hom (z (𝒲.sortIdx 𝒦 lam s hinj))) := by
  classical
  exact dite_eq_left_of_eq_true (eq_true hinj)

theorem unitPullback_apply_of_not_injective (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover)
    (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w))
    (n : ℕ) (z : (unit πY).cochain 𝒦 n) (s : 𝒲.Idx n)
    (hinj : ¬ Function.Injective (lam ∘ s.1)) :
    unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z s = 0 := by
  classical
  exact dite_eq_right_of_eq_false (eq_false hinj)

end AlgebraicGeometry.OModulePresheaf
