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

public import MathlibExt.KTheory.Ring.K2.Basic
import Mathlib.Algebra.Category.Grp.EpiMono

open CategoryTheory

/-! # K₂ kernel bridge

Ergonomic bridge between the categorical `K₂ R` and `ker StableSteinberg.toStableE`.
-/

@[expose] public section

universe u

namespace AlgebraicKTheory

noncomputable section

/-- Element of `K₂ R` from a kernel element of `toStableE`. -/
noncomputable def K2.ofKer {R : Type u} [Ring R]
    (z : StableSteinberg R) (hz : StableSteinberg.toStableE (R := R) z = 1) : K2 R :=
  (K2.kernelIsoKerOf (R := R)).inv ⟨z, hz⟩

@[simp]
theorem K2.inclusion_ofKer {R : Type u} [Ring R]
    (z : StableSteinberg R) (hz : StableSteinberg.toStableE (R := R) z = 1) :
    K2.inclusion.app (RingCat.of R) (K2.ofKer (R := R) z hz) = z := by
  dsimp [K2.ofKer]
  change (((K2.kernelIsoKerOf (R := R)).inv ≫
    K2.inclusion.app (RingCat.of R)) ⟨z, hz⟩) = z
  rw [K2.kernelIsoKerOf_inv_comp_ι]
  rfl

/-- The composite of the `K₂` kernel inclusion with `St(R) → GL∞(R)` is trivial. -/
@[simp]
theorem K2.toStableGL_inclusion_apply {R : Type u} [Ring R] (a : K2 R) :
    StableSteinberg.toStableGL
        (K2.inclusion.app (RingCat.of R) a) = (1 : StableGL R) := by
  let z : StableSteinberg R := K2.inclusion.app (RingCat.of R) a
  have hz : StableSteinberg.toStableE (R := R) z = 1 := by
    exact K2.toStableE_inclusion_apply a
  change StableSteinberg.toStableGL (R := R) z = 1
  calc
    StableSteinberg.toStableGL (R := R) z =
        ((StableSteinberg.toStableE (R := R) z : StableE R) : StableGL R) :=
      StableSteinberg.toStableGL_apply z
    _ = ((1 : StableE R) : StableGL R) := congrArg Subtype.val hz
    _ = 1 := rfl

/-- `K2.inclusion` is injective. -/
theorem K2.inclusion_injective {R : Type u} [Ring R] :
    Function.Injective (K2.inclusion.app (RingCat.of R)) := by
  have hMono : Mono (K2.inclusion.app (RingCat.of R)) := by
    rw [K2.inclusion_app]
    exact CategoryTheory.Limits.equalizer.ι_mono
  exact (GrpCat.mono_iff_injective _).mp hMono

/-- Extensionality for `K2` via `K2.inclusion`. -/
@[ext]
theorem K2.ext {R : Type u} [Ring R] {x y : K2 R}
    (h : K2.inclusion.app (RingCat.of R) x = K2.inclusion.app (RingCat.of R) y) :
    x = y :=
  K2.inclusion_injective h

/-- `K2.ofKer` after `K2.inclusion` is the identity. -/
@[simp]
theorem K2.ofKer_inclusion {R : Type u} [Ring R] (x : K2 R) :
    K2.ofKer (R := R) (K2.inclusion.app (RingCat.of R) x)
      (K2.toStableE_inclusion_apply x) = x := by
  apply K2.inclusion_injective
  exact K2.inclusion_ofKer
    (K2.inclusion.app (RingCat.of R) x)
    (K2.toStableE_inclusion_apply x)

end

end AlgebraicKTheory

end
