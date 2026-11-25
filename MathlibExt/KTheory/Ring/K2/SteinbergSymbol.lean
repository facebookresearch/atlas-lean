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

public import MathlibExt.KTheory.Ring.K2.Functoriality
public import MathlibExt.KTheory.Ring.K2.KernelBridge
public import MathlibExt.KTheory.Ring.K2.StableSteinbergCentrality
public import MathlibExt.KTheory.Ring.K2.StableSteinbergTorusImage

/-! # Canonical Steinberg symbol

Torus cocycle at `(0, 1)` and its `K₂` symbol.
-/

@[expose] public section

universe u

namespace AlgebraicKTheory.StableSteinberg

/-- Canonical torus cocycle at `(0, 1)`: `c(u,v) = h₀₁(u) h₀₁(v) h₀₁(uv)⁻¹`. -/
def torusCocycle {F : Type u} [Field F] (u v : Fˣ) : StableSteinberg F :=
  torus 0 1 (by omega) u * torus 0 1 (by omega) v *
    (torus 0 1 (by omega) (u * v))⁻¹

@[simp]
theorem mapRingHom_torusCocycle {F K : Type u} [Field F] [Field K]
    (f : F →+* K) (u v : Fˣ) :
    mapRingHom f (torusCocycle u v) =
      torusCocycle (Units.map f.toMonoidHom u)
        (Units.map f.toMonoidHom v) := by
  simp only [torusCocycle, map_mul, map_inv, mapRingHom_torus]

@[simp]
theorem toStableE_torusCocycle {F : Type u} [Field F] (u v : Fˣ) :
    toStableE (torusCocycle u v) = 1 := by
  simp only [torusCocycle, map_mul, map_inv,
    toStableE_torus_zero_one_mul, mul_inv_cancel]

theorem torusCocycle_mem_center {F : Type u} [Field F] (u v : Fˣ) :
    torusCocycle u v ∈ Subgroup.center (StableSteinberg F) := by
  have hker : torusCocycle u v ∈ MonoidHom.ker toStableE :=
    MonoidHom.mem_ker.mpr (toStableE_torusCocycle u v)
  exact ker_toStableE_le_center hker

end AlgebraicKTheory.StableSteinberg

namespace AlgebraicKTheory.K2

/-- Steinberg symbol via the torus cocycle. -/
noncomputable def steinbergSymbol {F : Type u} [Field F] (u v : Fˣ) :
    K2 F :=
  K2.ofKer
    (AlgebraicKTheory.StableSteinberg.torusCocycle u v)
    (AlgebraicKTheory.StableSteinberg.toStableE_torusCocycle u v)

@[simp]
theorem inclusion_steinbergSymbol {F : Type u} [Field F] (u v : Fˣ) :
    K2.inclusion.app (RingCat.of F) (steinbergSymbol u v) =
      AlgebraicKTheory.StableSteinberg.torusCocycle u v := by
  unfold steinbergSymbol
  exact K2.inclusion_ofKer _ _

@[simp]
theorem mapRingHom_steinbergSymbol {F K : Type u} [Field F] [Field K]
    (f : F →+* K) (u v : Fˣ) :
    K2.mapRingHom f (steinbergSymbol u v) =
      steinbergSymbol (Units.map f.toMonoidHom u)
        (Units.map f.toMonoidHom v) := by
  apply K2.ext
  simp only [K2.inclusion_mapRingHom_apply, steinbergSymbol,
    K2.inclusion_ofKer]
  rw [StableSteinberg.mapRingHom_torusCocycle]

end AlgebraicKTheory.K2

end
