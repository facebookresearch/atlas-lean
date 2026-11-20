/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib











namespace StatMech
namespace Exact3D



abbrev SurfaceVec3 : Type :=
  Fin 3 → ℝ


def surfaceVec3 (x y z : ℝ) : SurfaceVec3 :=
  ![x, y, z]


def surfaceXAxisUnit : SurfaceVec3 :=
  surfaceVec3 1 0 0




theorem surfaceTension_cubeFace_axis_le_of_convex_flip23
    {T : SurfaceVec3 → ℝ}
    (hconv : ConvexOn ℝ Set.univ T)
    (hflip : ∀ x y z : ℝ,
      T (surfaceVec3 x (-y) (-z)) = T (surfaceVec3 x y z))
    (n a b : ℝ) :
    T (surfaceVec3 n 0 0) ≤ T (surfaceVec3 n a b) := by
  let p : SurfaceVec3 := surfaceVec3 n a b
  let q : SurfaceVec3 := surfaceVec3 n (-a) (-b)
  have hmid := hconv.2 (Set.mem_univ p) (Set.mem_univ q)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 by norm_num)
  have hmid_eq :
      (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q =
        surfaceVec3 n 0 0 := by
    ext i
    fin_cases i
    · simp [p, q, surfaceVec3]
      ring
    · simp [p, q, surfaceVec3]
    · simp [p, q, surfaceVec3]
  have hq : T q = T p := by
    simpa [p, q] using hflip n a b
  calc
    T (surfaceVec3 n 0 0) =
        T ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q) := by
      rw [hmid_eq]
    _ ≤ (1 / 2 : ℝ) • T p + (1 / 2 : ℝ) • T q := hmid
    _ = T p := by
      rw [hq]
      module
    _ = T (surfaceVec3 n a b) := rfl




theorem surfaceTension_cubeFace_xAxisRate_le_of_convex_flip23_hom
    {T : SurfaceVec3 → ℝ}
    (hconv : ConvexOn ℝ Set.univ T)
    (hflip : ∀ x y z : ℝ,
      T (surfaceVec3 x (-y) (-z)) = T (surfaceVec3 x y z))
    (hhom : ∀ t : ℝ, 0 ≤ t →
      T (surfaceVec3 t 0 0) = t * T surfaceXAxisUnit)
    {n a b : ℝ} (hn : 0 ≤ n) :
    n * T surfaceXAxisUnit ≤ T (surfaceVec3 n a b) := by
  calc
    n * T surfaceXAxisUnit = T (surfaceVec3 n 0 0) := (hhom n hn).symm
    _ ≤ T (surfaceVec3 n a b) :=
      surfaceTension_cubeFace_axis_le_of_convex_flip23 hconv hflip n a b



theorem surfaceTension_cubeBoundary_xAxisRate_le_of_convex_signedPerm_hom
    {T : SurfaceVec3 → ℝ}
    (hconv : ConvexOn ℝ Set.univ T)
    (hflip1 : ∀ x y z : ℝ,
      T (surfaceVec3 (-x) y z) = T (surfaceVec3 x y z))
    (hflip2 : ∀ x y z : ℝ,
      T (surfaceVec3 x (-y) z) = T (surfaceVec3 x y z))
    (hflip3 : ∀ x y z : ℝ,
      T (surfaceVec3 x y (-z)) = T (surfaceVec3 x y z))
    (hswap12 : ∀ x y z : ℝ,
      T (surfaceVec3 y x z) = T (surfaceVec3 x y z))
    (hswap13 : ∀ x y z : ℝ,
      T (surfaceVec3 z y x) = T (surfaceVec3 x y z))
    (hhom : ∀ t : ℝ, 0 ≤ t →
      T (surfaceVec3 t 0 0) = t * T surfaceXAxisUnit)
    {n x y z : ℝ} (hn : 0 ≤ n)
    (hface :
      x = n ∨ x = -n ∨ y = n ∨ y = -n ∨ z = n ∨ z = -n) :
    n * T surfaceXAxisUnit ≤ T (surfaceVec3 x y z) := by
  have hflip23 : ∀ x y z : ℝ,
      T (surfaceVec3 x (-y) (-z)) = T (surfaceVec3 x y z) := by
    intro x y z
    calc
      T (surfaceVec3 x (-y) (-z)) = T (surfaceVec3 x (-y) z) :=
        hflip3 x (-y) z
      _ = T (surfaceVec3 x y z) := hflip2 x y z
  rcases hface with hx | hx | hy | hy | hz | hz
  · subst x
    exact
      surfaceTension_cubeFace_xAxisRate_le_of_convex_flip23_hom
        hconv hflip23 hhom hn
  · subst x
    calc
      n * T surfaceXAxisUnit ≤ T (surfaceVec3 n y z) :=
        surfaceTension_cubeFace_xAxisRate_le_of_convex_flip23_hom
          hconv hflip23 hhom hn
      _ = T (surfaceVec3 (-n) y z) := (hflip1 n y z).symm
  · subst y
    calc
      n * T surfaceXAxisUnit ≤ T (surfaceVec3 n x z) :=
        surfaceTension_cubeFace_xAxisRate_le_of_convex_flip23_hom
          hconv hflip23 hhom hn
      _ = T (surfaceVec3 x n z) := (hswap12 n x z).symm
  · subst y
    calc
      n * T surfaceXAxisUnit ≤ T (surfaceVec3 n x z) :=
        surfaceTension_cubeFace_xAxisRate_le_of_convex_flip23_hom
          hconv hflip23 hhom hn
      _ = T (surfaceVec3 x n z) := (hswap12 n x z).symm
      _ = T (surfaceVec3 x (-n) z) := (hflip2 x n z).symm
  · subst z
    calc
      n * T surfaceXAxisUnit ≤ T (surfaceVec3 n y x) :=
        surfaceTension_cubeFace_xAxisRate_le_of_convex_flip23_hom
          hconv hflip23 hhom hn
      _ = T (surfaceVec3 x y n) := (hswap13 n y x).symm
  · subst z
    calc
      n * T surfaceXAxisUnit ≤ T (surfaceVec3 n y x) :=
        surfaceTension_cubeFace_xAxisRate_le_of_convex_flip23_hom
          hconv hflip23 hhom hn
      _ = T (surfaceVec3 x y n) := (hswap13 n y x).symm
      _ = T (surfaceVec3 x y (-n)) := (hflip3 x y n).symm

end Exact3D
end StatMech
