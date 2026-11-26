/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Data.Fin.VecNotation
public import PhyslibExt.CondensedMatter.Crystallography.MillerIndices
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring.Basic

/-!
# Interplanar spacing of a simple cubic point lattice

For the simple cubic Bravais lattice, the plane at level `m` consists of points whose dot
product with the integer normal `h` is `m * a`. Its Euclidean distance to the next level is
attained by the crystallographic plane shift. Occupancy is a separate question: Bézout's
identity characterizes the levels containing points of `aℤ³` by divisibility by the gcd of the
three indices. For `(2, 0, 0)` only the even levels are occupied, so their spacing is twice the
spacing of the full plane family.

This is Euclidean geometry only; it does not assert a physical diffraction law or treat
noncubic metrics.

Reference: MIT OpenCourseWare 3.091, *Introduction to Solid-State Chemistry*, fall 2018,
Recitation 14, Miller indices and interplanar spacing.
-/

namespace Chemistry.Diffraction

open Crystallography.BravaisLattice

/-- The gcd of the absolute values of the three Miller indices. -/
private def millerIndexGCD (h : Fin 3 → ℤ) : ℕ :=
  Int.gcd (Int.gcd (h 0) (h 1) : ℤ) (h 2)

private lemma latticePlane_isLeast_dist (Λ : Crystallography.BravaisLattice) (h : Fin 3 → ℤ)
    (h₀ : h ≠ 0) (m : ℤ) :
    IsLeast (Set.image2 dist (Λ.latticePlane h m) (Λ.latticePlane h (m + 1)))
      (Λ.interplanarSpacing h) := by
  have hG : Λ.reciprocalVector h ≠ 0 := fun hz =>
    h₀ (Λ.reciprocalVector_injective (hz.trans (Λ.reciprocalVector_zero).symm))
  have hzero : 0 ∈ Λ.latticePlane h 0 := by simp [latticePlane]
  constructor
  · let shift := (‖Λ.reciprocalVector h‖ ^ 2)⁻¹ • Λ.reciprocalVector h
    have hshift : shift ∈ Λ.latticePlane h 1 := by
      simpa only [zero_add, Int.zero_add] using Λ.planeShift_mem h 0 0 hG hzero
    let x := (m : ℝ) • shift
    have hx : x ∈ Λ.latticePlane h m := by
      simp only [latticePlane, Set.mem_ofPred_eq, Int.cast_one] at hshift
      simp only [x, latticePlane, Set.mem_ofPred_eq, real_inner_smul_right, hshift, mul_one]
    refine Set.mem_image2.mpr ⟨x, hx, x + shift, Λ.planeShift_mem h m x hG hx, ?_⟩
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left]
    exact Λ.planeShift_norm h hG
  · intro d hd
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_image2.mp hd
    -- Translating by `-x` puts the two points on levels `0` and `1`.
    have hyx : y - x ∈ Λ.latticePlane h 1 := by
      simp only [latticePlane, Set.mem_ofPred_eq] at hx hy ⊢
      rw [inner_sub_right, hy, hx, Int.cast_add, Int.cast_one, add_sub_cancel_left]
    rw [dist_comm, dist_eq_norm]
    simpa only [zero_sub, norm_neg] using Λ.planeDist_ge h 0 (y - x) hG hzero hyx

private lemma interplanarSpacing_cubic {a : ℝ} (ha : 0 < a) (h : Fin 3 → ℤ) (h₀ : h ≠ 0)
    (m : ℤ) :
    IsLeast (Set.image2 dist ((simpleCubic a ha).latticePlane h m)
      ((simpleCubic a ha).latticePlane h (m + 1)))
      (a / Real.sqrt ((h 0 : ℝ) ^ 2 + (h 1 : ℝ) ^ 2 + (h 2 : ℝ) ^ 2)) := by
  rw [← spacing_simpleCubic a ha h h₀]
  exact latticePlane_isLeast_dist (simpleCubic a ha) h h₀ m

/-- Level `m` contains a lattice point exactly when the gcd of the Miller indices divides `m`.
The divisibility is in `ℤ`, so it covers negative levels as well. -/
private lemma latticePlane_occupied_iff_dvd (Λ : Crystallography.BravaisLattice)
    (h : Fin 3 → ℤ) (m : ℤ) :
    (Λ.latticePlane h m ∩ (Λ.lattice : Set _)).Nonempty ↔ (millerIndexGCD h : ℤ) ∣ m := by
  have hpoint (z : Fin 3 → ℤ) : Λ.latticeVector z ∈ Λ.latticePlane h m ↔
      h 0 * z 0 + h 1 * z 1 + h 2 * z 2 = m := by
    simp only [Λ.mem_latticePlane_iff, Λ.repr_latticeVector, Fin.sum_univ_three]
    exact_mod_cast (Iff.rfl : h 0 * z 0 + h 1 * z 1 + h 2 * z 2 = m ↔ _)
  let g := Int.gcd (h 0) (h 1)
  let d := Int.gcd (g : ℤ) (h 2)
  change _ ↔ (d : ℤ) ∣ m
  constructor
  · rintro ⟨x, hx, hlat⟩
    obtain ⟨z, rfl⟩ := (Λ.mem_lattice_iff x).mp hlat
    rw [← (hpoint z).1 hx]
    have hg : (d : ℤ) ∣ (g : ℤ) := Int.gcd_dvd_left _ _
    exact dvd_add
      (dvd_add
        (dvd_mul_of_dvd_left (hg.trans (Int.gcd_dvd_left _ _)) _)
        (dvd_mul_of_dvd_left (hg.trans (Int.gcd_dvd_right _ _)) _))
      (dvd_mul_of_dvd_left (Int.gcd_dvd_right (g : ℤ) (h 2)) _)
  · rintro ⟨q, hq⟩
    -- Apply Bézout twice, then multiply the resulting coefficients by `q`.
    let z : Fin 3 → ℤ := ![Int.gcdA (h 0) (h 1) * Int.gcdA (g : ℤ) (h 2) * q,
      Int.gcdB (h 0) (h 1) * Int.gcdA (g : ℤ) (h 2) * q, Int.gcdB (g : ℤ) (h 2) * q]
    refine ⟨Λ.latticeVector z, (hpoint z).2 ?_, (Λ.mem_lattice_iff _).2 ⟨z, rfl⟩⟩
    calc
      h 0 * z 0 + h 1 * z 1 + h 2 * z 2 = (d : ℤ) * q := by
        rw [show (d : ℤ) = _ from Int.gcd_eq_gcd_ab (g : ℤ) (h 2)]
        simp only [z, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.tail_cons, Matrix.head_cons]
        rw [show (g : ℤ) = _ from Int.gcd_eq_gcd_ab (h 0) (h 1)]
        ring
      _ = m := hq.symm

private lemma latticePlane_all_occupied_iff_primitive (Λ : Crystallography.BravaisLattice)
    (h : Fin 3 → ℤ) :
    (∀ m : ℤ, (Λ.latticePlane h m ∩ (Λ.lattice : Set _)).Nonempty) ↔ millerIndexGCD h = 1 := by
  simp only [latticePlane_occupied_iff_dvd]
  constructor
  · intro hall
    exact Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp (hall 1))
  · intro hg m
    simp [hg]

private lemma latticePlane_200_occupied_iff_even (Λ : Crystallography.BravaisLattice) (m : ℤ) :
    (Λ.latticePlane ![2, 0, 0] m ∩ (Λ.lattice : Set _)).Nonempty ↔ Even m := by
  rw [latticePlane_occupied_iff_dvd, even_iff_two_dvd]
  have hg : millerIndexGCD ![2, 0, 0] = 2 := by decide
  simp [hg]

private lemma interplanarSpacing_cubic_200_occupied {a : ℝ} (ha : 0 < a) (m : ℤ) :
    let Λ := simpleCubic a ha
    IsLeast (Set.image2 dist (Λ.latticePlane ![2, 0, 0] (2 * m))
      (Λ.latticePlane ![2, 0, 0] (2 * (m + 1)))) a := by
  intro Λ
  -- Level `2n` for `(2, 0, 0)` is level `n` for `(1, 0, 0)`.
  have hplane (n : ℤ) : Λ.latticePlane ![2, 0, 0] (2 * n) = Λ.latticePlane ![1, 0, 0] n := by
    ext x
    rw [show (![2, 0, 0] : Fin 3 → ℤ) = (2 : ℤ) • ![1, 0, 0] by decide]
    simp only [latticePlane, Set.mem_ofPred_eq, reciprocalVector_smul, real_inner_smul_left,
      Int.cast_mul, Int.cast_ofNat, mul_right_inj' (two_ne_zero : (2 : ℝ) ≠ 0)]
  rw [hplane, hplane]
  simpa using interplanarSpacing_cubic ha ![1, 0, 0] (by decide) m

/-- In a simple cubic lattice of spacing `a > 0`, consecutive levels of a nonzero integer
normal `h` have exact Euclidean distance `a / √(h₀² + h₁² + h₂²)`. Level `m` contains a
lattice point precisely when the gcd of the three indices divides `m`, so all levels are
occupied precisely for primitive indices. For `(2,0,0)` the occupied levels are the even ones,
and consecutive even levels have distance `a` rather than `a/2`.

Source: MIT OpenCourseWare 3.091, *Introduction to Solid-State Chemistry*, fall 2018,
Recitation 14 (Miller indices and interplanar spacing). -/
public theorem cubic_plane_spacing_and_occupancy {a : ℝ} (ha : 0 < a) :
    let Λ := simpleCubic a ha
    let gcd (h : Fin 3 → ℤ) := Int.gcd (Int.gcd (h 0) (h 1) : ℤ) (h 2)
    (∀ (h : Fin 3 → ℤ), h ≠ 0 → ∀ m : ℤ,
      IsLeast (Set.image2 dist (Λ.latticePlane h m) (Λ.latticePlane h (m + 1)))
        (a / Real.sqrt ((h 0 : ℝ) ^ 2 + (h 1 : ℝ) ^ 2 + (h 2 : ℝ) ^ 2))) ∧
    (∀ h m, (Λ.latticePlane h m ∩ (Λ.lattice : Set _)).Nonempty ↔ (gcd h : ℤ) ∣ m) ∧
    (∀ h, (∀ m, (Λ.latticePlane h m ∩ (Λ.lattice : Set _)).Nonempty) ↔ gcd h = 1) ∧
    (∀ m, (Λ.latticePlane ![2, 0, 0] m ∩ (Λ.lattice : Set _)).Nonempty ↔ Even m) ∧
    (∀ m, IsLeast (Set.image2 dist (Λ.latticePlane ![2, 0, 0] (2 * m))
      (Λ.latticePlane ![2, 0, 0] (2 * (m + 1)))) a) :=
  ⟨fun h hn m => interplanarSpacing_cubic ha h hn m,
    latticePlane_occupied_iff_dvd _, latticePlane_all_occupied_iff_primitive _,
    latticePlane_200_occupied_iff_even _, interplanarSpacing_cubic_200_occupied ha⟩

end Chemistry.Diffraction
