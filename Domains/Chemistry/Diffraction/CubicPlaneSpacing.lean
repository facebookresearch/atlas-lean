/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring.Basic

/-!
# Interplanar spacing of a simple cubic point lattice

The plane at level `m` consists of points whose dot product with the integer normal `h` is
`m * a`. Its Euclidean distance to the next level is the least distance between any two
points, one in each plane. Cauchy–Schwarz gives a lower bound, and a displacement along the
normal attains it. Occupancy is a separate question: Bézout's identity characterizes the levels
containing points of `aℤ³` by divisibility by the gcd of the three indices. For `(2, 0, 0)` only
the even levels are occupied, so their spacing is twice the spacing of the full plane family.

This is Euclidean geometry only; it does not assert a physical diffraction law or treat
noncubic metrics.

Reference: MIT OpenCourseWare 3.091, *Introduction to Solid-State Chemistry*, fall 2018,
Recitation 14, Miller indices and interplanar spacing.
-/

namespace Chemistry.Diffraction

open scoped InnerProductSpace

/-- Level `m` of the plane family with integer normal `h` and lattice parameter `a`: the points
satisfying `h₀ x₀ + h₁ x₁ + h₂ x₂ = m a`. -/
private def cubicPlane (a : ℝ) (h : Fin 3 → ℤ) (m : ℤ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | ∑ i, (h i : ℝ) * x i = (m : ℝ) * a}

/-- The simple cubic point lattice `aℤ³` in Euclidean three-space. -/
private def cubicLattice (a : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  Set.range fun z : Fin 3 → ℤ => WithLp.toLp 2 (fun i => a * (z i : ℝ))

/-- The gcd of the absolute values of the three Miller indices. -/
private def millerIndexGCD (h : Fin 3 → ℤ) : ℕ :=
  Int.gcd (Int.gcd (h 0) (h 1) : ℤ) (h 2)

private lemma cubicPlane_isLeast_dist (a : ℝ) (h : Fin 3 → ℤ) (h₀ : h ≠ 0) (m n : ℤ) :
    IsLeast (Set.image2 dist (cubicPlane a h m) (cubicPlane a h n))
      (|(n : ℝ) * a - (m : ℝ) * a| /
        Real.sqrt ((h 0 : ℝ) ^ 2 + (h 1 : ℝ) ^ 2 + (h 2 : ℝ) ^ 2)) := by
  let v : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun i => (h i : ℝ))
  have hv : 0 < ‖v‖ := by
    apply norm_pos_iff.mpr
    intro hv
    apply h₀
    funext i
    exact_mod_cast (show (h i : ℝ) = 0 from congrArg (fun w : EuclideanSpace ℝ (Fin 3) => w i) hv)
  have hnorm : ‖v‖ = Real.sqrt ((h 0 : ℝ) ^ 2 + (h 1 : ℝ) ^ 2 + (h 2 : ℝ) ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg v), EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  have hmem (j : ℤ) (x : EuclideanSpace ℝ (Fin 3)) :
      x ∈ cubicPlane a h j ↔ ⟪v, x⟫_ℝ = (j : ℝ) * a := by
    simp [cubicPlane, v, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  let t := (n : ℝ) * a - (m : ℝ) * a
  rw [← hnorm]
  change IsLeast _ (|t| / ‖v‖)
  constructor
  · -- Take a pair whose displacement is along the normal.
    let u : EuclideanSpace ℝ (Fin 3) := ‖v‖⁻¹ • v
    have hu : ⟪v, u⟫_ℝ = ‖v‖ := by
      dsimp only [u]
      rw [real_inner_smul_right, real_inner_self_eq_norm_mul_norm, ← mul_assoc,
        inv_mul_cancel₀ hv.ne', one_mul]
    have hunit : ‖u‖ = 1 := by
      dsimp only [u]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hv.le), inv_mul_cancel₀ hv.ne']
    let x : EuclideanSpace ℝ (Fin 3) := ((m : ℝ) * a / ‖v‖) • u
    have hx : ⟪v, x⟫_ℝ = (m : ℝ) * a := by
      dsimp only [x]
      rw [real_inner_smul_right, hu, div_mul_cancel₀ _ hv.ne']
    refine Set.mem_image2.mpr ⟨x, (hmem m x).2 hx, x + (t / ‖v‖) • u, ?_, ?_⟩
    · rw [hmem, inner_add_right, hx, real_inner_smul_right, hu, div_mul_cancel₀ _ hv.ne']
      dsimp only [t]
      ring
    · rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hunit, mul_one,
        Real.norm_eq_abs, abs_div, abs_of_pos hv]
  · -- Cauchy–Schwarz bounds the distance of every pair.
    intro d hd
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_image2.mp hd
    have hsub : ⟪v, y - x⟫_ℝ = t := by
      rw [inner_sub_right, (hmem n y).1 hy, (hmem m x).1 hx]
    rw [dist_comm, dist_eq_norm, div_le_iff₀ hv, ← hsub, mul_comm ‖y - x‖]
    exact abs_real_inner_le_norm v (y - x)

/-- The exact Euclidean distance from `Pₘ` to `Pₘ₊₁` is `a / √(h₀² + h₁² + h₂²)`.
The value bounds every cross-plane distance from below and is attained by a pair of points,
regardless of whether the planes contain any lattice points. -/
private theorem interplanarSpacing_cubic {a : ℝ} (ha : 0 < a) (h : Fin 3 → ℤ) (h₀ : h ≠ 0) (m : ℤ) :
    IsLeast (Set.image2 dist (cubicPlane a h m) (cubicPlane a h (m + 1)))
      (a / Real.sqrt ((h 0 : ℝ) ^ 2 + (h 1 : ℝ) ^ 2 + (h 2 : ℝ) ^ 2)) := by
  have hgap : ((m + 1 : ℤ) : ℝ) * a - (m : ℝ) * a = a := by
    rw [Int.cast_add, Int.cast_one]
    ring
  simpa only [hgap, abs_of_pos ha] using cubicPlane_isLeast_dist a h h₀ m (m + 1)

/-- Level `m` contains a point of `aℤ³` exactly when the gcd of the Miller indices divides `m`.
The divisibility is in `ℤ`, so it covers negative levels as well. -/
private theorem cubicPlane_occupied_iff_dvd {a : ℝ} (ha : 0 < a) (h : Fin 3 → ℤ) (m : ℤ) :
    (cubicPlane a h m ∩ cubicLattice a).Nonempty ↔ (millerIndexGCD h : ℤ) ∣ m := by
  have hpoint (z : Fin 3 → ℤ) :
      WithLp.toLp 2 (fun i => a * (z i : ℝ)) ∈ cubicPlane a h m ↔
        h 0 * z 0 + h 1 * z 1 + h 2 * z 2 = m := by
    change (∑ i, (h i : ℝ) * (a * (z i : ℝ))) = (m : ℝ) * a ↔ _
    simp only [mul_left_comm _ a, ← Finset.mul_sum, mul_comm (m : ℝ) a,
      mul_right_inj' ha.ne', Fin.sum_univ_three]
    exact_mod_cast (Iff.rfl : h 0 * z 0 + h 1 * z 1 + h 2 * z 2 = m ↔ _)
  let g := Int.gcd (h 0) (h 1)
  let d := Int.gcd (g : ℤ) (h 2)
  change _ ↔ (d : ℤ) ∣ m
  constructor
  · rintro ⟨_, hx, ⟨z, rfl⟩⟩
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
    refine ⟨_, (hpoint z).2 ?_, ⟨z, rfl⟩⟩
    calc
      h 0 * z 0 + h 1 * z 1 + h 2 * z 2 = (d : ℤ) * q := by
        rw [show (d : ℤ) = _ from Int.gcd_eq_gcd_ab (g : ℤ) (h 2)]
        simp only [z, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.tail_cons, Matrix.head_cons]
        rw [show (g : ℤ) = _ from Int.gcd_eq_gcd_ab (h 0) (h 1)]
        ring
      _ = m := hq.symm

/-- All levels are occupied exactly for primitive indices (gcd `1`). In that case consecutive
levels are consecutive occupied planes. -/
private theorem cubicPlane_all_occupied_iff_primitive {a : ℝ} (ha : 0 < a) (h : Fin 3 → ℤ) :
    (∀ m : ℤ, (cubicPlane a h m ∩ cubicLattice a).Nonempty) ↔ millerIndexGCD h = 1 := by
  simp only [cubicPlane_occupied_iff_dvd ha]
  constructor
  · intro hall
    exact Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp (hall 1))
  · intro hg m
    simp [hg]

/-- With indices `(2, 0, 0)`, the even levels are occupied and the odd levels are empty. -/
private theorem cubicPlane_200_occupied_iff_even {a : ℝ} (ha : 0 < a) (m : ℤ) :
    (cubicPlane a ![2, 0, 0] m ∩ cubicLattice a).Nonempty ↔ Even m := by
  rw [cubicPlane_occupied_iff_dvd ha, even_iff_two_dvd]
  have hg : millerIndexGCD ![2, 0, 0] = 2 := by decide
  simp [hg]

private lemma indices200_ne_zero : (![2, 0, 0] : Fin 3 → ℤ) ≠ 0 := by
  decide

/-- For `(2, 0, 0)`, levels `2m` and `2(m+1)` are consecutive occupied planes, and their exact
Euclidean distance is `a`. -/
private theorem interplanarSpacing_cubic_200_occupied {a : ℝ} (ha : 0 < a) (m : ℤ) :
    IsLeast (Set.image2 dist (cubicPlane a ![2, 0, 0] (2 * m))
      (cubicPlane a ![2, 0, 0] (2 * (m + 1)))) a := by
  have hgap : ((2 * (m + 1) : ℤ) : ℝ) * a - ((2 * m : ℤ) : ℝ) * a = 2 * a := by
    push_cast
    ring
  have hsqrt : Real.sqrt (2 ^ 2 + 0 ^ 2 + 0 ^ 2) = 2 := by
    simpa only [zero_pow (by decide : 2 ≠ 0), add_zero] using
      Real.sqrt_sq (zero_le_two : (0 : ℝ) ≤ 2)
  have h := cubicPlane_isLeast_dist a ![2, 0, 0] indices200_ne_zero (2 * m) (2 * (m + 1))
  simpa only [hgap, abs_of_pos (mul_pos two_pos ha), Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Int.cast_ofNat, Int.cast_zero, hsqrt,
    mul_div_cancel_left₀ a (two_ne_zero : (2 : ℝ) ≠ 0)] using h

/-- In a simple cubic lattice of spacing `a > 0`, consecutive levels of a nonzero integer
normal `h` have exact Euclidean distance `a / √(h₀² + h₁² + h₂²)`. Level `m` contains a
lattice point precisely when the gcd of the three indices divides `m`, so all levels are
occupied precisely for primitive indices. For `(2,0,0)` the occupied levels are the even ones,
and consecutive even levels have distance `a` rather than `a/2`.

Source: MIT OpenCourseWare 3.091, *Introduction to Solid-State Chemistry*, fall 2018,
Recitation 14 (Miller indices and interplanar spacing). -/
public theorem cubic_plane_spacing_and_occupancy {a : ℝ} (ha : 0 < a) :
    let plane (h : Fin 3 → ℤ) (m : ℤ) : Set (EuclideanSpace ℝ (Fin 3)) :=
      {x | ∑ i, (h i : ℝ) * x i = (m : ℝ) * a}
    let lattice : Set (EuclideanSpace ℝ (Fin 3)) :=
      Set.range fun z : Fin 3 → ℤ => WithLp.toLp 2 (fun i => a * (z i : ℝ))
    let gcd (h : Fin 3 → ℤ) := Int.gcd (Int.gcd (h 0) (h 1) : ℤ) (h 2)
    (∀ (h : Fin 3 → ℤ), h ≠ 0 → ∀ m : ℤ,
      IsLeast (Set.image2 dist (plane h m) (plane h (m + 1)))
        (a / Real.sqrt ((h 0 : ℝ) ^ 2 + (h 1 : ℝ) ^ 2 + (h 2 : ℝ) ^ 2))) ∧
    (∀ h m, (plane h m ∩ lattice).Nonempty ↔ (gcd h : ℤ) ∣ m) ∧
    (∀ h, (∀ m, (plane h m ∩ lattice).Nonempty) ↔ gcd h = 1) ∧
    (∀ m, (plane ![2, 0, 0] m ∩ lattice).Nonempty ↔ Even m) ∧
    (∀ m, IsLeast (Set.image2 dist (plane ![2, 0, 0] (2 * m))
      (plane ![2, 0, 0] (2 * (m + 1)))) a) :=
  ⟨fun h hn m => interplanarSpacing_cubic ha h hn m,
    cubicPlane_occupied_iff_dvd ha, cubicPlane_all_occupied_iff_primitive ha,
    cubicPlane_200_occupied_iff_even ha, interplanarSpacing_cubic_200_occupied ha⟩

end Chemistry.Diffraction
