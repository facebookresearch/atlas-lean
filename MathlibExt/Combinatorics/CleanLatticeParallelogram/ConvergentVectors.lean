/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.CleanLatticeParallelogram
import Mathlib.Tactic.LinearCombination

/-!
# Lattice points in a convergent parallelogram

Consecutive convergent vectors generate the integer lattice, and the only lattice points
in their closed parallelogram are its four vertices.
-/

namespace MetaMathlibExt
namespace convergentVec_parallelogram_latticePoints

open GenContFract
open GenContFract (of)

private theorem contsAux_integral (x : ℚ) (n : ℕ) :
    ∃ a b : ℤ, (of x).contsAux n = ⟨a, b⟩ := by
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨1, 0, by simp⟩
  | one => exact ⟨⌊x⌋, 1, by simp [of_h_eq_floor]⟩
  | more n ih₀ ih₁ =>
    obtain ⟨a, b, hab⟩ := ih₀
    obtain ⟨c, d, hcd⟩ := ih₁
    cases h : (of x).s.get? n with
    | none => exact ⟨c, d, (contsAux_stable_step_of_terminated h).trans hcd⟩
    | some gp =>
      obtain ⟨ha, q, hb⟩ := of_partNum_eq_one_and_exists_int_partDen_eq h
      exact ⟨q * c + a, q * d + b, by simp [contsAux_recurrence h hab hcd, ha, hb]⟩

private theorem convergentVec_natCast (x : ℚ) (j : ℕ) :
    convergentVec x j = (((of x).dens j : ℝ), ((of x).nums j : ℝ)) := by
  simp [convergentVec, show (j : ℤ) ≠ -2 by omega, show (j : ℤ) ≠ -1 by omega]

-- An integer inverse determinant works for either orientation of the two columns.
private theorem consecutive_columns (x : ℚ) {m : ℕ}
    (hm : IsLeast {k | (of x).TerminatedAt k} m) {i : ℤ} (hi : -2 ≤ i) (him : i < m) :
    ∃ a b c d e : ℤ, convergentVec x i = ((a : ℝ), (b : ℝ)) ∧
      convergentVec x (i + 1) = ((c : ℝ), (d : ℝ)) ∧
      e * (a * d - b * c) = 1 := by
  obtain rfl | rfl | hpos : i = -2 ∨ i = -1 ∨ 0 ≤ i := by omega
  · exact ⟨1, 0, 0, 1, 1, by simp [convergentVec], by norm_num [convergentVec], by decide⟩
  · refine ⟨0, 1, 1, ⌊x⌋, -1, ?_, ?_, by simp⟩
    · simpa using (convergentVec_initial x).2.1
    · simpa using (convergentVec_initial x).2.2.1
  lift i to ℕ using hpos
  have hterm : ¬(of x).TerminatedAt i := fun h => by
    have := hm.2 h
    omega
  obtain ⟨b, a, hab⟩ := contsAux_integral x (i + 1)
  obtain ⟨d, c, hcd⟩ := contsAux_integral x (i + 2)
  have hdet := (SimpContFract.of x).determinant hterm
  change (of x).nums i * (of x).dens (i + 1) - (of x).dens i * (of x).nums (i + 1) =
    (-1 : ℚ) ^ (i + 1) at hdet
  simp only [num_eq_conts_a, den_eq_conts_b, nth_cont_eq_succ_nth_contAux, hab, hcd] at hdet
  refine ⟨a, b, c, d, -((-1) ^ (i + 1)), ?_, ?_, ?_⟩
  · simp [convergentVec_natCast, num_eq_conts_a, den_eq_conts_b, nth_cont_eq_succ_nth_contAux, hab]
  · rw [← Nat.cast_succ, convergentVec_natCast]
    simp [num_eq_conts_a, den_eq_conts_b, nth_cont_eq_succ_nth_contAux, hcd]
  · have h : b * c - a * d = (-1 : ℤ) ^ (i + 1) := by exact_mod_cast hdet
    rcases neg_one_pow_eq_or ℤ (i + 1) with he | he <;> rw [he] at h ⊢ <;> linarith

private theorem endpoint_of_intCast {z : ℤ} (h₀ : 0 ≤ (z : ℝ)) (h₁ : (z : ℝ) ≤ 1) :
    z = 0 ∨ z = 1 := by
  norm_cast at h₀ h₁
  omega

private theorem latticePoints_of_unit_det (a b c d e : ℤ) (h : e * (a * d - b * c) = 1) :
    let u : ℝ × ℝ := (a, b)
    let v : ℝ × ℝ := (c, d)
    latticeParallelogram u v ∩ latticePoints = {0, u, v, u + v} ∧
      ∀ p ∈ latticePoints, ∃ s t : ℤ, p = (s : ℝ) • u + (t : ℝ) • v := by
  intro u v
  have hdet : (e : ℝ) * (a * d - b * c) = 1 := by exact_mod_cast h
  -- Cramer's rule gives integer coordinates and recovers every lattice point.
  have coords (x y : ℤ) (s t : ℝ) :
      ((x : ℝ), (y : ℝ)) = s • u + t • v ↔
        s = ((e * (x * d - y * c) : ℤ) : ℝ) ∧ t = ((e * (a * y - b * x) : ℤ) : ℝ) := by
    change ((x : ℝ), (y : ℝ)) = (s * a + t * c, s * b + t * d) ↔ _
    rw [Prod.mk.injEq]
    push_cast
    constructor
    · rintro ⟨hx, hy⟩
      rw [hx, hy]
      constructor
      · linear_combination -s * hdet
      · linear_combination -t * hdet
    · rintro ⟨rfl, rfl⟩
      constructor
      · linear_combination -(x : ℝ) * hdet
      · linear_combination -(y : ℝ) * hdet
  constructor
  · ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨s, t, hs₀, hs₁, ht₀, ht₁, hp⟩, ⟨⟨x, y⟩, rfl⟩⟩
      obtain ⟨rfl, rfl⟩ := (coords x y s t).mp hp
      rw [hp]
      rcases endpoint_of_intCast hs₀ hs₁ with hs | hs <;>
        rcases endpoint_of_intCast ht₀ ht₁ with ht | ht <;> simp [hs, ht]
    · have vertex (s t : ℤ) (hs : s = 0 ∨ s = 1) (ht : t = 0 ∨ t = 1) :
          (s : ℝ) • u + (t : ℝ) • v ∈ latticeParallelogram u v ∩ latticePoints := by
        constructor
        · refine ⟨s, t, ?_, ?_, ?_, ?_, rfl⟩ <;> rcases hs with rfl | rfl <;>
            rcases ht with rfl | rfl <;> norm_num
        · exact ⟨(s * a + t * c, s * b + t * d), by ext <;> simp [u, v]⟩
      rintro (rfl | rfl | rfl | rfl)
      · simpa using vertex 0 0 (Or.inl rfl) (Or.inl rfl)
      · simpa using vertex 1 0 (Or.inr rfl) (Or.inl rfl)
      · simpa using vertex 0 1 (Or.inl rfl) (Or.inr rfl)
      · simpa using vertex 1 1 (Or.inr rfl) (Or.inr rfl)
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    exact ⟨_, _, (coords x y _ _).mpr ⟨rfl, rfl⟩⟩

end convergentVec_parallelogram_latticePoints

set_option linter.unusedVariables false in
/-- **Lattice points of the parallelogram of two consecutive convergent vectors.** Let
$1 \le a < n$ be integers, let $n / a = [q_0; q_1, \dots, q_m]$ be the regular continued fraction
of $n / a$, where $m$ is the least index at which it terminates, and let $v_i$ be its convergent
vectors. For every integer $i$ with $-2 \le i < m$, the lattice points of the parallelogram
spanned by $v_i$ and $v_{i+1}$ are exactly $0$, $v_i$, $v_{i+1}$ and $v_i + v_{i+1}$, and every
point of $\mathbb{Z}^2$ equals $s v_i + t v_{i+1}$ for some integers $s$ and $t$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Theorem 4 (`integers-2026-A10-thm-4`). -/
public theorem convergentVec_parallelogram_latticePoints {a n m : ℕ} (ha : 1 ≤ a)
    (han : a < n) (hm : IsLeast {k | (GenContFract.of ((n : ℚ) / a)).TerminatedAt k} m)
    {i : ℤ} (hi : -2 ≤ i) (him : i < m) :
    latticeParallelogram (convergentVec ((n : ℚ) / a) i) (convergentVec ((n : ℚ) / a) (i + 1)) ∩
        latticePoints =
      {0, convergentVec ((n : ℚ) / a) i, convergentVec ((n : ℚ) / a) (i + 1),
        convergentVec ((n : ℚ) / a) i + convergentVec ((n : ℚ) / a) (i + 1)} ∧
      ∀ p ∈ latticePoints, ∃ s t : ℤ,
        p = (s : ℝ) • convergentVec ((n : ℚ) / a) i +
          (t : ℝ) • convergentVec ((n : ℚ) / a) (i + 1) := by
  obtain ⟨u₁, u₂, v₁, v₂, e, hu, hv, hdet⟩ :=
    convergentVec_parallelogram_latticePoints.consecutive_columns _ hm hi him
  rw [hu, hv]
  exact convergentVec_parallelogram_latticePoints.latticePoints_of_unit_det _ _ _ _ e hdet

end MetaMathlibExt
