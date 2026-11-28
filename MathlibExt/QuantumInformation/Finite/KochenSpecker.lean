/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Tactic.FinCases

@[expose] public section

namespace MathlibExt.QuantumInformation.Finite.KochenSpeckerWanted

private def w : Fin 35 → Fin 3 → ℤ :=
  ![![0, 0, 1], ![0, 1, -2], ![0, 1, -1], ![0, 1, 0], ![0, 1, 1], ![0, 1, 2], ![0, 2, -1],
    ![0, 2, 1], ![1, -2, 0], ![1, -2, 1], ![1, -1, -2], ![1, -1, -1], ![1, -1, 0], ![1, -1, 1],
    ![1, 0, -2], ![1, 0, -1], ![1, 0, 0], ![1, 0, 1], ![1, 1, -2], ![1, 1, -1], ![1, 1, 0],
    ![1, 1, 1], ![1, 2, -2], ![1, 2, -1], ![1, 2, 0], ![1, 2, 2], ![2, -2, -1], ![2, -2, 1],
    ![2, -1, 0], ![2, -1, 1], ![2, 0, 1], ![2, 1, -2], ![2, 1, 0], ![2, 1, 1], ![2, 1, 2]]

private def x (i : Fin 35) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun j => ((w i j : ℤ) : ℝ))

private lemma inner_x (i j : Fin 35) :
    inner (𝕜 := ℝ) (x i) (x j) = ((dotProduct (w i) (w j) : ℤ) : ℝ) := by
  rw [PiLp.inner_apply]
  simp only [x, WithLp.ofLp_toLp]
  simp only [dotProduct]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rw [RCLike.inner_apply]
  simp [mul_comm]

private noncomputable def v (i : Fin 35) : EuclideanSpace ℝ (Fin 3) := (‖x i‖⁻¹) • (x i)

private lemma x_ne_zero (i : Fin 35) (h : dotProduct (w i) (w i) ≠ 0) : x i ≠ 0 := by
  intro hz
  have h2 : inner (𝕜 := ℝ) (x i) (x i) = 0 := by rw [hz]; exact inner_zero_left _
  rw [inner_x] at h2
  exact h (Int.cast_eq_zero.mp h2)

private lemma v_norm (i : Fin 35) (h : dotProduct (w i) (w i) ≠ 0) : ‖v i‖ = 1 := by
  have hne : x i ≠ 0 := x_ne_zero i h
  simp only [v, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hne)),
    inv_mul_cancel₀ (ne_of_gt (norm_pos_iff.mpr hne))]

private lemma inner_v (i j : Fin 35) :
    inner (𝕜 := ℝ) (v i) (v j) =
      ‖x i‖⁻¹ * ‖x j‖⁻¹ * ((dotProduct (w i) (w j) : ℤ) : ℝ) := by
  simp only [v, inner_smul_left, inner_smul_right, inner_x]
  simp [mul_assoc, mul_comm]

private lemma inner_v_zero (i j : Fin 35) (h : dotProduct (w i) (w j) = 0) :
    inner (𝕜 := ℝ) (v i) (v j) = 0 := by
  rw [inner_v, h, Int.cast_zero, mul_zero]

private lemma orthonorm_of {t : Fin 3 → Fin 35}
    (hab : dotProduct (w (t 0)) (w (t 1)) = 0)
    (hac : dotProduct (w (t 0)) (w (t 2)) = 0)
    (hbc : dotProduct (w (t 1)) (w (t 2)) = 0)
    (hunit : ∀ i, ‖v i‖ = 1) :
    Orthonormal ℝ (fun r : Fin 3 => v (t r)) := by
  have habs : dotProduct (w (t 1)) (w (t 0)) = 0 := by rwa [dotProduct_comm]
  have hacs : dotProduct (w (t 2)) (w (t 0)) = 0 := by rwa [dotProduct_comm]
  have hbcs : dotProduct (w (t 2)) (w (t 1)) = 0 := by rwa [dotProduct_comm]
  refine ⟨fun r => hunit _, ?_⟩
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact absurd rfl hrs
  · exact inner_v_zero _ _ hab
  · exact inner_v_zero _ _ hac
  · exact inner_v_zero _ _ habs
  · exact absurd rfl hrs
  · exact inner_v_zero _ _ hbc
  · exact inner_v_zero _ _ hacs
  · exact inner_v_zero _ _ hbcs
  · exact absurd rfl hrs

private lemma t111_ab {a b c : ℕ} (s : a + b + c = 1) (h1 : a = 0) (h2 : b = 0) : c = 1 := by
  omega
private lemma t111_ac {a b c : ℕ} (s : a + b + c = 1) (h1 : a = 0) (h2 : c = 0) : b = 1 := by
  omega
private lemma t111_bc {a b c : ℕ} (s : a + b + c = 1) (h1 : b = 0) (h2 : c = 0) : a = 1 := by
  omega
private lemma p10 {a b : ℕ} (p : a + b ≤ 1) (h : a = 1) : b = 0 := by omega
private lemma p01 {a b : ℕ} (p : a + b ≤ 1) (h : b = 1) : a = 0 := by omega
private lemma tc {a b c : ℕ} (s : a + b + c = 1) (h1 : a = 0) (h2 : b = 0) (h3 : c = 0) :
    False := by omega
private lemma pc {a b : ℕ} (p : a + b ≤ 1) (h1 : a = 1) (h2 : b = 1) : False := by omega
private lemma split2 (f : Fin 2) : f.val = 0 ∨ f.val = 1 := by
  have h := Fin.isLt f
  omega

private lemma alldots : ∀ i : Fin 35, dotProduct (w i) (w i) ≠ 0 := by decide

private lemma hunit : ∀ i : Fin 35, ‖v i‖ = 1 := fun i => v_norm i (alldots i)

/--
**Kochen–Specker theorem in $\mathbb{R}^3$.** There exist a natural number $N$ and unit vectors
$v_1, \dots, v_N \in \mathbb{R}^3$ such that no function $c : \{1, \dots, N\} \to \{0, 1\}$
satisfies both of the following: $c(i) + c(j) \le 1$ whenever $v_i$ and $v_j$ are orthogonal, and
$c(i) + c(j) + c(k) = 1$ whenever $(v_i, v_j, v_k)$ is an orthonormal triple.

Proves `Wanted` entry `kochen_specker_finite_real_three`.

Source: S. Kochen, E. P. Specker, The Problem of Hidden Variables in Quantum Mechanics, J. Math.
Mech. 17 (1967), 59-87, DOI 10.1512/iumj.1968.17.17004.
-/
theorem kochen_specker_finite_real_three :
    ∃ (N : ℕ) (v : Fin N → EuclideanSpace ℝ (Fin 3)),
      (∀ i, ‖v i‖ = 1) ∧
      ¬ ∃ (c : Fin N → Fin 2),
        (∀ i j : Fin N, inner (𝕜 := ℝ) (v i) (v j) = 0 →
          (c i).val + (c j).val ≤ 1) ∧
          ∀ (b : Fin 3 → Fin N),
            Orthonormal ℝ (fun r => v (b r)) →
              (∑ r : Fin 3, (c (b r)).val) = 1 := by
  refine ⟨35, v, hunit, ?_⟩
  rintro ⟨c, hO, hC⟩
  have q0 : (c 0).val + (c 3).val ≤ 1 :=
    hO 0 3 (inner_v_zero 0 3 (by decide))
  have q1 : (c 0).val + (c 8).val ≤ 1 :=
    hO 0 8 (inner_v_zero 0 8 (by decide))
  have q2 : (c 0).val + (c 12).val ≤ 1 :=
    hO 0 12 (inner_v_zero 0 12 (by decide))
  have q3 : (c 0).val + (c 16).val ≤ 1 :=
    hO 0 16 (inner_v_zero 0 16 (by decide))
  have q4 : (c 0).val + (c 20).val ≤ 1 :=
    hO 0 20 (inner_v_zero 0 20 (by decide))
  have q5 : (c 0).val + (c 24).val ≤ 1 :=
    hO 0 24 (inner_v_zero 0 24 (by decide))
  have q6 : (c 0).val + (c 28).val ≤ 1 :=
    hO 0 28 (inner_v_zero 0 28 (by decide))
  have q7 : (c 0).val + (c 32).val ≤ 1 :=
    hO 0 32 (inner_v_zero 0 32 (by decide))
  have q8 : (c 1).val + (c 16).val ≤ 1 :=
    hO 1 16 (inner_v_zero 1 16 (by decide))
  have q9 : (c 1).val + (c 26).val ≤ 1 :=
    hO 1 26 (inner_v_zero 1 26 (by decide))
  have q10 : (c 2).val + (c 4).val ≤ 1 :=
    hO 2 4 (inner_v_zero 2 4 (by decide))
  have q11 : (c 2).val + (c 11).val ≤ 1 :=
    hO 2 11 (inner_v_zero 2 11 (by decide))
  have q12 : (c 2).val + (c 16).val ≤ 1 :=
    hO 2 16 (inner_v_zero 2 16 (by decide))
  have q13 : (c 2).val + (c 21).val ≤ 1 :=
    hO 2 21 (inner_v_zero 2 21 (by decide))
  have q14 : (c 2).val + (c 25).val ≤ 1 :=
    hO 2 25 (inner_v_zero 2 25 (by decide))
  have q15 : (c 2).val + (c 33).val ≤ 1 :=
    hO 2 33 (inner_v_zero 2 33 (by decide))
  have q16 : (c 3).val + (c 14).val ≤ 1 :=
    hO 3 14 (inner_v_zero 3 14 (by decide))
  have q17 : (c 3).val + (c 15).val ≤ 1 :=
    hO 3 15 (inner_v_zero 3 15 (by decide))
  have q18 : (c 3).val + (c 16).val ≤ 1 :=
    hO 3 16 (inner_v_zero 3 16 (by decide))
  have q19 : (c 3).val + (c 17).val ≤ 1 :=
    hO 3 17 (inner_v_zero 3 17 (by decide))
  have q20 : (c 3).val + (c 30).val ≤ 1 :=
    hO 3 30 (inner_v_zero 3 30 (by decide))
  have q21 : (c 4).val + (c 13).val ≤ 1 :=
    hO 4 13 (inner_v_zero 4 13 (by decide))
  have q22 : (c 4).val + (c 16).val ≤ 1 :=
    hO 4 16 (inner_v_zero 4 16 (by decide))
  have q23 : (c 4).val + (c 19).val ≤ 1 :=
    hO 4 19 (inner_v_zero 4 19 (by decide))
  have q24 : (c 4).val + (c 22).val ≤ 1 :=
    hO 4 22 (inner_v_zero 4 22 (by decide))
  have q25 : (c 4).val + (c 29).val ≤ 1 :=
    hO 4 29 (inner_v_zero 4 29 (by decide))
  have q26 : (c 5).val + (c 9).val ≤ 1 :=
    hO 5 9 (inner_v_zero 5 9 (by decide))
  have q27 : (c 5).val + (c 16).val ≤ 1 :=
    hO 5 16 (inner_v_zero 5 16 (by decide))
  have q28 : (c 5).val + (c 23).val ≤ 1 :=
    hO 5 23 (inner_v_zero 5 23 (by decide))
  have q29 : (c 5).val + (c 27).val ≤ 1 :=
    hO 5 27 (inner_v_zero 5 27 (by decide))
  have q30 : (c 6).val + (c 10).val ≤ 1 :=
    hO 6 10 (inner_v_zero 6 10 (by decide))
  have q31 : (c 6).val + (c 16).val ≤ 1 :=
    hO 6 16 (inner_v_zero 6 16 (by decide))
  have q32 : (c 6).val + (c 34).val ≤ 1 :=
    hO 6 34 (inner_v_zero 6 34 (by decide))
  have q33 : (c 7).val + (c 16).val ≤ 1 :=
    hO 7 16 (inner_v_zero 7 16 (by decide))
  have q34 : (c 7).val + (c 18).val ≤ 1 :=
    hO 7 18 (inner_v_zero 7 18 (by decide))
  have q35 : (c 8).val + (c 31).val ≤ 1 :=
    hO 8 31 (inner_v_zero 8 31 (by decide))
  have q36 : (c 8).val + (c 33).val ≤ 1 :=
    hO 8 33 (inner_v_zero 8 33 (by decide))
  have q37 : (c 8).val + (c 34).val ≤ 1 :=
    hO 8 34 (inner_v_zero 8 34 (by decide))
  have q38 : (c 9).val + (c 15).val ≤ 1 :=
    hO 9 15 (inner_v_zero 9 15 (by decide))
  have q39 : (c 9).val + (c 32).val ≤ 1 :=
    hO 9 32 (inner_v_zero 9 32 (by decide))
  have q40 : (c 10).val + (c 20).val ≤ 1 :=
    hO 10 20 (inner_v_zero 10 20 (by decide))
  have q41 : (c 10).val + (c 30).val ≤ 1 :=
    hO 10 30 (inner_v_zero 10 30 (by decide))
  have q42 : (c 11).val + (c 17).val ≤ 1 :=
    hO 11 17 (inner_v_zero 11 17 (by decide))
  have q43 : (c 11).val + (c 20).val ≤ 1 :=
    hO 11 20 (inner_v_zero 11 20 (by decide))
  have q44 : (c 12).val + (c 18).val ≤ 1 :=
    hO 12 18 (inner_v_zero 12 18 (by decide))
  have q45 : (c 12).val + (c 19).val ≤ 1 :=
    hO 12 19 (inner_v_zero 12 19 (by decide))
  have q46 : (c 12).val + (c 20).val ≤ 1 :=
    hO 12 20 (inner_v_zero 12 20 (by decide))
  have q47 : (c 12).val + (c 21).val ≤ 1 :=
    hO 12 21 (inner_v_zero 12 21 (by decide))
  have q48 : (c 13).val + (c 15).val ≤ 1 :=
    hO 13 15 (inner_v_zero 13 15 (by decide))
  have q49 : (c 13).val + (c 20).val ≤ 1 :=
    hO 13 20 (inner_v_zero 13 20 (by decide))
  have q50 : (c 14).val + (c 27).val ≤ 1 :=
    hO 14 27 (inner_v_zero 14 27 (by decide))
  have q51 : (c 14).val + (c 29).val ≤ 1 :=
    hO 14 29 (inner_v_zero 14 29 (by decide))
  have q52 : (c 14).val + (c 33).val ≤ 1 :=
    hO 14 33 (inner_v_zero 14 33 (by decide))
  have q53 : (c 15).val + (c 21).val ≤ 1 :=
    hO 15 21 (inner_v_zero 15 21 (by decide))
  have q54 : (c 15).val + (c 34).val ≤ 1 :=
    hO 15 34 (inner_v_zero 15 34 (by decide))
  have q55 : (c 17).val + (c 19).val ≤ 1 :=
    hO 17 19 (inner_v_zero 17 19 (by decide))
  have q56 : (c 17).val + (c 23).val ≤ 1 :=
    hO 17 23 (inner_v_zero 17 23 (by decide))
  have q57 : (c 17).val + (c 31).val ≤ 1 :=
    hO 17 31 (inner_v_zero 17 31 (by decide))
  have q58 : (c 18).val + (c 30).val ≤ 1 :=
    hO 18 30 (inner_v_zero 18 30 (by decide))
  have q59 : (c 20).val + (c 26).val ≤ 1 :=
    hO 20 26 (inner_v_zero 20 26 (by decide))
  have q60 : (c 20).val + (c 27).val ≤ 1 :=
    hO 20 27 (inner_v_zero 20 27 (by decide))
  have q61 : (c 22).val + (c 30).val ≤ 1 :=
    hO 22 30 (inner_v_zero 22 30 (by decide))
  have q62 : (c 23).val + (c 28).val ≤ 1 :=
    hO 23 28 (inner_v_zero 23 28 (by decide))
  have q63 : (c 24).val + (c 29).val ≤ 1 :=
    hO 24 29 (inner_v_zero 24 29 (by decide))
  have q64 : (c 25).val + (c 28).val ≤ 1 :=
    hO 25 28 (inner_v_zero 25 28 (by decide))
  have s0 : (c 0).val + (c 3).val + (c 16).val = 1 := by
    have o := orthonorm_of (t := ![0, 3, 16]) (by decide) (by decide)
      (by decide) hunit
    have h := hC _ o
    rwa [Fin.sum_univ_three] at h
  have s1 : (c 0).val + (c 8).val + (c 32).val = 1 := by
    have o := orthonorm_of (t := ![0, 8, 32]) (by decide) (by decide)
      (by decide) hunit
    have h := hC _ o
    rwa [Fin.sum_univ_three] at h
  have s2 : (c 0).val + (c 12).val + (c 20).val = 1 := by
    have o := orthonorm_of (t := ![0, 12, 20]) (by decide) (by decide)
      (by decide) hunit
    have h := hC _ o
    rwa [Fin.sum_univ_three] at h
  have s3 : (c 0).val + (c 24).val + (c 28).val = 1 := by
    have o := orthonorm_of (t := ![0, 24, 28]) (by decide) (by decide)
      (by decide) hunit
    have h := hC _ o
    rwa [Fin.sum_univ_three] at h
  have s4 : (c 1).val + (c 7).val + (c 16).val = 1 := by
    have o := orthonorm_of (t := ![1, 7, 16]) (by decide) (by decide)
      (by decide) hunit
    have h := hC _ o
    rwa [Fin.sum_univ_three] at h
  have s5 : (c 2).val + (c 4).val + (c 16).val = 1 := by
    have o := orthonorm_of (t := ![2, 4, 16]) (by decide) (by decide)
      (by decide) hunit
    have h := hC _ o
    rwa [Fin.sum_univ_three] at h
  have s6 : (c 2).val + (c 11).val + (c 33).val = 1 := by
    have o := orthonorm_of (t := ![2, 11, 33]) (by decide) (by decide)
      (by decide) hunit
    have h := hC _ o
    rwa [Fin.sum_univ_three] at h
  have s7 : (c 3).val + (c 14).val + (c 30).val = 1 := by
    have o := orthonorm_of (t := ![3, 14, 30]) (by decide) (by decide)
      (by decide) hunit
    have h := hC _ o
    rwa [Fin.sum_univ_three] at h
  have s8 : (c 3).val + (c 15).val + (c 17).val = 1 := by
    have o := orthonorm_of (t := ![3, 15, 17]) (by decide) (by decide)
      (by decide) hunit
    have h := hC _ o
    rwa [Fin.sum_univ_three] at h
  have s9 : (c 4).val + (c 19).val + (c 29).val = 1 := by
    have o := orthonorm_of (t := ![4, 19, 29]) (by decide) (by decide)
      (by decide) hunit
    have h := hC _ o
    rwa [Fin.sum_univ_three] at h
  have s10 : (c 5).val + (c 6).val + (c 16).val = 1 := by
    have o := orthonorm_of (t := ![5, 6, 16]) (by decide) (by decide)
      (by decide) hunit
    have h := hC _ o
    rwa [Fin.sum_univ_three] at h
  have s11 : (c 9).val + (c 15).val + (c 21).val = 1 := by
    have o := orthonorm_of (t := ![9, 15, 21]) (by decide) (by decide)
      (by decide) hunit
    have h := hC _ o
    rwa [Fin.sum_univ_three] at h
  have s12 : (c 10).val + (c 13).val + (c 20).val = 1 := by
    have o := orthonorm_of (t := ![10, 13, 20]) (by decide) (by decide)
      (by decide) hunit
    have h := hC _ o
    rwa [Fin.sum_univ_three] at h
  have s13 : (c 11).val + (c 17).val + (c 23).val = 1 := by
    have o := orthonorm_of (t := ![11, 17, 23]) (by decide) (by decide)
      (by decide) hunit
    have h := hC _ o
    rwa [Fin.sum_univ_three] at h
  have s14 : (c 12).val + (c 18).val + (c 21).val = 1 := by
    have o := orthonorm_of (t := ![12, 18, 21]) (by decide) (by decide)
      (by decide) hunit
    have h := hC _ o
    rwa [Fin.sum_univ_three] at h
  have s15 : (c 22).val + (c 26).val + (c 34).val = 1 := by
    have o := orthonorm_of (t := ![22, 26, 34]) (by decide) (by decide)
      (by decide) hunit
    have h := hC _ o
    rwa [Fin.sum_univ_three] at h
  have s16 : (c 25).val + (c 27).val + (c 31).val = 1 := by
    have o := orthonorm_of (t := ![25, 27, 31]) (by decide) (by decide)
      (by decide) hunit
    have h := hC _ o
    rwa [Fin.sum_univ_three] at h
  have e1 : (c 0).val = 0 ∨ (c 0).val = 1 := split2 (c 0)
  rcases e1 with e1|e1
  · have e2 : (c 16).val = 0 ∨ (c 16).val = 1 := split2 (c 16)
    rcases e2 with e2|e2
    · have e3 : (c 3).val = 1 := t111_ac s0 e1 e2
      have e4 : (c 14).val = 0 := p10 q16 e3
      have e5 : (c 15).val = 0 := p10 q17 e3
      have e6 : (c 17).val = 0 := p10 q19 e3
      have e7 : (c 30).val = 0 := p10 q20 e3
      have e8 : (c 20).val = 0 ∨ (c 20).val = 1 := split2 (c 20)
      rcases e8 with e8|e8
      · have e9 : (c 12).val = 1 := t111_ac s2 e1 e8
        have e10 : (c 18).val = 0 := p10 q44 e9
        have e11 : (c 19).val = 0 := p10 q45 e9
        have e12 : (c 21).val = 0 := p10 q47 e9
        have e13 : (c 9).val = 1 := t111_bc s11 e5 e12
        have e14 : (c 5).val = 0 := p01 q26 e13
        have e15 : (c 6).val = 1 := t111_ac s10 e14 e2
        have e16 : (c 10).val = 0 := p10 q30 e15
        have e17 : (c 13).val = 1 := t111_ac s12 e16 e8
        have e18 : (c 4).val = 0 := p01 q21 e17
        have e19 : (c 2).val = 1 := t111_bc s5 e18 e2
        have e20 : (c 29).val = 1 := t111_ab s9 e18 e11
        have e21 : (c 11).val = 0 := p10 q11 e19
        have e22 : (c 23).val = 1 := t111_ab s13 e21 e6
        have e23 : (c 25).val = 0 := p10 q14 e19
        have e24 : (c 33).val = 0 := p10 q15 e19
        have e25 : (c 34).val = 0 := p10 q32 e15
        have e26 : (c 32).val = 0 := p10 q39 e13
        have e27 : (c 8).val = 1 := t111_ac s1 e1 e26
        have e28 : (c 31).val = 0 := p10 q35 e27
        have e29 : (c 27).val = 1 := t111_ac s16 e23 e28
        have e30 : (c 28).val = 0 := p10 q62 e22
        have e31 : (c 24).val = 1 := t111_ac s3 e1 e30
        exact pc q63 e31 e20
      · have e32 : (c 10).val = 0 := p01 q40 e8
        have e33 : (c 11).val = 0 := p01 q43 e8
        have e34 : (c 23).val = 1 := t111_ab s13 e33 e6
        have e35 : (c 5).val = 0 := p01 q28 e34
        have e36 : (c 6).val = 1 := t111_ac s10 e35 e2
        have e37 : (c 34).val = 0 := p10 q32 e36
        have e38 : (c 12).val = 0 := p01 q46 e8
        have e39 : (c 13).val = 0 := p01 q49 e8
        have e40 : (c 26).val = 0 := p10 q59 e8
        have e41 : (c 22).val = 1 := t111_bc s15 e40 e37
        have e42 : (c 4).val = 0 := p01 q24 e41
        have e43 : (c 2).val = 1 := t111_bc s5 e42 e2
        have e44 : (c 21).val = 0 := p10 q13 e43
        have e45 : (c 9).val = 1 := t111_bc s11 e5 e44
        have e46 : (c 18).val = 1 := t111_ac s14 e38 e44
        have e47 : (c 25).val = 0 := p10 q14 e43
        have e48 : (c 33).val = 0 := p10 q15 e43
        have e49 : (c 7).val = 0 := p01 q34 e46
        have e50 : (c 1).val = 1 := t111_bc s4 e49 e2
        have e51 : (c 32).val = 0 := p10 q39 e45
        have e52 : (c 8).val = 1 := t111_ac s1 e1 e51
        have e53 : (c 31).val = 0 := p10 q35 e52
        have e54 : (c 27).val = 1 := t111_ac s16 e47 e53
        exact pc q60 e8 e54
    · have e55 : (c 1).val = 0 := p01 q8 e2
      have e56 : (c 2).val = 0 := p01 q12 e2
      have e57 : (c 3).val = 0 := p01 q18 e2
      have e58 : (c 4).val = 0 := p01 q22 e2
      have e59 : (c 5).val = 0 := p01 q27 e2
      have e60 : (c 6).val = 0 := p01 q31 e2
      have e61 : (c 7).val = 0 := p01 q33 e2
      have e62 : (c 20).val = 0 ∨ (c 20).val = 1 := split2 (c 20)
      rcases e62 with e62|e62
      · have e63 : (c 12).val = 1 := t111_ac s2 e1 e62
        have e64 : (c 18).val = 0 := p10 q44 e63
        have e65 : (c 19).val = 0 := p10 q45 e63
        have e66 : (c 29).val = 1 := t111_ab s9 e58 e65
        have e67 : (c 21).val = 0 := p10 q47 e63
        have e68 : (c 14).val = 0 := p01 q51 e66
        have e69 : (c 30).val = 1 := t111_ab s7 e57 e68
        have e70 : (c 10).val = 0 := p01 q41 e69
        have e71 : (c 13).val = 1 := t111_ac s12 e70 e62
        have e72 : (c 15).val = 0 := p10 q48 e71
        have e73 : (c 17).val = 1 := t111_ab s8 e57 e72
        have e74 : (c 9).val = 1 := t111_bc s11 e72 e67
        have e75 : (c 32).val = 0 := p10 q39 e74
        have e76 : (c 8).val = 1 := t111_ac s1 e1 e75
        have e77 : (c 31).val = 0 := p10 q35 e76
        have e78 : (c 33).val = 0 := p10 q36 e76
        have e79 : (c 11).val = 1 := t111_ac s6 e56 e78
        have e80 : (c 34).val = 0 := p10 q37 e76
        exact pc q42 e79 e73
      · have e81 : (c 10).val = 0 := p01 q40 e62
        have e82 : (c 11).val = 0 := p01 q43 e62
        have e83 : (c 33).val = 1 := t111_ab s6 e56 e82
        have e84 : (c 8).val = 0 := p01 q36 e83
        have e85 : (c 32).val = 1 := t111_ab s1 e1 e84
        have e86 : (c 9).val = 0 := p01 q39 e85
        have e87 : (c 12).val = 0 := p01 q46 e62
        have e88 : (c 13).val = 0 := p01 q49 e62
        have e89 : (c 14).val = 0 := p01 q52 e83
        have e90 : (c 30).val = 1 := t111_ab s7 e57 e89
        have e91 : (c 18).val = 0 := p01 q58 e90
        have e92 : (c 21).val = 1 := t111_ab s14 e87 e91
        have e93 : (c 15).val = 0 := p01 q53 e92
        have e94 : (c 17).val = 1 := t111_ab s8 e57 e93
        have e95 : (c 19).val = 0 := p10 q55 e94
        have e96 : (c 29).val = 1 := t111_ab s9 e58 e95
        have e97 : (c 23).val = 0 := p10 q56 e94
        have e98 : (c 31).val = 0 := p10 q57 e94
        have e99 : (c 26).val = 0 := p10 q59 e62
        have e100 : (c 27).val = 0 := p10 q60 e62
        have e101 : (c 25).val = 1 := t111_bc s16 e100 e98
        have e102 : (c 22).val = 0 := p01 q61 e90
        have e103 : (c 34).val = 1 := t111_ab s15 e102 e99
        have e104 : (c 24).val = 0 := p01 q63 e96
        have e105 : (c 28).val = 1 := t111_ab s3 e1 e104
        exact pc q64 e101 e105
  · have e106 : (c 3).val = 0 := p10 q0 e1
    have e107 : (c 8).val = 0 := p10 q1 e1
    have e108 : (c 12).val = 0 := p10 q2 e1
    have e109 : (c 16).val = 0 := p10 q3 e1
    have e110 : (c 20).val = 0 := p10 q4 e1
    have e111 : (c 24).val = 0 := p10 q5 e1
    have e112 : (c 28).val = 0 := p10 q6 e1
    have e113 : (c 32).val = 0 := p10 q7 e1
    have e114 : (c 2).val = 0 ∨ (c 2).val = 1 := split2 (c 2)
    rcases e114 with e114|e114
    · have e115 : (c 4).val = 1 := t111_ac s5 e114 e109
      have e116 : (c 13).val = 0 := p10 q21 e115
      have e117 : (c 10).val = 1 := t111_bc s12 e116 e110
      have e118 : (c 19).val = 0 := p10 q23 e115
      have e119 : (c 22).val = 0 := p10 q24 e115
      have e120 : (c 29).val = 0 := p10 q25 e115
      have e121 : (c 6).val = 0 := p01 q30 e117
      have e122 : (c 5).val = 1 := t111_bc s10 e121 e109
      have e123 : (c 9).val = 0 := p10 q26 e122
      have e124 : (c 23).val = 0 := p10 q28 e122
      have e125 : (c 27).val = 0 := p10 q29 e122
      have e126 : (c 30).val = 0 := p10 q41 e117
      have e127 : (c 14).val = 1 := t111_ac s7 e106 e126
      have e128 : (c 33).val = 0 := p10 q52 e127
      have e129 : (c 11).val = 1 := t111_ac s6 e114 e128
      have e130 : (c 17).val = 0 := p10 q42 e129
      have e131 : (c 15).val = 1 := t111_ac s8 e106 e130
      have e132 : (c 21).val = 0 := p10 q53 e131
      have e133 : (c 18).val = 1 := t111_ac s14 e108 e132
      have e134 : (c 7).val = 0 := p01 q34 e133
      have e135 : (c 1).val = 1 := t111_bc s4 e134 e109
      have e136 : (c 26).val = 0 := p10 q9 e135
      have e137 : (c 34).val = 1 := t111_ab s15 e119 e136
      exact pc q54 e131 e137
    · have e138 : (c 4).val = 0 := p10 q10 e114
      have e139 : (c 11).val = 0 := p10 q11 e114
      have e140 : (c 21).val = 0 := p10 q13 e114
      have e141 : (c 18).val = 1 := t111_ac s14 e108 e140
      have e142 : (c 25).val = 0 := p10 q14 e114
      have e143 : (c 33).val = 0 := p10 q15 e114
      have e144 : (c 7).val = 0 := p01 q34 e141
      have e145 : (c 1).val = 1 := t111_bc s4 e144 e109
      have e146 : (c 26).val = 0 := p10 q9 e145
      have e147 : (c 30).val = 0 := p10 q58 e141
      have e148 : (c 14).val = 1 := t111_ac s7 e106 e147
      have e149 : (c 27).val = 0 := p10 q50 e148
      have e150 : (c 31).val = 1 := t111_ab s16 e142 e149
      have e151 : (c 29).val = 0 := p10 q51 e148
      have e152 : (c 19).val = 1 := t111_ac s9 e138 e151
      have e153 : (c 17).val = 0 := p01 q55 e152
      have e154 : (c 15).val = 1 := t111_ac s8 e106 e153
      have e155 : (c 23).val = 1 := t111_ab s13 e139 e153
      have e156 : (c 5).val = 0 := p01 q28 e155
      have e157 : (c 6).val = 1 := t111_ac s10 e156 e109
      have e158 : (c 10).val = 0 := p10 q30 e157
      have e159 : (c 13).val = 1 := t111_ac s12 e158 e110
      have e160 : (c 34).val = 0 := p10 q32 e157
      have e161 : (c 22).val = 1 := t111_bc s15 e146 e160
      have e162 : (c 9).val = 0 := p01 q38 e154
      exact pc q48 e159 e154

end MathlibExt.QuantumInformation.Finite.KochenSpeckerWanted
