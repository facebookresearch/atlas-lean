/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Nat.Nth
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.NumberTheory.NicomacheanAdjoinedProgression
public import MathlibExt.NumberTheory.NicomacheanTranslations
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Golden-ratio sequences with vanishing Nicomachean defect

Bag-product powers of `[1, φ⁻¹, 3, 2φ⁻¹, 5, 3φ⁻¹]` prove
`exists_goldenRatio_nicomachean_sequence`: for every `N` there is a positive `Z[φ]`-valued
sequence with zero defect containing `φ⁻¹ ^ n` for `1 ≤ n ≤ N` and with a subsequence of
irrational entries longer than half.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 7.
-/

namespace MetaMathlibExt

private noncomputable def psi : ℝ := Real.goldenRatio⁻¹
private noncomputable def A : List ℝ := [1, psi, 3, 2*psi, 5, 3*psi]
private noncomputable def A_irr : List ℝ := [psi, 2*psi, 3*psi]

private noncomputable def sig : ℕ → List ℝ
  | 0 => [1]
  | n+1 => (sig n).flatMap (fun a => A.map (fun b => a * b))

private theorem psi_eq : psi = Real.goldenRatio - 1 := by
  have hφ : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  have h : Real.goldenRatio * (Real.goldenRatio - 1) = 1 := by
    linear_combination hφ
  have h2 : psi = Real.goldenRatio⁻¹ := rfl
  rw [h2]
  exact (eq_inv_of_mul_eq_one_right h).symm

private theorem psi_pos : 0 < psi := by
  have h : 0 < Real.goldenRatio := Real.goldenRatio_pos
  simp only [psi]
  exact inv_pos.mpr h

private theorem A_len : A.length = 6 := by rfl
private theorem A_irr_len : A_irr.length = 3 := by rfl

private theorem A_pos : ∀ x ∈ A, 0 < x := by
  intro x hx
  simp only [A, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · exact psi_pos
  · norm_num
  · have h := psi_pos; positivity
  · norm_num
  · have h := psi_pos; positivity

private theorem sig_pos (n : ℕ) : ∀ x ∈ sig n, 0 < x := by
  induction n with
  | zero =>
    intro x hx
    simp only [sig, List.mem_singleton] at hx
    rw [hx]; norm_num
  | succ n ih =>
    intro x hx
    simp only [sig, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have ha_pos := ih a ha
    have hb_pos := A_pos b hb
    exact mul_pos ha_pos hb_pos

private theorem A_zphi : ∀ x ∈ A, ∃ p q : ℤ, x = p + q * Real.goldenRatio := by
  intro x hx
  simp only [A, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, by push_cast; ring⟩
  · exact ⟨-1, 1, by rw [psi_eq]; push_cast; ring⟩
  · exact ⟨3, 0, by push_cast; ring⟩
  · refine ⟨-2, 2, ?_⟩
    rw [psi_eq]; push_cast; ring
  · exact ⟨5, 0, by push_cast; ring⟩
  · refine ⟨-3, 3, ?_⟩
    rw [psi_eq]; push_cast; ring

private theorem zphi_mul {x1 x2 : ℝ} {p1 q1 p2 q2 : ℤ}
    (h1 : x1 = p1 + q1 * Real.goldenRatio)
    (h2 : x2 = p2 + q2 * Real.goldenRatio) :
    ∃ p q : ℤ, x1 * x2 = p + q * Real.goldenRatio := by
  have hφ : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  refine ⟨p1 * p2 + q1 * q2, p1 * q2 + q1 * p2 + q1 * q2, ?_⟩
  rw [h1, h2]
  push_cast
  linear_combination (q1 * q2 : ℝ) * hφ

private theorem sig_zphi (n : ℕ) : ∀ x ∈ sig n, ∃ p q : ℤ, x = p + q * Real.goldenRatio := by
  induction n with
  | zero =>
    intro x hx
    simp only [sig, List.mem_singleton] at hx
    rw [hx]
    exact ⟨1, 0, by push_cast; ring⟩
  | succ n ih =>
    intro x hx
    simp only [sig, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨p1, q1, h1⟩ := ih a ha
    obtain ⟨p2, q2, h2⟩ := A_zphi b hb
    exact zphi_mul h1 h2

private theorem A_rep : ∀ x ∈ A, ∃ R : ℤ, R ≠ 0 ∧ ∃ k ≤ 1, x = R * psi ^ k := by
  intro x hx
  simp only [A, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, by norm_num, 0, by norm_num, by push_cast; ring⟩
  · exact ⟨1, by norm_num, 1, by norm_num, by push_cast; ring⟩
  · exact ⟨3, by norm_num, 0, by norm_num, by push_cast; ring⟩
  · exact ⟨2, by norm_num, 1, by norm_num, by push_cast; ring⟩
  · exact ⟨5, by norm_num, 0, by norm_num, by push_cast; ring⟩
  · exact ⟨3, by norm_num, 1, by norm_num, by push_cast; ring⟩

private theorem sig_rep (n : ℕ) : ∀ x ∈ sig n, ∃ R : ℤ, R ≠ 0 ∧ ∃ k ≤ n, x = R * psi ^ k := by
  induction n with
  | zero =>
    intro x hx
    simp only [sig, List.mem_singleton] at hx
    rw [hx]
    exact ⟨1, by norm_num, 0, by norm_num, by push_cast; ring⟩
  | succ n ih =>
    intro x hx
    simp only [sig, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨R1, hR1, k1, hk1, rfl⟩ := ih a ha
    obtain ⟨R2, hR2, k2, hk2, rfl⟩ := A_rep b hb
    refine ⟨R1 * R2, mul_ne_zero hR1 hR2, k1 + k2, by omega, ?_⟩
    push_cast
    rw [pow_add]
    ring

private theorem golden_pow_fib (n : ℕ) :
    Real.goldenRatio ^ (n + 1) = (Nat.fib n : ℝ) + (Nat.fib (n + 1) : ℝ) * Real.goldenRatio := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hφ : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
    have hfib : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    calc Real.goldenRatio ^ (n + 1 + 1)
        = Real.goldenRatio ^ (n + 1) * Real.goldenRatio := by ring
      _ = ((Nat.fib n : ℝ) + (Nat.fib (n + 1) : ℝ) * Real.goldenRatio) * Real.goldenRatio := by
          rw [ih]
      _ = (Nat.fib (n + 1) : ℝ) + ((Nat.fib n : ℝ) + (Nat.fib (n + 1) : ℝ)) * Real.goldenRatio := by
          linear_combination (Nat.fib (n + 1) : ℝ) * hφ
      _ = (Nat.fib (n + 1) : ℝ) + (Nat.fib (n + 2) : ℝ) * Real.goldenRatio := by
          rw [hfib]; push_cast; ring

private theorem golden_pow_irrational {n : ℕ} (hn : 1 ≤ n) : Irrational (Real.goldenRatio ^ n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hfib_pos : 0 < Nat.fib (m + 1) := Nat.fib_pos.mpr (by omega)
  have hfib_int_ne : (Nat.fib (m + 1) : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hfib_pos
  by_contra h_rat
  obtain ⟨q, hq⟩ := exists_rat_of_not_irrational h_rat
  have h_eq := golden_pow_fib m
  rw [hq] at h_eq
  have h_rat2 : ¬ Irrational ((Nat.fib (m + 1) : ℝ) * Real.goldenRatio) := by
    have h2 : (Nat.fib (m + 1) : ℝ) * Real.goldenRatio = ((q - (Nat.fib m : ℚ)) : ℚ) := by
      have h4 : (Nat.fib (m + 1) : ℝ) * Real.goldenRatio = (q : ℝ) - (Nat.fib m : ℝ) := by
        linear_combination -h_eq
      rw [h4]
      push_cast
      ring
    rw [h2]
    exact Rat.not_irrational _
  have h_rat3 : ¬ Irrational Real.goldenRatio := by
    intro h_irr
    have h5 : Irrational (Real.goldenRatio * ((Nat.fib (m + 1) : ℤ) : ℝ)) :=
      h_irr.mul_intCast hfib_int_ne
    have h6 : (Real.goldenRatio * ((Nat.fib (m + 1) : ℤ) : ℝ))
        = (Nat.fib (m + 1) : ℝ) * Real.goldenRatio := by
      push_cast; ring
    rw [h6] at h5
    exact h_rat2 h5
  exact h_rat3 Real.goldenRatio_irrational

private theorem psi_pow_irrational {k : ℕ} (hk : 1 ≤ k) :
    Irrational ((Real.goldenRatio⁻¹) ^ k) := by
  have h1 : Irrational (Real.goldenRatio ^ k) := golden_pow_irrational hk
  have h2 : ((Real.goldenRatio⁻¹) ^ k) = (Real.goldenRatio ^ k)⁻¹ := by rw [inv_pow]
  rw [h2]
  exact h1.inv

private theorem psi_pow_irrational' {k : ℕ} (hk : 1 ≤ k) : Irrational (psi ^ k) := by
  have h : psi ^ k = (Real.goldenRatio⁻¹) ^ k := rfl
  rw [h]
  exact psi_pow_irrational hk

private theorem int_mul_psi_pow_irrational {R : ℤ} {k : ℕ} (hR : R ≠ 0) (hk : 1 ≤ k) :
    Irrational (R * psi ^ k) := by
  have hpsi : Irrational (psi ^ k) := psi_pow_irrational' hk
  exact hpsi.intCast_mul hR

private theorem flatMap_len (l : List ℝ) :
    (l.flatMap (fun a => A.map (fun b => a * b))).length = l.length * 6 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, A_len, ih, List.length_cons]
    ring

private theorem sig_len (n : ℕ) : (sig n).length = 6 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sig, flatMap_len, ih]
    ring

private theorem sum_map_mul (a : ℝ) : (A.map (fun b => a * b)).sum = a * A.sum := by
  simp only [A, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

private theorem sum_flatMap (l : List ℝ) :
    (l.flatMap (fun a => A.map (fun b => a * b))).sum = l.sum * A.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.sum_append, sum_map_mul, ih, List.sum_cons]
    ring

private theorem sig_sum (n : ℕ) : (sig n).sum = A.sum ^ n := by
  induction n with
  | zero => simp [sig]
  | succ n ih =>
    simp only [sig, sum_flatMap, ih]
    ring

private theorem cubes_map_mul (a : ℝ) :
    ((A.map (fun b => a * b)).map (· ^ 3)).sum = a ^ 3 * ((A.map (· ^ 3)).sum) := by
  simp only [A, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

private theorem cubes_flatMap (l : List ℝ) :
    (((l.flatMap (fun a => A.map (fun b => a * b))).map (· ^ 3)).sum)
      = ((l.map (· ^ 3)).sum) * (((A.map (· ^ 3)).sum)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hmap : ((List.flatMap (fun a => List.map (fun b => a * b) A) (a :: l)).map (· ^ 3))
        = ((A.map (fun b => a * b)).map (· ^ 3))
          ++ (((l.flatMap (fun a => A.map (fun b => a * b))).map (· ^ 3))) := by
      rw [List.flatMap_cons, List.map_append]
    rw [hmap, List.sum_append, cubes_map_mul, ih]
    simp only [List.map_cons, List.sum_cons]
    ring

private theorem sig_cubes (n : ℕ) : (((sig n).map (· ^ 3)).sum) = (((A.map (· ^ 3)).sum)) ^ n := by
  induction n with
  | zero => simp [sig]
  | succ n ih =>
    simp only [sig, cubes_flatMap, ih]
    ring

private theorem A_nu : nicomacheanNu A = 0 := by
  have hφ : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  simp only [nicomacheanNu, A]
  simp only [List.sum_cons, List.sum_nil, List.map_cons, List.map_nil]
  rw [psi_eq]
  linear_combination (108 - 36 * Real.goldenRatio) * hφ

private theorem sig_nu (n : ℕ) : nicomacheanNu (sig n) = 0 := by
  have hA : A.sum ^ 2 = ((A.map (· ^ 3)).sum) := by
    have h := A_nu
    simp only [nicomacheanNu] at h
    linear_combination h
  simp only [nicomacheanNu, sig_sum, sig_cubes]
  have h2 : (A.sum ^ n) ^ 2 = (A.sum ^ 2) ^ n := by rw [← pow_right_comm]
  rw [h2, hA, sub_self]

private theorem A_irr_sub : A_irr.Sublist A := by
  simp only [A_irr, A]
  apply List.Sublist.cons
  apply List.Sublist.cons_cons
  apply List.Sublist.cons
  apply List.Sublist.cons_cons
  apply List.Sublist.cons
  apply List.Sublist.cons_cons
  exact List.Sublist.slnil

private theorem one_mem_A : (1 : ℝ) ∈ A := by simp [A]
private theorem psi_mem_A : psi ∈ A := by simp [A]

private theorem psi_mem_sig (n k : ℕ) (hk : k ≤ n) : psi ^ k ∈ sig n := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    rw [hk0]
    simp [sig]
  | succ n ih =>
    by_cases hk2 : k ≤ n
    · have hmem : psi ^ k ∈ sig n := ih k hk2
      have h1 : (1 : ℝ) ∈ A := one_mem_A
      have h_eq : psi ^ k = psi ^ k * 1 := by ring
      rw [h_eq]
      simp only [sig, List.mem_flatMap, List.mem_map]
      exact ⟨psi ^ k, hmem, 1, h1, rfl⟩
    · have hk_eq : k = n + 1 := by omega
      rw [hk_eq]
      have hmem : psi ^ n ∈ sig n := ih n (by omega)
      have hpsi : psi ∈ A := psi_mem_A
      have h_eq : psi ^ (n + 1) = psi ^ n * psi := by ring
      rw [h_eq]
      simp only [sig, List.mem_flatMap, List.mem_map]
      exact ⟨psi ^ n, hmem, psi, hpsi, rfl⟩

private theorem A_irr_rep : ∀ x ∈ A_irr, ∃ R : ℤ, R ≠ 0 ∧ x = R * psi ^ 1 := by
  intro x hx
  simp only [A_irr, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨1, by norm_num, by push_cast; ring⟩
  · exact ⟨2, by norm_num, by push_cast; ring⟩
  · exact ⟨3, by norm_num, by push_cast; ring⟩

private theorem flatMap_sublist (l : List ℝ) (s t : ℝ → List ℝ)
    (h : ∀ a, (s a).Sublist (t a)) :
    (l.flatMap s).Sublist (l.flatMap t) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons]
    exact List.Sublist.append (h a) ih

private theorem flatMap_len_irr (l : List ℝ) :
    (l.flatMap (fun a => A_irr.map (fun b => a * b))).length = l.length * 3 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hlen : (A_irr.map (fun b => a * b)).length = 3 := by
      rw [List.length_map, A_irr_len]
    simp only [List.flatMap_cons, List.length_append, hlen, ih, List.length_cons]
    ring

private theorem A_map_sublist_irr (a : ℝ) :
    (A_irr.map (fun b => a * b)).Sublist (A.map (fun b => a * b)) :=
  A_irr_sub.map _

private theorem exists_tau {m : ℕ} (hm : 1 ≤ m) :
    ∃ τ : List ℝ, τ.Sublist (sig (m + 1)) ∧ (sig (m + 1)).length < 2 * τ.length ∧
      ∀ x ∈ τ, Irrational x := by
  have hpsi1_mem : psi ^ 1 ∈ sig m := psi_mem_sig m 1 hm
  have hpsi_mem : psi ∈ sig m := by simpa using hpsi1_mem
  obtain ⟨s, t, h_split⟩ := List.append_of_mem hpsi_mem
  have h_sig_eq : sig (m + 1)
      = (s.flatMap (fun a => A.map (fun b => a * b)))
        ++ ((A.map (fun b => psi * b))
        ++ (t.flatMap (fun a => A.map (fun b => a * b)))) := by
    simp only [sig, h_split, List.flatMap_append, List.flatMap_cons]
  refine ⟨(s.flatMap (fun a => A_irr.map (fun b => a * b)))
    ++ ((A.map (fun b => psi * b))
    ++ (t.flatMap (fun a => A_irr.map (fun b => a * b)))), ?_, ?_, ?_⟩
  · rw [h_sig_eq]
    exact List.Sublist.append
      (flatMap_sublist s _ _ (fun a => A_map_sublist_irr a))
      (List.Sublist.append (List.Sublist.refl _)
        (flatMap_sublist t _ _ (fun a => A_map_sublist_irr a)))
  · have h_len_s : (s.flatMap (fun a => A_irr.map (fun b => a * b))).length = s.length * 3 :=
      flatMap_len_irr s
    have h_len_t : (t.flatMap (fun a => A_irr.map (fun b => a * b))).length = t.length * 3 :=
      flatMap_len_irr t
    have h_len_mid : (A.map (fun b => psi * b)).length = 6 := by
      rw [List.length_map, A_len]
    have h_len_sig : (sig m).length = 6 ^ m := sig_len m
    have h_split_len : s.length + 1 + t.length = 6 ^ m := by
      have h1 : (s ++ psi :: t).length = 6 ^ m := by rw [← h_split, h_len_sig]
      simp only [List.length_append, List.length_cons] at h1
      omega
    have h_tau_len : (((s.flatMap (fun a => A_irr.map (fun b => a * b)))
      ++ ((A.map (fun b => psi * b))
      ++ (t.flatMap (fun a => A_irr.map (fun b => a * b))))).length)
        = s.length * 3 + 6 + t.length * 3 := by
      simp only [List.length_append, h_len_s, h_len_mid, h_len_t]
      ring
    have h_sig_len : (sig (m + 1)).length = 6 * 6 ^ m := by
      rw [sig_len, pow_succ']
    rw [h_sig_len, h_tau_len]
    omega
  · intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx_s | hx_mid | hx_t
    · simp only [List.mem_flatMap, List.mem_map] at hx_s
      obtain ⟨a, ha, b, hb, rfl⟩ := hx_s
      have ha_mem : a ∈ sig m := by rw [h_split]; exact List.mem_append_left _ ha
      obtain ⟨R1, hR1, k1, _, rfl⟩ := sig_rep m a ha_mem
      obtain ⟨R2, hR2, rfl⟩ := A_irr_rep b hb
      have hR : R1 * R2 ≠ 0 := mul_ne_zero hR1 hR2
      have h_eq : (R1 : ℝ) * psi ^ k1 * ((R2 : ℝ) * psi ^ 1)
          = ((R1 * R2 : ℤ) : ℝ) * psi ^ (k1 + 1) := by
        push_cast; rw [pow_add]; ring
      rw [h_eq]
      exact int_mul_psi_pow_irrational hR (by omega)
    · simp only [List.mem_map] at hx_mid
      obtain ⟨b, hb, rfl⟩ := hx_mid
      obtain ⟨R2, hR2, k2, _, rfl⟩ := A_rep b hb
      have hR : (1 : ℤ) * R2 ≠ 0 := by simpa using hR2
      have h_eq : psi * ((R2 : ℝ) * psi ^ k2) = (((1 : ℤ) * R2 : ℤ) : ℝ) * psi ^ (1 + k2) := by
        have hpsi1 : psi = ((1 : ℤ) : ℝ) * psi ^ 1 := by push_cast; ring
        rw [hpsi1]
        push_cast; rw [pow_add]; ring
      rw [h_eq]
      exact int_mul_psi_pow_irrational hR (by omega)
    · simp only [List.mem_flatMap, List.mem_map] at hx_t
      obtain ⟨a, ha, b, hb, rfl⟩ := hx_t
      have ha_mem : a ∈ sig m := by
        rw [h_split]
        exact List.mem_append_right s (List.mem_cons_of_mem psi ha)
      obtain ⟨R1, hR1, k1, _, rfl⟩ := sig_rep m a ha_mem
      obtain ⟨R2, hR2, rfl⟩ := A_irr_rep b hb
      have hR : R1 * R2 ≠ 0 := mul_ne_zero hR1 hR2
      have h_eq : (R1 : ℝ) * psi ^ k1 * ((R2 : ℝ) * psi ^ 1)
          = ((R1 * R2 : ℤ) : ℝ) * psi ^ (k1 + 1) := by
        push_cast; rw [pow_add]; ring
      rw [h_eq]
      exact int_mul_psi_pow_irrational hR (by omega)

/-- **Golden-ratio sequences with vanishing Nicomachean defect.** Let $\varphi = (1 + \sqrt 5)/2$
be the golden ratio and write
$\nu(a_1, \dots, a_k) = (a_1 + \dots + a_k)^2 - (a_1^3 + \dots + a_k^3)$ for the Nicomachean defect
of a finite sequence of real numbers. For every natural number $N$ there is a finite sequence
$\sigma$ of positive real numbers, each of the form $p + q\varphi$ with $p, q \in \mathbb{Z}$, such
that $\nu(\sigma) = 0$, $\sigma$ contains $\varphi^{-n}$ for every $1 \le n \le N$, and $\sigma$ has
a subsequence of irrational entries whose length is more than half the length of $\sigma$.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 7
(`jis-2024-24.6.3-prop-7`). -/
public theorem exists_goldenRatio_nicomachean_sequence (N : ℕ) :
    ∃ σ : List ℝ, (∀ x ∈ σ, 0 < x ∧ ∃ p q : ℤ, x = p + q * Real.goldenRatio) ∧
      (∃ τ : List ℝ, τ.Sublist σ ∧ σ.length < 2 * τ.length ∧ ∀ x ∈ τ, Irrational x) ∧
      nicomacheanNu σ = 0 ∧ ∀ n ∈ Finset.Icc 1 N, Real.goldenRatio⁻¹ ^ n ∈ σ := by
  set n0 := max N 2 with hn0_def
  have hn0_ge : 2 ≤ n0 := le_max_right N 2
  have hN_le : N ≤ n0 := le_max_left N 2
  set m := n0 - 1 with hm_def
  have hm1 : 1 ≤ m := by omega
  have hm_eq : m + 1 = n0 := by omega
  refine ⟨sig n0, ?_, ?_, sig_nu n0, ?_⟩
  · intro x hx
    exact ⟨sig_pos n0 x hx, sig_zphi n0 x hx⟩
  · have htau := exists_tau hm1
    rw [hm_eq] at htau
    exact htau
  · intro n hn
    have hmem := Finset.mem_Icc.mp hn
    have hn_le : n ≤ n0 := le_trans hmem.2 hN_le
    have h_mem : psi ^ n ∈ sig n0 := psi_mem_sig n0 n hn_le
    have h_eq : Real.goldenRatio⁻¹ ^ n = psi ^ n := rfl
    rw [h_eq]
    exact h_mem

end MetaMathlibExt
