/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Stereographic snapping to rational points of `S^1` and `S^3`

A rational approximation `w` of a unit vector is projected stereographically from the pole
opposite in sign to a largest-magnitude coordinate of `w` and inverted exactly over `ℚ`.
Constants follow the frozen snapping contract: `C₁ = 3` for per-coordinate error
`δ ≤ 1/4` on `S^1`, and `C₃ = 4` for `δ ≤ 1/8` on `S^3`.
-/

@[expose] public section

namespace MathlibExt.Quantum.RationalSnapping

set_option autoImplicit false

open scoped BigOperators

/-- Stereographic snap of a rational approximation `w` of a point of the unit sphere in
`ℚ^(n+1)`: project from the pole `-(sign w_k) e_k`, then invert exactly over `ℚ`. -/
def stereoSnap {n : ℕ} (w : Fin (n + 1) → ℚ) (k : Fin (n + 1)) : Fin (n + 1) → ℚ :=
  let s : ℚ := if 0 ≤ w k then 1 else -1
  let t : Fin (n + 1) → ℚ := fun j => if j = k then 0 else w j / (1 + s * w k)
  let r : ℚ := ∑ j, t j ^ 2
  fun j => if j = k then s * (1 - r) / (1 + r) else 2 * t j / (1 + r)

/-- Inverse stereographic formulas land on the unit sphere when the pole sign squares
to one and the projected coordinate at the pole index vanishes. -/
private theorem sum_sq_aux {n : ℕ} {k : Fin (n + 1)} (s : ℚ) (hs : s ^ 2 = 1)
    (t : Fin (n + 1) → ℚ) (ht : t k = 0) (r : ℚ) (hr : r = ∑ i, t i ^ 2) :
    ∑ j, (if j = k then s * (1 - r) / (1 + r) else 2 * t j / (1 + r)) ^ 2 = 1 := by
  have hr_nonneg : 0 ≤ r := by
    rw [hr]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hpos : (0 : ℚ) < 1 + r := by linarith
  have hD : (1 : ℚ) + r ≠ 0 := ne_of_gt hpos
  have hD2 : ((1 : ℚ) + r) ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_ne_zero hD hD
  have hterm : ∀ j : Fin (n + 1),
      (2 * t j / (1 + r)) ^ 2 = (t j ^ 2) * (4 / (1 + r) ^ 2) := by
    intro j
    field_simp
    ring
  have hB : ∑ j, (2 * t j / (1 + r)) ^ 2 = r * (4 / (1 + r) ^ 2) := by
    simp_rw [hterm, ← Finset.sum_mul, ← hr]
  have hA : (s * (1 - r) / (1 + r)) ^ 2 = (1 - r) ^ 2 / (1 + r) ^ 2 := by
    rw [div_pow, mul_pow, hs, one_mul]
  have h0 : ((2 : ℚ) * 0 / (1 + r)) ^ 2 = 0 := by norm_num
  have hC : ∀ j : Fin (n + 1),
      (if j = k then s * (1 - r) / (1 + r) else 2 * t j / (1 + r)) ^ 2
        = (2 * t j / (1 + r)) ^ 2
          + (if j = k then (s * (1 - r) / (1 + r)) ^ 2 - (2 * t k / (1 + r)) ^ 2
            else 0) := by
    intro j
    by_cases hj : j = k
    · subst hj
      simp only [eq_self_iff_true, ite_true]
      abel
    · simp only [hj, ite_false, add_zero]
  simp_rw [hC]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  rw [hB, ht, hA, h0, sub_zero]
  field_simp
  ring

/-- The snapped point lies exactly on the unit sphere. -/
theorem sum_sq_stereoSnap {n : ℕ} (w : Fin (n + 1) → ℚ) (k : Fin (n + 1)) :
    ∑ j, stereoSnap w k j ^ 2 = 1 := by
  have hs : (if 0 ≤ w k then (1 : ℚ) else -1) ^ 2 = 1 := by
    by_cases h : (0 : ℚ) ≤ w k
    · rw [ite_eq_left h]
      norm_num
    · rw [ite_eq_right h]
      norm_num
  have ht : (fun j => if j = k then (0 : ℚ)
      else w j / (1 + (if 0 ≤ w k then (1 : ℚ) else -1) * w k)) k = 0 := by
    simp only [eq_self_iff_true, ite_true]
  exact sum_sq_aux (if 0 ≤ w k then (1 : ℚ) else -1) hs
    (fun j => if j = k then (0 : ℚ)
      else w j / (1 + (if 0 ≤ w k then (1 : ℚ) else -1) * w k)) ht _ rfl

/-- Projecting an exact rational sphere point and inverting recovers it, when the pole
sign squares to one, the projection has the stereographic form off the pole index and
the pole denominator is nonzero. -/
private theorem stereoSnap_eq_self_aux {n : ℕ} {z : Fin (n + 1) → ℚ} {k : Fin (n + 1)}
    (hz : ∑ j, z j ^ 2 = 1) (s : ℚ) (hs : s ^ 2 = 1) (t : Fin (n + 1) → ℚ)
    (htk : t k = 0) (htj : ∀ j, j ≠ k → t j = z j / (1 + s * z k))
    (hD : (1 : ℚ) + s * z k ≠ 0) (r : ℚ) (hr : r = ∑ i, t i ^ 2) :
    (fun j => if j = k then s * (1 - r) / (1 + r) else 2 * t j / (1 + r)) = z := by
  have hD2 : ((1 : ℚ) + s * z k) ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_ne_zero hD hD
  have htsq : ∀ i : Fin (n + 1), t i ^ 2
      = (z i / (1 + s * z k)) ^ 2
        - (if i = k then (z i / (1 + s * z k)) ^ 2 else 0) := by
    intro i
    by_cases hi : i = k
    · subst hi
      simp only [htk, eq_self_iff_true, ite_true, sub_self]
      norm_num
    · simp only [hi, ite_false, htj i hi, sub_zero]
  have hsum : ∑ i, (z i / (1 + s * z k)) ^ 2 = 1 / (1 + s * z k) ^ 2 := by
    have h1 : ∀ i : Fin (n + 1),
        (z i / (1 + s * z k)) ^ 2 = (z i ^ 2) * (1 / (1 + s * z k) ^ 2) := by
      intro i
      field_simp
    simp_rw [h1, ← Finset.sum_mul, hz, one_mul]
  have hr_eq : r = (1 - z k ^ 2) / (1 + s * z k) ^ 2 := by
    rw [hr]
    simp_rw [htsq]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    rw [hsum]
    field_simp
  have hmul : (1 + r) * (1 + s * z k) ^ 2 = 2 * (1 + s * z k) := by
    rw [hr_eq, add_mul, one_mul, div_mul_cancel₀ _ hD2]
    linear_combination z k ^ 2 * hs
  rw [pow_two, ← mul_assoc] at hmul
  have hDr : (1 + r) * (1 + s * z k) = 2 := mul_right_cancel₀ hD hmul
  have h1r_ne : (1 : ℚ) + r ≠ 0 := by
    intro hcon
    rw [hcon, zero_mul] at hDr
    norm_num at hDr
  funext j
  by_cases hj : j = k
  · subst hj
    simp only [eq_self_iff_true, ite_true]
    rw [div_eq_iff h1r_ne]
    have e : (s * (1 - r)) * (1 + s * z j) ^ 2
        = (z j * (1 + r)) * (1 + s * z j) ^ 2 := by
      rw [hr_eq, mul_assoc, mul_assoc, sub_mul, one_mul, div_mul_cancel₀ _ hD2,
        add_mul, one_mul, div_mul_cancel₀ _ hD2]
      linear_combination (2 * z j + s * z j ^ 2 - z j ^ 3) * hs
    exact mul_right_cancel₀ hD2 e
  · simp only [hj, ite_false]
    rw [htj j hj, div_eq_iff h1r_ne]
    have e1 : (2 * (z j / (1 + s * z k))) * (1 + s * z k) = 2 * z j := by
      rw [mul_assoc, div_mul_cancel₀ _ hD]
    have e2 : (z j * (1 + r)) * (1 + s * z k) = 2 * z j := by
      rw [mul_assoc, hDr]
      ring
    have e : (2 * (z j / (1 + s * z k))) * (1 + s * z k)
        = (z j * (1 + r)) * (1 + s * z k) := by
      rw [e1, e2]
    exact mul_right_cancel₀ hD e

/-- Snapping an exact rational point of the unit sphere returns it (any pole index). -/
theorem stereoSnap_eq_self {n : ℕ} {z : Fin (n + 1) → ℚ} (hz : ∑ j, z j ^ 2 = 1)
    (k : Fin (n + 1)) : stereoSnap z k = z := by
  have hs : (if 0 ≤ z k then (1 : ℚ) else -1) ^ 2 = 1 := by
    by_cases h : (0 : ℚ) ≤ z k
    · rw [ite_eq_left h]
      norm_num
    · rw [ite_eq_right h]
      norm_num
  have hD : (1 : ℚ) + (if 0 ≤ z k then (1 : ℚ) else -1) * z k ≠ 0 := by
    by_cases h : (0 : ℚ) ≤ z k
    · rw [ite_eq_left h]
      have hpos : (0 : ℚ) < 1 + 1 * z k := by linarith
      exact ne_of_gt hpos
    · rw [ite_eq_right h]
      have hpos : (0 : ℚ) < 1 + -1 * z k := by linarith
      exact ne_of_gt hpos
  have htk : (fun j => if j = k then (0 : ℚ)
      else z j / (1 + (if 0 ≤ z k then (1 : ℚ) else -1) * z k)) k = 0 := by
    simp only [eq_self_iff_true, ite_true]
  have htj : ∀ j, j ≠ k → (fun j => if j = k then (0 : ℚ)
        else z j / (1 + (if 0 ≤ z k then (1 : ℚ) else -1) * z k)) j
      = z j / (1 + (if 0 ≤ z k then (1 : ℚ) else -1) * z k) := by
    intro j hj
    simp only [hj, ite_false]
  exact stereoSnap_eq_self_aux hz (if 0 ≤ z k then (1 : ℚ) else -1) hs
    (fun j => if j = k then (0 : ℚ)
      else z j / (1 + (if 0 ≤ z k then (1 : ℚ) else -1) * z k)) htk htj hD _ rfl

/-- A largest-magnitude coordinate of `w` (the first one on ties). -/
def poleIndex {n : ℕ} (w : Fin (n + 1) → ℚ) : Fin (n + 1) :=
  (List.finRange (n + 1)).foldl (fun b j => if |w b| < |w j| then j else b) 0

/-- Folding the argmax step over any list keeps an accumulator that dominates both the
starting value and every listed element in magnitude. -/
private theorem abs_le_foldl {n : ℕ} (w : Fin (n + 1) → ℚ) :
    ∀ (l : List (Fin (n + 1))) (b : Fin (n + 1)),
      |w b| ≤ |w (l.foldl (fun b j => if |w b| < |w j| then j else b) b)|
      ∧ ∀ x ∈ l,
        |w x| ≤ |w (l.foldl (fun b j => if |w b| < |w j| then j else b) b)| := by
  intro l
  induction l with
  | nil =>
    intro b
    simp only [List.foldl_nil]
    exact ⟨le_of_eq rfl, fun x hx => False.elim ((List.mem_nil_iff x).mp hx)⟩
  | cons hd tl ih =>
    intro b
    rw [List.foldl_cons]
    by_cases h : |w b| < |w hd|
    · simp only [h, ite_true]
      have ihhd := ih hd
      constructor
      · exact le_trans (le_of_lt h) ihhd.1
      · intro x hx
        simp only [List.mem_cons] at hx
        cases hx with
        | inl hxhd =>
          subst hxhd
          exact ihhd.1
        | inr hxtl =>
          exact ihhd.2 x hxtl
    · simp only [h, ite_false]
      have ihb := ih b
      have hle : |w hd| ≤ |w b| := le_of_not_gt h
      constructor
      · exact ihb.1
      · intro x hx
        simp only [List.mem_cons] at hx
        cases hx with
        | inl hxhd =>
          subst hxhd
          exact le_trans hle ihb.1
        | inr hxtl =>
          exact ihb.2 x hxtl

theorem abs_le_abs_poleIndex {n : ℕ} (w : Fin (n + 1) → ℚ) (j : Fin (n + 1)) :
    |w j| ≤ |w (poleIndex w)| := by
  have h := (abs_le_foldl w (List.finRange (n + 1)) 0).2 j (List.mem_finRange j)
  exact h

/-- The snapping map with the frozen pole rule. -/
def snap {n : ℕ} (w : Fin (n + 1) → ℚ) : Fin (n + 1) → ℚ := stereoSnap w (poleIndex w)

/-- Inverse stereographic map `ℝ^n → S^n ⊂ ℝ^(n+1)` from the pole `-e_0`. -/
noncomputable def invStereo {n : ℕ} (t : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.cons ((1 - ‖t‖ ^ 2) / (1 + ‖t‖ ^ 2))
    (fun j => 2 * t j / (1 + ‖t‖ ^ 2)))

/-- Constant certificate: the inverse stereographic map is `2`-Lipschitz. -/
theorem lipschitzWith_invStereo (n : ℕ) :
    LipschitzWith 2 (invStereo (n := n)) := by
  refine LipschitzWith.of_dist_le_mul fun t u => ?_
  have h2 : ((2 : NNReal) : ℝ) = 2 := by norm_num
  rw [h2]
  simp only [dist_eq_norm]
  have hnorm2 : ∀ (m : ℕ) (x : EuclideanSpace ℝ (Fin m)),
      ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
    intro m x
    have hnn : (0 : ℝ) ≤ ∑ i, ‖x i‖ ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt hnn]
    simp only [Real.norm_eq_abs, sq_abs]
  have hA : (0 : ℝ) < 1 + ‖t‖ ^ 2 := by linarith [sq_nonneg ‖t‖]
  have hB : (0 : ℝ) < 1 + ‖u‖ ^ 2 := by linarith [sq_nonneg ‖u‖]
  have hAne : (1 : ℝ) + ‖t‖ ^ 2 ≠ 0 := ne_of_gt hA
  have hBne : (1 : ℝ) + ‖u‖ ^ 2 ≠ 0 := ne_of_gt hB
  have hABne : (1 + ‖t‖ ^ 2) * (1 + ‖u‖ ^ 2) ≠ 0 := mul_ne_zero hAne hBne
  have hAB2ne : ((1 + ‖t‖ ^ 2) * (1 + ‖u‖ ^ 2)) ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_ne_zero hABne hABne
  have hft0 : (invStereo t) 0 = (1 - ‖t‖ ^ 2) / (1 + ‖t‖ ^ 2) := by
    simp only [invStereo]
    exact Fin.cons_zero _ _
  have hfu0 : (invStereo u) 0 = (1 - ‖u‖ ^ 2) / (1 + ‖u‖ ^ 2) := by
    simp only [invStereo]
    exact Fin.cons_zero _ _
  have hftS : ∀ i : Fin n, (invStereo t) i.succ = 2 * t i / (1 + ‖t‖ ^ 2) := by
    intro i
    simp only [invStereo]
    exact Fin.cons_succ _ _ _
  have hfuS : ∀ i : Fin n, (invStereo u) i.succ = 2 * u i / (1 + ‖u‖ ^ 2) := by
    intro i
    simp only [invStereo]
    exact Fin.cons_succ _ _ _
  have hdiff0 : (invStereo t - invStereo u) 0
      = (1 - ‖t‖ ^ 2) / (1 + ‖t‖ ^ 2) - (1 - ‖u‖ ^ 2) / (1 + ‖u‖ ^ 2) := by
    show (invStereo t) 0 - (invStereo u) 0 = _
    rw [hft0, hfu0]
  have hdiffS : ∀ i : Fin n, ((invStereo t - invStereo u) i.succ) ^ 2
      = (2 * t i / (1 + ‖t‖ ^ 2) - 2 * u i / (1 + ‖u‖ ^ 2)) ^ 2 := by
    intro i
    show ((invStereo t) i.succ - (invStereo u) i.succ) ^ 2 = _
    rw [hftS i, hfuS i]
  have hsplit : ‖invStereo t - invStereo u‖ ^ 2
      = ((1 - ‖t‖ ^ 2) / (1 + ‖t‖ ^ 2) - (1 - ‖u‖ ^ 2) / (1 + ‖u‖ ^ 2)) ^ 2
        + ∑ i : Fin n, (2 * t i / (1 + ‖t‖ ^ 2) - 2 * u i / (1 + ‖u‖ ^ 2)) ^ 2 := by
    rw [hnorm2, Fin.sum_univ_succ, hdiff0]
    simp_rw [hdiffS]
  have hhead2 : ((1 - ‖t‖ ^ 2) / (1 + ‖t‖ ^ 2) - (1 - ‖u‖ ^ 2) / (1 + ‖u‖ ^ 2)) ^ 2
      = 4 * (‖u‖ ^ 2 - ‖t‖ ^ 2) ^ 2 / ((1 + ‖t‖ ^ 2) * (1 + ‖u‖ ^ 2)) ^ 2 := by
    field_simp
    ring
  have htail : ∀ i : Fin n, (2 * t i / (1 + ‖t‖ ^ 2) - 2 * u i / (1 + ‖u‖ ^ 2)) ^ 2
      = 4 * ((1 + ‖u‖ ^ 2) * t i - (1 + ‖t‖ ^ 2) * u i) ^ 2
        / ((1 + ‖t‖ ^ 2) * (1 + ‖u‖ ^ 2)) ^ 2 := by
    intro i
    field_simp
    ring
  have hfac : ∀ i : Fin n,
      4 * ((1 + ‖u‖ ^ 2) * t i - (1 + ‖t‖ ^ 2) * u i) ^ 2
        / ((1 + ‖t‖ ^ 2) * (1 + ‖u‖ ^ 2)) ^ 2
      = (((1 + ‖u‖ ^ 2) * t i - (1 + ‖t‖ ^ 2) * u i) ^ 2)
        * (4 / ((1 + ‖t‖ ^ 2) * (1 + ‖u‖ ^ 2)) ^ 2) := by
    intro i
    rw [← mul_div_assoc, mul_comm _ 4]
  have htailSum : ∑ i : Fin n, (2 * t i / (1 + ‖t‖ ^ 2) - 2 * u i / (1 + ‖u‖ ^ 2)) ^ 2
      = (∑ i : Fin n, ((1 + ‖u‖ ^ 2) * t i - (1 + ‖t‖ ^ 2) * u i) ^ 2)
        * (4 / ((1 + ‖t‖ ^ 2) * (1 + ‖u‖ ^ 2)) ^ 2) := by
    simp_rw [htail, hfac, ← Finset.sum_mul]
  have hexpand : ∀ i : Fin n, ((1 + ‖u‖ ^ 2) * t i - (1 + ‖t‖ ^ 2) * u i) ^ 2
      = (t i ^ 2) * ((1 + ‖u‖ ^ 2) ^ 2) - (t i * u i) * (2 * ((1 + ‖t‖ ^ 2) * (1 + ‖u‖ ^ 2)))
        + (u i ^ 2) * ((1 + ‖t‖ ^ 2) ^ 2) := by
    intro i
    ring
  have hexpandS : ∀ i : Fin n, (t i - u i) ^ 2
      = (t i ^ 2) - (t i * u i) * 2 + (u i ^ 2) := by
    intro i
    ring
  have hsumY : ∑ i : Fin n, ((1 + ‖u‖ ^ 2) * t i - (1 + ‖t‖ ^ 2) * u i) ^ 2
      = ‖t‖ ^ 2 * ((1 + ‖u‖ ^ 2) ^ 2) - (∑ i, t i * u i) * (2 * ((1 + ‖t‖ ^ 2) * (1 + ‖u‖ ^ 2)))
        + ‖u‖ ^ 2 * ((1 + ‖t‖ ^ 2) ^ 2) := by
    simp_rw [hexpand]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      ← Finset.sum_mul, ← hnorm2 n t, ← hnorm2 n u]
  have hsumS : ∑ i : Fin n, (t i - u i) ^ 2
      = ‖t‖ ^ 2 - (∑ i, t i * u i) * 2 + ‖u‖ ^ 2 := by
    simp_rw [hexpandS]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← hnorm2 n t, ← hnorm2 n u]
  have hsub : ∀ i : Fin n, (t - u : EuclideanSpace ℝ (Fin n)) i = t i - u i :=
    fun i => rfl
  have hS : ‖t - u‖ ^ 2 = ‖t‖ ^ 2 - (∑ i, t i * u i) * 2 + ‖u‖ ^ 2 := by
    rw [hnorm2]
    simp_rw [hsub]
    rw [hsumS]
  have hcore : (‖u‖ ^ 2 - ‖t‖ ^ 2) ^ 2
        + ∑ i : Fin n, ((1 + ‖u‖ ^ 2) * t i - (1 + ‖t‖ ^ 2) * u i) ^ 2
      = ‖t - u‖ ^ 2 * ((1 + ‖t‖ ^ 2) * (1 + ‖u‖ ^ 2)) := by
    rw [hsumY, hS]
    ring
  have hnum : 4 * (‖u‖ ^ 2 - ‖t‖ ^ 2) ^ 2
        + (∑ i : Fin n, ((1 + ‖u‖ ^ 2) * t i - (1 + ‖t‖ ^ 2) * u i) ^ 2) * 4
      = 4 * (‖t - u‖ ^ 2 * ((1 + ‖t‖ ^ 2) * (1 + ‖u‖ ^ 2))) := by
    linear_combination 4 * hcore
  have hkey : ‖invStereo t - invStereo u‖ ^ 2
      = 4 * ‖t - u‖ ^ 2 / ((1 + ‖t‖ ^ 2) * (1 + ‖u‖ ^ 2)) := by
    rw [hsplit, hhead2, htailSum, ← mul_div_assoc, ← add_div, hnum]
    field_simp
  have hAB1 : (1 : ℝ) ≤ (1 + ‖t‖ ^ 2) * (1 + ‖u‖ ^ 2) := by
    have e : (1 + ‖t‖ ^ 2) * (1 + ‖u‖ ^ 2) - 1
        = ‖t‖ ^ 2 + ‖u‖ ^ 2 + ‖t‖ ^ 2 * ‖u‖ ^ 2 := by ring
    have hnn : (0 : ℝ) ≤ ‖t‖ ^ 2 + ‖u‖ ^ 2 + ‖t‖ ^ 2 * ‖u‖ ^ 2 :=
      add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    linarith
  have hfin : ‖invStereo t - invStereo u‖ ≤ 2 * ‖t - u‖ := by
    have hsq : ‖invStereo t - invStereo u‖ ^ 2 ≤ (2 * ‖t - u‖) ^ 2 := by
      have hSnn : (0 : ℝ) ≤ 4 * ‖t - u‖ ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
      have hle : 4 * ‖t - u‖ ^ 2 / ((1 + ‖t‖ ^ 2) * (1 + ‖u‖ ^ 2)) ≤ 4 * ‖t - u‖ ^ 2 :=
        div_le_self hSnn hAB1
      have h4 : (2 * ‖t - u‖) ^ 2 = 4 * ‖t - u‖ ^ 2 := by ring
      rw [hkey, h4]
      exact hle
    have habs := sq_le_sq.mp hsq
    have hnn1 : (0 : ℝ) ≤ ‖invStereo t - invStereo u‖ := by positivity
    have hnn2 : (0 : ℝ) ≤ 2 * ‖t - u‖ := by positivity
    rw [abs_of_nonneg hnn1, abs_of_nonneg hnn2] at habs
    exact habs
  exact hfin

/-- The rational point `w` viewed in Euclidean space. -/
def toEuclid {n : ℕ} (w : Fin n → ℚ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => (w j : ℝ))

/-- Real-analytic core of `S^1` snapping: the chordal estimate for a general pole.
All inputs are real; the caller supplies the rational approximations and casts. -/
private theorem dist_circle_aux {k : Fin 2} {z : EuclideanSpace ℝ (Fin 2)} (hz : ‖z‖ = 1)
    (W : Fin 2 → ℝ) (s : ℝ) (hs : s ^ 2 = 1)
    (D : ℝ) (hDdef : D = 1 + s * W k)
    (T : Fin 2 → ℝ) (hTk : T k = 0) (hTj : ∀ j, j ≠ k → T j = W j / D)
    (R : ℝ) (hR : R = ∑ i, T i ^ 2)
    (X : EuclideanSpace ℝ (Fin 2))
    (hX : ∀ j, X j = (if j = k then s * (1 - R) / (1 + R) else 2 * T j / (1 + R)))
    (δ : ℝ) (hδ : δ ≤ 1 / 4)
    (hw : ∀ j, |W j - z j| ≤ δ) (hk : ∀ j, |W j| ≤ |W k|)
    (hwk : (0 : ℝ) ≤ s * W k) :
    dist X z ≤ 3 * δ := by
  have hnorm2 : ∀ (m : ℕ) (x : EuclideanSpace ℝ (Fin m)),
      ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
    intro m x
    have hnn : (0 : ℝ) ≤ ∑ i, ‖x i‖ ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt hnn]
    simp only [Real.norm_eq_abs, sq_abs]
  have hsum1 : ∑ i, (z i) ^ 2 = 1 := by
    rw [← hnorm2 2 z, hz, one_pow]
  have hδnn : (0 : ℝ) ≤ δ := le_trans (abs_nonneg _) (hw k)
  have hs_pm : s = 1 ∨ s = -1 := by
    have hfac : (s - 1) * (s + 1) = 0 := by linear_combination hs
    rcases mul_eq_zero.mp hfac with h | h
    · left; linarith
    · right; linarith
  have hsgn : s * W k = |W k| := by
    rcases hs_pm with rfl | rfl
    · rw [one_mul]
      have hwknn : (0 : ℝ) ≤ W k := by linarith [hwk]
      rw [abs_of_nonneg hwknn]
    · have hwknn : W k ≤ 0 := by linarith [hwk]
      rw [abs_of_nonpos hwknn]
      ring
  have hRnn : (0 : ℝ) ≤ R := by
    rw [hR]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h1Rpos : (0 : ℝ) < 1 + R := by linarith [hRnn]
  have h1Rne : (1 : ℝ) + R ≠ 0 := ne_of_gt h1Rpos
  have htri : ∀ j, |z j| - δ ≤ |W k| := by
    intro j
    have h1 : |W j| ≤ |W k| := hk j
    have e1 : |z j| ≤ |z j - W j| + |W j| := by
      have := abs_add_le (z j - W j) (W j)
      rwa [sub_add_cancel] at this
    have e2 : |z j - W j| = |W j - z j| := by
      have : z j - W j = -(W j - z j) := by ring
      rw [this, abs_neg]
    linarith [hw j]
  have hWk45 : (0.45 : ℝ) ≤ |W k| := by
    by_cases h0 : (0.7 : ℝ) ≤ |z 0|
    · linarith [htri 0, h0, hδ]
    · push_neg at h0
      have h1 : (0.7 : ℝ) ≤ |z 1| := by
        by_contra hc
        push_neg at hc
        have ab07 : |(0.7 : ℝ)| = 0.7 := abs_of_nonneg (by norm_num)
        have hlt0 : |z 0| < |(0.7 : ℝ)| := by rw [ab07]; exact h0
        have hlt1 : |z 1| < |(0.7 : ℝ)| := by rw [ab07]; exact hc
        have e0 := sq_lt_sq.mpr hlt0
        have e1 := sq_lt_sq.mpr hlt1
        have h49 : (0.7 : ℝ) ^ 2 = 0.49 := by norm_num
        rw [h49] at e0 e1
        have hsum2 : ∑ i, (z i) ^ 2 = z 0 ^ 2 + z 1 ^ 2 := Fin.sum_univ_two _
        linarith [hsum1, hsum2, e0, e1]
      linarith [htri 1, h1, hδ]
  have hD145 : (1.45 : ℝ) ≤ D := by linarith [hDdef, hsgn, hWk45]
  have hDpos : (0 : ℝ) < D := by linarith [hD145]
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hSx : |s * (z k - W k)| ≤ δ := by
    have hx : |z k - W k| ≤ δ := by
      have e : |z k - W k| = |W k - z k| := by
        have : z k - W k = -(W k - z k) := by ring
        rw [this, abs_neg]
      rw [e]; exact hw k
    have hsq : (s * (z k - W k)) ^ 2 ≤ δ ^ 2 := by
      have h2 : (s * (z k - W k)) ^ 2 = (z k - W k) ^ 2 := by
        rw [mul_pow, hs, one_mul]
      have h3 : (z k - W k) ^ 2 ≤ δ ^ 2 := by
        have habs : |z k - W k| ≤ |δ| := by
          rw [abs_of_nonneg hδnn]; exact hx
        exact sq_le_sq.mpr habs
      rw [h2]; exact h3
    have habs2 := sq_le_sq.mp hsq
    rwa [abs_of_nonneg hδnn] at habs2
  have hSx_neg : -δ ≤ s * (z k - W k) := by
    by_cases hnn : (0 : ℝ) ≤ s * (z k - W k)
    · linarith [hδnn]
    · push_neg at hnn
      have e : |s * (z k - W k)| = -(s * (z k - W k)) := abs_of_neg hnn
      linarith [hSx, e]
  have hDz12 : (1.2 : ℝ) ≤ 1 + s * z k := by
    have h1 : s * z k = s * W k + s * (z k - W k) := by ring
    linarith [h1, hsgn, hWk45, hSx_neg, hδ]
  have hDzpos : (0 : ℝ) < 1 + s * z k := by linarith [hDz12]
  have hDzne : (1 : ℝ) + s * z k ≠ 0 := ne_of_gt hDzpos
  have hDz2ne : ((1 : ℝ) + s * z k) ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_ne_zero hDzne hDzne
  set P : Fin 2 → ℝ := fun j => if j = k then 0 else z j / (1 + s * z k) with hP
  set Rz : ℝ := ∑ i, P i ^ 2 with hRz
  have hPk : P k = 0 := by simp only [hP, eq_self_iff_true, ite_true]
  have hPj : ∀ j, j ≠ k → P j = z j / (1 + s * z k) := by
    intro j hj
    simp only [hP, hj, ite_false]
  have hRznn : (0 : ℝ) ≤ Rz := by
    rw [hRz]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h1Rzpos : (0 : ℝ) < 1 + Rz := by linarith [hRznn]
  have h1Rzne : (1 : ℝ) + Rz ≠ 0 := ne_of_gt h1Rzpos
  have hABne : (1 + R) * (1 + Rz) ≠ 0 := mul_ne_zero h1Rne h1Rzne
  have hAB2ne : ((1 + R) * (1 + Rz)) ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_ne_zero hABne hABne
  have htsqz : ∀ i : Fin 2, P i ^ 2
      = (z i / (1 + s * z k)) ^ 2
        - (if i = k then (z i / (1 + s * z k)) ^ 2 else 0) := by
    intro i
    by_cases hi : i = k
    · subst hi
      simp only [hPk, eq_self_iff_true, ite_true, sub_self]
      norm_num
    · simp only [hi, ite_false, hPj i hi, sub_zero]
  have hsumz : ∑ i, (z i / (1 + s * z k)) ^ 2 = 1 / (1 + s * z k) ^ 2 := by
    have h1 : ∀ i : Fin 2,
        (z i / (1 + s * z k)) ^ 2 = (z i ^ 2) * (1 / (1 + s * z k) ^ 2) := by
      intro i
      field_simp
    simp_rw [h1, ← Finset.sum_mul, hsum1, one_mul]
  have hRz_eq : Rz = (1 - z k ^ 2) / (1 + s * z k) ^ 2 := by
    rw [hRz]
    simp_rw [htsqz]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    rw [hsumz]
    field_simp
  have hmulz : (1 + Rz) * (1 + s * z k) ^ 2 = 2 * (1 + s * z k) := by
    rw [hRz_eq, add_mul, one_mul, div_mul_cancel₀ _ hDz2ne]
    linear_combination z k ^ 2 * hs
  rw [pow_two, ← mul_assoc] at hmulz
  have hDrz : (1 + Rz) * (1 + s * z k) = 2 := mul_right_cancel₀ hDzne hmulz
  have hzk : z k = s * (1 - Rz) / (1 + Rz) := by
    have e : (s * (1 - Rz)) * (1 + s * z k) ^ 2
        = (z k * (1 + Rz)) * (1 + s * z k) ^ 2 := by
      rw [hRz_eq, mul_assoc, mul_assoc, sub_mul, one_mul, div_mul_cancel₀ _ hDz2ne,
        add_mul, one_mul, div_mul_cancel₀ _ hDz2ne]
      linear_combination (2 * z k + s * z k ^ 2 - z k ^ 3) * hs
    have e2 := mul_right_cancel₀ hDz2ne e
    field_simp
    linarith [e2]
  have hzj : ∀ j, j ≠ k → z j = 2 * P j / (1 + Rz) := by
    intro j hj
    have e1 : (2 * (z j / (1 + s * z k))) * (1 + s * z k) = 2 * z j := by
      rw [mul_assoc, div_mul_cancel₀ _ hDzne]
    have e2 : (z j * (1 + Rz)) * (1 + s * z k) = 2 * z j := by
      rw [mul_assoc, hDrz]
      ring
    have e : (2 * (z j / (1 + s * z k))) * (1 + s * z k)
        = (z j * (1 + Rz)) * (1 + s * z k) := by
      rw [e1, e2]
    have hcan := mul_right_cancel₀ hDzne e
    rw [hPj j hj]
    field_simp
    linarith [hcan]
  have hdiffXk : X k - z k
      = s * (1 - R) / (1 + R) - s * (1 - Rz) / (1 + Rz) := by
    rw [hX k, ite_eq_left rfl, hzk]
  have hdiffXj : ∀ j, j ≠ k → X j - z j = 2 * T j / (1 + R) - 2 * P j / (1 + Rz) := by
    intro j hj
    rw [hX j, ite_eq_right hj, hzj j hj]
  have hC : ∀ j : Fin 2, (X j - z j) ^ 2
      = (2 * T j / (1 + R) - 2 * P j / (1 + Rz)) ^ 2
        + (if j = k then (s * (1 - R) / (1 + R) - s * (1 - Rz) / (1 + Rz)) ^ 2
          - (2 * T k / (1 + R) - 2 * P k / (1 + Rz)) ^ 2 else 0) := by
    intro j
    by_cases hj : j = k
    · subst hj
      simp only [eq_self_iff_true, ite_true]
      rw [hdiffXk]
      abel
    · simp only [hj, ite_false]
      rw [hdiffXj j hj, add_zero]
  have hTk0 : (2 * T k / (1 + R) - 2 * P k / (1 + Rz)) ^ 2 = 0 := by
    rw [hTk, hPk]
    norm_num
  have hchord : ‖X - z‖ ^ 2
      = 4 * (∑ i, (T i - P i) ^ 2) / ((1 + R) * (1 + Rz)) := by
    have hsplit2 : ‖X - z‖ ^ 2
        = (s * (1 - R) / (1 + R) - s * (1 - Rz) / (1 + Rz)) ^ 2
          + ∑ j : Fin 2, (2 * T j / (1 + R) - 2 * P j / (1 + Rz)) ^ 2 := by
      rw [hnorm2]
      have hsub : ∀ i : Fin 2, ((X - z) i) = (X i - z i) := fun i => by simp
      simp_rw [hsub, hC]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ite_true]
      rw [hTk0, sub_zero, add_comm]
    have hA : (s * (1 - R) / (1 + R) - s * (1 - Rz) / (1 + Rz)) ^ 2
        = 4 * (Rz - R) ^ 2 / ((1 + R) * (1 + Rz)) ^ 2 := by
      have hs2 : (s * (1 - R) / (1 + R) - s * (1 - Rz) / (1 + Rz))
          = s * ((1 - R) / (1 + R) - (1 - Rz) / (1 + Rz)) := by ring
      rw [hs2, mul_pow, hs, one_mul]
      field_simp
      ring
    have hB : ∀ j : Fin 2, (2 * T j / (1 + R) - 2 * P j / (1 + Rz)) ^ 2
        = 4 * ((1 + Rz) * T j - (1 + R) * P j) ^ 2 / ((1 + R) * (1 + Rz)) ^ 2 := by
      intro j
      field_simp
      ring
    have hCsum : ∑ j : Fin 2, (2 * T j / (1 + R) - 2 * P j / (1 + Rz)) ^ 2
        = (∑ j : Fin 2, ((1 + Rz) * T j - (1 + R) * P j) ^ 2)
          * (4 / ((1 + R) * (1 + Rz)) ^ 2) := by
      have hfac : ∀ j : Fin 2,
          4 * ((1 + Rz) * T j - (1 + R) * P j) ^ 2 / ((1 + R) * (1 + Rz)) ^ 2
          = (((1 + Rz) * T j - (1 + R) * P j) ^ 2) * (4 / ((1 + R) * (1 + Rz)) ^ 2) := by
        intro j
        rw [← mul_div_assoc, mul_comm _ 4]
      simp_rw [hB, hfac, ← Finset.sum_mul]
    have hexp : ∀ j : Fin 2, ((1 + Rz) * T j - (1 + R) * P j) ^ 2
        = (T j ^ 2) * ((1 + Rz) ^ 2) - (T j * P j) * (2 * ((1 + R) * (1 + Rz)))
          + (P j ^ 2) * ((1 + R) ^ 2) := by
      intro j
      ring
    have hexpS : ∀ j : Fin 2, (T j - P j) ^ 2
        = (T j ^ 2) - (T j * P j) * 2 + (P j ^ 2) := by
      intro j
      ring
    have hsumY : ∑ j : Fin 2, ((1 + Rz) * T j - (1 + R) * P j) ^ 2
        = R * ((1 + Rz) ^ 2) - (∑ i, T i * P i) * (2 * ((1 + R) * (1 + Rz)))
          + Rz * ((1 + R) ^ 2) := by
      simp_rw [hexp]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        ← Finset.sum_mul, ← hR, ← hRz]
    have hsumS : ∑ j : Fin 2, (T j - P j) ^ 2
        = R - (∑ i, T i * P i) * 2 + Rz := by
      simp_rw [hexpS]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← hR, ← hRz]
    have hcore : (Rz - R) ^ 2 + ∑ j : Fin 2, ((1 + Rz) * T j - (1 + R) * P j) ^ 2
        = (∑ j : Fin 2, (T j - P j) ^ 2) * ((1 + R) * (1 + Rz)) := by
      rw [hsumY, hsumS]
      ring
    have hnum : 4 * (Rz - R) ^ 2
          + (∑ j : Fin 2, ((1 + Rz) * T j - (1 + R) * P j) ^ 2) * 4
        = 4 * ((∑ j : Fin 2, (T j - P j) ^ 2) * ((1 + R) * (1 + Rz))) := by
      linear_combination 4 * hcore
    rw [hsplit2, hA, hCsum, ← mul_div_assoc, ← add_div, hnum]
    field_simp
  have hDDne : D * (1 + s * z k) ≠ 0 := mul_ne_zero hDne hDzne
  have heq : ∀ j, j ≠ k → T j - P j
      = ((W j - z j) * (1 + s * z k) + z j * ((1 + s * z k) - D)) / (D * (1 + s * z k)) := by
    intro j hj
    rw [hTj j hj, hPj j hj]
    field_simp
    ring
  have hz1 : ∀ j : Fin 2, |z j| ≤ 1 := by
    intro j
    fin_cases j
    · have h2 : ∑ i, (z i) ^ 2 = z 0 ^ 2 + z 1 ^ 2 := Fin.sum_univ_two _
      have hle : z 0 ^ 2 ≤ 1 := by linarith [hsum1, h2, sq_nonneg (z 1)]
      have hle2 : z 0 ^ 2 ≤ (1 : ℝ) ^ 2 := by rw [one_pow]; exact hle
      have habs := sq_le_sq.mp hle2
      rwa [abs_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)] at habs
    · have h2 : ∑ i, (z i) ^ 2 = z 0 ^ 2 + z 1 ^ 2 := Fin.sum_univ_two _
      have hle : z 1 ^ 2 ≤ 1 := by linarith [hsum1, h2, sq_nonneg (z 0)]
      have hle2 : z 1 ^ 2 ≤ (1 : ℝ) ^ 2 := by rw [one_pow]; exact hle
      have habs := sq_le_sq.mp hle2
      rwa [abs_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)] at habs
  have hDzD : |(1 + s * z k) - D| ≤ δ := by
    have e : (1 + s * z k) - D = s * (z k - W k) := by linarith [hDdef]
    rw [e]; exact hSx
  have hDznn : (0 : ℝ) ≤ 1 + s * z k := le_of_lt hDzpos
  have hDnn : (0 : ℝ) ≤ D := le_of_lt hDpos
  have hpoly : (1 + s * z k) + 1 ≤ (3 / 2) * D * (1 + s * z k) := by
    have h1 : (1 + s * z k) + 1 ≤ 2.175 * (1 + s * z k) := by linarith [hDz12]
    have h2 : 2.175 * (1 + s * z k) ≤ (3 / 2) * D * (1 + s * z k) := by
      have hpos : (0 : ℝ) ≤ (3 / 2) * (1 + s * z k) :=
        mul_nonneg (by norm_num) hDznn
      have hmul := mul_le_mul_of_nonneg_left (show (1.45 : ℝ) ≤ D from hD145) hpos
      linarith [hmul]
    linarith [h1, h2]
  have hTPabs : ∀ j, j ≠ k → |T j - P j| ≤ 3 * δ / 2 := by
    intro j hj
    have hMpos : (0 : ℝ) < D * (1 + s * z k) := mul_pos hDpos hDzpos
    have hNle : |(W j - z j) * (1 + s * z k) + z j * ((1 + s * z k) - D)|
        ≤ δ * ((1 + s * z k) + 1) := by
      have e1 := abs_add_le ((W j - z j) * (1 + s * z k)) (z j * ((1 + s * z k) - D))
      rw [abs_mul, abs_mul, abs_of_nonneg hDznn] at e1
      have m1 := mul_le_mul_of_nonneg_left (hw j) hDznn
      have m2a := mul_le_mul_of_nonneg_left (hz1 j) (abs_nonneg ((1 + s * z k) - D))
      have m2b := mul_le_mul_of_nonneg_left hDzD (show (0 : ℝ) ≤ 1 by norm_num)
      linarith [e1, m1, m2a, m2b]
    rw [heq j hj]
    have heq2 : |((W j - z j) * (1 + s * z k) + z j * ((1 + s * z k) - D)) / (D * (1 + s * z k))|
        ≤ 3 * δ / 2 := by
      rw [abs_div, abs_of_nonneg (le_of_lt hMpos), div_le_iff₀ hMpos]
      have hmul2 := mul_le_mul_of_nonneg_left hpoly hδnn
      linarith [hNle, hmul2]
    exact heq2
  have hTPsq : ∀ j, j ≠ k → (T j - P j) ^ 2 ≤ (3 * δ / 2) ^ 2 := by
    intro j hj
    have habs : |T j - P j| ≤ |3 * δ / 2| := by
      rw [abs_of_nonneg (by linarith [hδnn] : (0 : ℝ) ≤ 3 * δ / 2)]
      exact hTPabs j hj
    exact sq_le_sq.mpr habs
  have hSle : ∑ i, (T i - P i) ^ 2 ≤ (3 * δ / 2) ^ 2 := by
    have hpt : ∀ j : Fin 2, (T j - P j) ^ 2 ≤ (if j = k then (0 : ℝ) else (3 * δ / 2) ^ 2) := by
      intro j
      by_cases hj : j = k
      · subst hj
        simp only [hTk, hPk, eq_self_iff_true, ite_true]
        norm_num
      · simp only [hj, ite_false]
        exact hTPsq j hj
    have hle : (∑ j, (T j - P j) ^ 2) ≤ ∑ j, (if j = k then (0 : ℝ) else (3 * δ / 2) ^ 2) :=
      Finset.sum_le_sum (fun j _ => hpt j)
    have hite : ∑ j : Fin 2, (if j = k then (0 : ℝ) else (3 * δ / 2) ^ 2) = (3 * δ / 2) ^ 2 := by
      have hpt2 : ∀ j : Fin 2, (if j = k then (0 : ℝ) else (3 * δ / 2) ^ 2)
          = (3 * δ / 2) ^ 2 - (if j = k then (3 * δ / 2) ^ 2 else 0) := by
        intro j
        by_cases hj : j = k
        · subst hj; simp
        · simp [hj]
      simp_rw [hpt2]
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ite_true]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have h2n : ((2 : ℕ) : ℝ) = 2 := by norm_num
      rw [h2n]
      ring
    linarith [hle, hite]
  have hAB1 : (1 : ℝ) ≤ (1 + R) * (1 + Rz) := by
    have e : (1 + R) * (1 + Rz) - 1 = R + Rz + R * Rz := by ring
    have hnn : (0 : ℝ) ≤ R + Rz + R * Rz :=
      add_nonneg (add_nonneg hRnn hRznn) (mul_nonneg hRnn hRznn)
    linarith
  have hfin : ‖X - z‖ ≤ 3 * δ := by
    have hSnn : (0 : ℝ) ≤ ∑ i, (T i - P i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h4Snn : (0 : ℝ) ≤ 4 * (∑ i, (T i - P i) ^ 2) := by linarith [hSnn]
    have hle : 4 * (∑ i, (T i - P i) ^ 2) / ((1 + R) * (1 + Rz))
        ≤ 4 * (∑ i, (T i - P i) ^ 2) :=
      div_le_self h4Snn hAB1
    have h9 : 4 * (∑ i, (T i - P i) ^ 2) ≤ (3 * δ) ^ 2 := by
      have m := mul_le_mul_of_nonneg_left hSle (show (0 : ℝ) ≤ 4 by norm_num)
      linarith [m]
    have hsq : ‖X - z‖ ^ 2 ≤ (3 * δ) ^ 2 := by
      rw [hchord]
      linarith [hle, h9]
    have habs := sq_le_sq.mp hsq
    have hnn1 : (0 : ℝ) ≤ ‖X - z‖ := by positivity
    have hnn2 : (0 : ℝ) ≤ 3 * δ := by linarith [hδnn]
    rw [abs_of_nonneg hnn1, abs_of_nonneg hnn2] at habs
    exact habs
  rw [dist_eq_norm]
  exact hfin

/-- `S^1` snapping: per-coordinate input error `δ ≤ 1/4` gives distance at most `3 δ` when
the pole is opposite in sign to a largest-magnitude input coordinate. -/
theorem dist_stereoSnap_le_circle {z : EuclideanSpace ℝ (Fin 2)} (hz : ‖z‖ = 1)
    {w : Fin 2 → ℚ} {δ : ℝ} (hδ : δ ≤ 1 / 4) (hw : ∀ j, |(w j : ℝ) - z j| ≤ δ)
    {k : Fin 2} (hk : ∀ j, |w j| ≤ |w k|) :
    dist (toEuclid (stereoSnap w k)) z ≤ 3 * δ := by
  set sQ : ℚ := if 0 ≤ w k then 1 else -1 with hsQ
  set DQ : ℚ := 1 + sQ * w k with hDQ
  set TQ : Fin 2 → ℚ := fun j => if j = k then 0 else w j / DQ with hTQ
  set RQ : ℚ := ∑ j, (TQ j ^ 2) with hRQ
  have hs2 : sQ ^ 2 = 1 := by
    rw [hsQ]
    by_cases h : (0 : ℚ) ≤ w k
    · rw [ite_eq_left h]; norm_num
    · rw [ite_eq_right h]; norm_num
  have hs : ((sQ : ℚ) : ℝ) ^ 2 = 1 := by
    rw [hsQ]
    by_cases h : (0 : ℚ) ≤ w k
    · simp only [ite_eq_left h]
      push_cast
      norm_num
    · simp only [ite_eq_right h]
      push_cast
      norm_num
  have hsgnQ : sQ * w k = |w k| := by
    rw [hsQ]
    by_cases h : (0 : ℚ) ≤ w k
    · rw [ite_eq_left h, one_mul, abs_of_nonneg h]
    · rw [ite_eq_right h]
      have hneg : w k < 0 := lt_of_not_ge h
      rw [abs_of_neg hneg]
      ring
  have hwk : (0 : ℝ) ≤ ((sQ : ℚ) : ℝ) * ((w k : ℚ) : ℝ) := by
    rw [hsQ]
    by_cases h : (0 : ℚ) ≤ w k
    · simp only [ite_eq_left h]
      have hR : (0 : ℝ) ≤ ((w k : ℚ) : ℝ) := by exact_mod_cast h
      have h1 : (((1 : ℚ)) : ℝ) = 1 := by norm_cast
      rw [h1, one_mul]
      exact hR
    · simp only [ite_eq_right h]
      push_neg at h
      have hR : ((w k : ℚ) : ℝ) < 0 := by exact_mod_cast h
      have hm1 : (((-1 : ℚ)) : ℝ) = -1 := by norm_cast
      rw [hm1]
      have hle : ((w k : ℚ) : ℝ) ≤ 0 := le_of_lt hR
      linarith
  have hkR : ∀ j : Fin 2, |((w j : ℚ) : ℝ)| ≤ |((w k : ℚ) : ℝ)| := by
    intro j
    exact_mod_cast hk j
  have hTj : ∀ j : Fin 2, j ≠ k → (((TQ j : ℚ)) : ℝ) = ((w j : ℚ) : ℝ) / (((DQ : ℚ)) : ℝ) := by
    intro j hj
    rw [hTQ]
    simp only [hj, ite_false]
    exact_mod_cast rfl
  have hX : ∀ j : Fin 2, (toEuclid (stereoSnap w k)) j
      = (if j = k then ((sQ : ℚ) : ℝ) * (1 - ((RQ : ℚ) : ℝ)) / (1 + ((RQ : ℚ) : ℝ))
        else 2 * (((TQ j : ℚ)) : ℝ) / (1 + ((RQ : ℚ) : ℝ))) := by
    intro j
    show ((stereoSnap w k j : ℚ) : ℝ) = _
    by_cases hj : j = k
    · subst hj
      show ((if j = j then sQ * (1 - RQ) / (1 + RQ) else 2 * TQ j / (1 + RQ) : ℚ) : ℝ) = _
      simp only [eq_self_iff_true, ite_true]
      norm_cast
    · show ((if j = k then sQ * (1 - RQ) / (1 + RQ) else 2 * TQ j / (1 + RQ) : ℚ) : ℝ) = _
      simp only [hj, ite_false]
      norm_cast
  exact dist_circle_aux hz (fun j => ((w j : ℚ) : ℝ))
    ((sQ : ℚ) : ℝ) hs
    (((DQ : ℚ)) : ℝ) (by rw [hDQ]; push_cast; ring_nf)
    (fun j => (((TQ j : ℚ)) : ℝ))
    (by rw [hTQ]; simp only [eq_self_iff_true, ite_true]; norm_num) hTj
    (((RQ : ℚ)) : ℝ)
    (by rw [hRQ]; push_cast; simp only [])
    (toEuclid (stereoSnap w k)) hX δ hδ hw hkR hwk

/-- Real-analytic core of `S^3` snapping: the chordal estimate for a general pole.
All inputs are real; the caller supplies the rational approximations and casts. -/
private theorem dist_three_sphere_aux {k : Fin 4} {z : EuclideanSpace ℝ (Fin 4)} (hz : ‖z‖ = 1)
    (W : Fin 4 → ℝ) (s : ℝ) (hs : s ^ 2 = 1)
    (D : ℝ) (hDdef : D = 1 + s * W k)
    (T : Fin 4 → ℝ) (hTk : T k = 0) (hTj : ∀ j, j ≠ k → T j = W j / D)
    (R : ℝ) (hR : R = ∑ i, T i ^ 2)
    (X : EuclideanSpace ℝ (Fin 4))
    (hX : ∀ j, X j = (if j = k then s * (1 - R) / (1 + R) else 2 * T j / (1 + R)))
    (δ : ℝ) (hδ : δ ≤ 1 / 8)
    (hw : ∀ j, |W j - z j| ≤ δ) (hk : ∀ j, |W j| ≤ |W k|)
    (hwk : (0 : ℝ) ≤ s * W k) :
    dist X z ≤ 4 * δ := by
  have hnorm2 : ∀ (m : ℕ) (x : EuclideanSpace ℝ (Fin m)),
      ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
    intro m x
    have hnn : (0 : ℝ) ≤ ∑ i, ‖x i‖ ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt hnn]
    simp only [Real.norm_eq_abs, sq_abs]
  have hsum1 : ∑ i, (z i) ^ 2 = 1 := by
    rw [← hnorm2 4 z, hz, one_pow]
  have hδnn : (0 : ℝ) ≤ δ := le_trans (abs_nonneg _) (hw k)
  have hs_pm : s = 1 ∨ s = -1 := by
    have hfac : (s - 1) * (s + 1) = 0 := by linear_combination hs
    rcases mul_eq_zero.mp hfac with h | h
    · left; linarith
    · right; linarith
  have hsgn : s * W k = |W k| := by
    rcases hs_pm with rfl | rfl
    · rw [one_mul]
      have hwknn : (0 : ℝ) ≤ W k := by linarith [hwk]
      rw [abs_of_nonneg hwknn]
    · have hwknn : W k ≤ 0 := by linarith [hwk]
      rw [abs_of_nonpos hwknn]
      ring
  have hRnn : (0 : ℝ) ≤ R := by
    rw [hR]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h1Rpos : (0 : ℝ) < 1 + R := by linarith [hRnn]
  have h1Rne : (1 : ℝ) + R ≠ 0 := ne_of_gt h1Rpos
  have htri : ∀ j, |z j| - δ ≤ |W k| := by
    intro j
    have h1 : |W j| ≤ |W k| := hk j
    have e1 : |z j| ≤ |z j - W j| + |W j| := by
      have := abs_add_le (z j - W j) (W j)
      rwa [sub_add_cancel] at this
    have e2 : |z j - W j| = |W j - z j| := by
      have : z j - W j = -(W j - z j) := by ring
      rw [this, abs_neg]
    linarith [hw j]
  have hWk38 : (0.375 : ℝ) ≤ |W k| := by
    have hmax : ∃ j, (0.5 : ℝ) ≤ |z j| := by
      by_contra hc
      push_neg at hc
      have hlt : ∀ j : Fin 4, (z j) ^ 2 < (0.25 : ℝ) := by
        intro j
        have h1 : |z j| < |(0.5 : ℝ)| := by
          rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.5)]
          exact hc j
        have e := sq_lt_sq.mpr h1
        have h25 : (0.5 : ℝ) ^ 2 = 0.25 := by norm_num
        rwa [h25] at e
      have hle : ∀ i ∈ (Finset.univ : Finset (Fin 4)), (z i) ^ 2 ≤ (0.25 : ℝ) :=
        fun i _ => le_of_lt (hlt i)
      have hex : ∃ i ∈ (Finset.univ : Finset (Fin 4)), (z i) ^ 2 < (0.25 : ℝ) :=
        ⟨0, Finset.mem_univ 0, hlt 0⟩
      have hsum := Finset.sum_lt_sum hle hex
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
      have h4n : ((4 : ℕ) : ℝ) = 4 := by norm_num
      rw [h4n] at hsum
      norm_num at hsum
      linarith [hsum1, hsum]
    obtain ⟨j, hj⟩ := hmax
    linarith [htri j, hj, hδ]
  have hD1375 : (1.375 : ℝ) ≤ D := by linarith [hDdef, hsgn, hWk38]
  have hDpos : (0 : ℝ) < D := by linarith [hD1375]
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hSx : |s * (z k - W k)| ≤ δ := by
    have hx : |z k - W k| ≤ δ := by
      have e : |z k - W k| = |W k - z k| := by
        have : z k - W k = -(W k - z k) := by ring
        rw [this, abs_neg]
      rw [e]; exact hw k
    have hsq : (s * (z k - W k)) ^ 2 ≤ δ ^ 2 := by
      have h2 : (s * (z k - W k)) ^ 2 = (z k - W k) ^ 2 := by
        rw [mul_pow, hs, one_mul]
      have h3 : (z k - W k) ^ 2 ≤ δ ^ 2 := by
        have habs : |z k - W k| ≤ |δ| := by
          rw [abs_of_nonneg hδnn]; exact hx
        exact sq_le_sq.mpr habs
      rw [h2]; exact h3
    have habs2 := sq_le_sq.mp hsq
    rwa [abs_of_nonneg hδnn] at habs2
  have hSx_neg : -δ ≤ s * (z k - W k) := by
    by_cases hnn : (0 : ℝ) ≤ s * (z k - W k)
    · linarith [hδnn]
    · push_neg at hnn
      have e : |s * (z k - W k)| = -(s * (z k - W k)) := abs_of_neg hnn
      linarith [hSx, e]
  have hDz125 : (1.25 : ℝ) ≤ 1 + s * z k := by
    have h1 : s * z k = s * W k + s * (z k - W k) := by ring
    linarith [h1, hsgn, hWk38, hSx_neg, hδ]
  have hDzpos : (0 : ℝ) < 1 + s * z k := by linarith [hDz125]
  have hDzne : (1 : ℝ) + s * z k ≠ 0 := ne_of_gt hDzpos
  have hDz2ne : ((1 : ℝ) + s * z k) ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_ne_zero hDzne hDzne
  set P : Fin 4 → ℝ := fun j => if j = k then 0 else z j / (1 + s * z k) with hP
  set Rz : ℝ := ∑ i, P i ^ 2 with hRz
  have hPk : P k = 0 := by simp only [hP, eq_self_iff_true, ite_true]
  have hPj : ∀ j, j ≠ k → P j = z j / (1 + s * z k) := by
    intro j hj
    simp only [hP, hj, ite_false]
  have hRznn : (0 : ℝ) ≤ Rz := by
    rw [hRz]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h1Rzpos : (0 : ℝ) < 1 + Rz := by linarith [hRznn]
  have h1Rzne : (1 : ℝ) + Rz ≠ 0 := ne_of_gt h1Rzpos
  have hABne : (1 + R) * (1 + Rz) ≠ 0 := mul_ne_zero h1Rne h1Rzne
  have hAB2ne : ((1 + R) * (1 + Rz)) ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_ne_zero hABne hABne
  have htsqz : ∀ i : Fin 4, P i ^ 2
      = (z i / (1 + s * z k)) ^ 2
        - (if i = k then (z i / (1 + s * z k)) ^ 2 else 0) := by
    intro i
    by_cases hi : i = k
    · subst hi
      simp only [hPk, eq_self_iff_true, ite_true, sub_self]
      norm_num
    · simp only [hi, ite_false, hPj i hi, sub_zero]
  have hsumz : ∑ i, (z i / (1 + s * z k)) ^ 2 = 1 / (1 + s * z k) ^ 2 := by
    have h1 : ∀ i : Fin 4,
        (z i / (1 + s * z k)) ^ 2 = (z i ^ 2) * (1 / (1 + s * z k) ^ 2) := by
      intro i
      field_simp
    simp_rw [h1, ← Finset.sum_mul, hsum1, one_mul]
  have hRz_eq : Rz = (1 - z k ^ 2) / (1 + s * z k) ^ 2 := by
    rw [hRz]
    simp_rw [htsqz]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    rw [hsumz]
    field_simp
  have hmulz : (1 + Rz) * (1 + s * z k) ^ 2 = 2 * (1 + s * z k) := by
    rw [hRz_eq, add_mul, one_mul, div_mul_cancel₀ _ hDz2ne]
    linear_combination z k ^ 2 * hs
  rw [pow_two, ← mul_assoc] at hmulz
  have hDrz : (1 + Rz) * (1 + s * z k) = 2 := mul_right_cancel₀ hDzne hmulz
  have hzk : z k = s * (1 - Rz) / (1 + Rz) := by
    have e : (s * (1 - Rz)) * (1 + s * z k) ^ 2
        = (z k * (1 + Rz)) * (1 + s * z k) ^ 2 := by
      rw [hRz_eq, mul_assoc, mul_assoc, sub_mul, one_mul, div_mul_cancel₀ _ hDz2ne,
        add_mul, one_mul, div_mul_cancel₀ _ hDz2ne]
      linear_combination (2 * z k + s * z k ^ 2 - z k ^ 3) * hs
    have e2 := mul_right_cancel₀ hDz2ne e
    field_simp
    linarith [e2]
  have hzj : ∀ j, j ≠ k → z j = 2 * P j / (1 + Rz) := by
    intro j hj
    have e1 : (2 * (z j / (1 + s * z k))) * (1 + s * z k) = 2 * z j := by
      rw [mul_assoc, div_mul_cancel₀ _ hDzne]
    have e2 : (z j * (1 + Rz)) * (1 + s * z k) = 2 * z j := by
      rw [mul_assoc, hDrz]
      ring
    have e : (2 * (z j / (1 + s * z k))) * (1 + s * z k)
        = (z j * (1 + Rz)) * (1 + s * z k) := by
      rw [e1, e2]
    have hcan := mul_right_cancel₀ hDzne e
    rw [hPj j hj]
    field_simp
    linarith [hcan]
  have hdiffXk : X k - z k
      = s * (1 - R) / (1 + R) - s * (1 - Rz) / (1 + Rz) := by
    rw [hX k, ite_eq_left rfl, hzk]
  have hdiffXj : ∀ j, j ≠ k → X j - z j = 2 * T j / (1 + R) - 2 * P j / (1 + Rz) := by
    intro j hj
    rw [hX j, ite_eq_right hj, hzj j hj]
  have hC : ∀ j : Fin 4, (X j - z j) ^ 2
      = (2 * T j / (1 + R) - 2 * P j / (1 + Rz)) ^ 2
        + (if j = k then (s * (1 - R) / (1 + R) - s * (1 - Rz) / (1 + Rz)) ^ 2
          - (2 * T k / (1 + R) - 2 * P k / (1 + Rz)) ^ 2 else 0) := by
    intro j
    by_cases hj : j = k
    · subst hj
      simp only [eq_self_iff_true, ite_true]
      rw [hdiffXk]
      abel
    · simp only [hj, ite_false]
      rw [hdiffXj j hj, add_zero]
  have hTk0 : (2 * T k / (1 + R) - 2 * P k / (1 + Rz)) ^ 2 = 0 := by
    rw [hTk, hPk]
    norm_num
  have hchord : ‖X - z‖ ^ 2
      = 4 * (∑ i, (T i - P i) ^ 2) / ((1 + R) * (1 + Rz)) := by
    have hsplit2 : ‖X - z‖ ^ 2
        = (s * (1 - R) / (1 + R) - s * (1 - Rz) / (1 + Rz)) ^ 2
          + ∑ j : Fin 4, (2 * T j / (1 + R) - 2 * P j / (1 + Rz)) ^ 2 := by
      rw [hnorm2]
      have hsub : ∀ i : Fin 4, ((X - z) i) = (X i - z i) := fun i => by simp
      simp_rw [hsub, hC]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ite_true]
      rw [hTk0, sub_zero, add_comm]
    have hA : (s * (1 - R) / (1 + R) - s * (1 - Rz) / (1 + Rz)) ^ 2
        = 4 * (Rz - R) ^ 2 / ((1 + R) * (1 + Rz)) ^ 2 := by
      have hs2 : (s * (1 - R) / (1 + R) - s * (1 - Rz) / (1 + Rz))
          = s * ((1 - R) / (1 + R) - (1 - Rz) / (1 + Rz)) := by ring
      rw [hs2, mul_pow, hs, one_mul]
      field_simp
      ring
    have hB : ∀ j : Fin 4, (2 * T j / (1 + R) - 2 * P j / (1 + Rz)) ^ 2
        = 4 * ((1 + Rz) * T j - (1 + R) * P j) ^ 2 / ((1 + R) * (1 + Rz)) ^ 2 := by
      intro j
      field_simp
      ring
    have hCsum : ∑ j : Fin 4, (2 * T j / (1 + R) - 2 * P j / (1 + Rz)) ^ 2
        = (∑ j : Fin 4, ((1 + Rz) * T j - (1 + R) * P j) ^ 2)
          * (4 / ((1 + R) * (1 + Rz)) ^ 2) := by
      have hfac : ∀ j : Fin 4,
          4 * ((1 + Rz) * T j - (1 + R) * P j) ^ 2 / ((1 + R) * (1 + Rz)) ^ 2
          = (((1 + Rz) * T j - (1 + R) * P j) ^ 2) * (4 / ((1 + R) * (1 + Rz)) ^ 2) := by
        intro j
        rw [← mul_div_assoc, mul_comm _ 4]
      simp_rw [hB, hfac, ← Finset.sum_mul]
    have hexp : ∀ j : Fin 4, ((1 + Rz) * T j - (1 + R) * P j) ^ 2
        = (T j ^ 2) * ((1 + Rz) ^ 2) - (T j * P j) * (2 * ((1 + R) * (1 + Rz)))
          + (P j ^ 2) * ((1 + R) ^ 2) := by
      intro j
      ring
    have hexpS : ∀ j : Fin 4, (T j - P j) ^ 2
        = (T j ^ 2) - (T j * P j) * 2 + (P j ^ 2) := by
      intro j
      ring
    have hsumY : ∑ j : Fin 4, ((1 + Rz) * T j - (1 + R) * P j) ^ 2
        = R * ((1 + Rz) ^ 2) - (∑ i, T i * P i) * (2 * ((1 + R) * (1 + Rz)))
          + Rz * ((1 + R) ^ 2) := by
      simp_rw [hexp]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        ← Finset.sum_mul, ← hR, ← hRz]
    have hsumS : ∑ j : Fin 4, (T j - P j) ^ 2
        = R - (∑ i, T i * P i) * 2 + Rz := by
      simp_rw [hexpS]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← hR, ← hRz]
    have hcore : (Rz - R) ^ 2 + ∑ j : Fin 4, ((1 + Rz) * T j - (1 + R) * P j) ^ 2
        = (∑ j : Fin 4, (T j - P j) ^ 2) * ((1 + R) * (1 + Rz)) := by
      rw [hsumY, hsumS]
      ring
    have hnum : 4 * (Rz - R) ^ 2
          + (∑ j : Fin 4, ((1 + Rz) * T j - (1 + R) * P j) ^ 2) * 4
        = 4 * ((∑ j : Fin 4, (T j - P j) ^ 2) * ((1 + R) * (1 + Rz))) := by
      linear_combination 4 * hcore
    rw [hsplit2, hA, hCsum, ← mul_div_assoc, ← add_div, hnum]
    field_simp
  have hDDne : D * (1 + s * z k) ≠ 0 := mul_ne_zero hDne hDzne
  have heq : ∀ j, j ≠ k → T j - P j
      = ((W j - z j) * (1 + s * z k) + z j * ((1 + s * z k) - D)) / (D * (1 + s * z k)) := by
    intro j hj
    rw [hTj j hj, hPj j hj]
    field_simp
    ring
  have hsumAbs2 : ∑ j, |z j| ^ 2 = 1 := by
    simp_rw [sq_abs]
    exact hsum1
  have hDzD : |(1 + s * z k) - D| ≤ δ := by
    have e : (1 + s * z k) - D = s * (z k - W k) := by linarith [hDdef]
    rw [e]; exact hSx
  have hDznn : (0 : ℝ) ≤ 1 + s * z k := le_of_lt hDzpos
  have hDnn : (0 : ℝ) ≤ D := le_of_lt hDpos
  have hTPabs4 : ∀ j, j ≠ k → |T j - P j| ≤ δ * ((1 + s * z k) + |z j|) / (D * (1 + s * z k)) := by
    intro j hj
    have hMpos : (0 : ℝ) < D * (1 + s * z k) := mul_pos hDpos hDzpos
    have hNle : |(W j - z j) * (1 + s * z k) + z j * ((1 + s * z k) - D)|
        ≤ δ * ((1 + s * z k) + |z j|) := by
      have e1 := abs_add_le ((W j - z j) * (1 + s * z k)) (z j * ((1 + s * z k) - D))
      rw [abs_mul, abs_mul, abs_of_nonneg hDznn] at e1
      have m1 := mul_le_mul_of_nonneg_left (hw j) hDznn
      have m2 := mul_le_mul_of_nonneg_left hDzD (abs_nonneg (z j))
      linarith [e1, m1, m2]
    rw [heq j hj, abs_div, abs_of_nonneg (le_of_lt hMpos), div_le_iff₀ hMpos,
      div_mul_cancel₀ _ (ne_of_gt hMpos)]
    exact hNle
  have hTPsq4 : ∀ j, j ≠ k
      → (T j - P j) ^ 2 ≤ ((1 + s * z k) + |z j|) ^ 2 * (δ ^ 2 / ((D * (1 + s * z k)) ^ 2)) := by
    intro j hj
    have hnn : (0 : ℝ) ≤ δ * ((1 + s * z k) + |z j|) / (D * (1 + s * z k)) :=
      div_nonneg (mul_nonneg hδnn (add_nonneg hDznn (abs_nonneg _))) (le_of_lt (mul_pos hDpos hDzpos))
    have habs : |T j - P j| ≤ |δ * ((1 + s * z k) + |z j|) / (D * (1 + s * z k))| := by
      rw [abs_of_nonneg hnn]
      exact hTPabs4 j hj
    have hle := sq_le_sq.mpr habs
    have heq2 : (δ * ((1 + s * z k) + |z j|) / (D * (1 + s * z k))) ^ 2
        = ((1 + s * z k) + |z j|) ^ 2 * (δ ^ 2 / ((D * (1 + s * z k)) ^ 2)) := by
      rw [div_pow, mul_pow]
      ring
    rwa [heq2] at hle
  have hSumAux : ∑ j, (if j = k then (0 : ℝ) else ((1 + s * z k) + |z j|) ^ 2)
      ≤ 3 * (1 + s * z k) ^ 2 + 4 * (1 + s * z k) + 1 := by
    have hsplit : ∀ j : Fin 4, (if j = k then (0 : ℝ) else ((1 + s * z k) + |z j|) ^ 2)
        = ((1 + s * z k) + |z j|) ^ 2 - (if j = k then ((1 + s * z k) + |z j|) ^ 2 else 0) := by
      intro j
      by_cases hj : j = k
      · subst hj; simp
      · simp [hj]
    simp_rw [hsplit]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    have hexp : ∀ j : Fin 4, ((1 + s * z k) + |z j|) ^ 2
        = (1 + s * z k) ^ 2 + |z j| * (2 * (1 + s * z k)) + |z j| ^ 2 := by
      intro j; ring
    simp_rw [hexp]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
    have hconst : (∑ _ : Fin 4, (1 + s * z k) ^ 2) = 4 * (1 + s * z k) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have h4n : ((4 : ℕ) : ℝ) = 4 := by norm_num
      rw [h4n]
    rw [hconst, hsumAbs2]
    have hsum2 : ∑ j, |z j| ≤ 2 := by
      have h1 : (∑ j, |z j|) ^ 2 ≤ (2 : ℝ) ^ 2 := by
        have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => |z j|) (fun _ => (1 : ℝ))
        have eL : (∑ i ∈ (Finset.univ : Finset (Fin 4)), |z i| * 1) = ∑ j, |z j| := by
          simp only [mul_one]
        have eR1 : (∑ i ∈ (Finset.univ : Finset (Fin 4)), |z i| ^ 2) = 1 := hsumAbs2
        have eR2 : (∑ i ∈ (Finset.univ : Finset (Fin 4)), (1 : ℝ) ^ 2) = 4 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have h4n : ((4 : ℕ) : ℝ) = 4 := by norm_num
          rw [h4n]
          norm_num
        rw [eL, eR1, eR2] at hCS
        norm_num at hCS ⊢
        exact hCS
      have habs := sq_le_sq.mp h1
      rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _)),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at habs
      exact habs
    have hpole : (1 + s * z k) ^ 2 ≤ ((1 + s * z k) + |z k|) ^ 2 := by
      linarith [mul_nonneg hDznn (abs_nonneg (z k)), sq_nonneg (|z k| : ℝ)]
    have hmid2 : (∑ j, |z j|) * (2 * (1 + s * z k)) ≤ 4 * (1 + s * z k) := by
      have h2X : (0 : ℝ) ≤ 2 * (1 + s * z k) := by linarith [hDznn]
      have h1 := mul_le_mul_of_nonneg_left hsum2 h2X
      linear_combination h1
    linarith [hmid2, hpole]
  have hSle4 : ∑ i, (T i - P i) ^ 2 ≤ 4 * δ ^ 2 := by
    have hpt : ∀ j : Fin 4, (T j - P j) ^ 2
        ≤ (if j = k then (0 : ℝ)
          else ((1 + s * z k) + |z j|) ^ 2 * (δ ^ 2 / ((D * (1 + s * z k)) ^ 2))) := by
      intro j
      by_cases hj : j = k
      · subst hj
        simp only [hTk, hPk, eq_self_iff_true, ite_true]
        norm_num
      · simp only [hj, ite_false]
        exact hTPsq4 j hj
    have hle : (∑ j, (T j - P j) ^ 2)
        ≤ ∑ j, (if j = k then (0 : ℝ)
          else ((1 + s * z k) + |z j|) ^ 2 * (δ ^ 2 / ((D * (1 + s * z k)) ^ 2))) :=
      Finset.sum_le_sum (fun j _ => hpt j)
    have hfactor : ∀ j : Fin 4,
        (if j = k then (0 : ℝ)
          else ((1 + s * z k) + |z j|) ^ 2 * (δ ^ 2 / ((D * (1 + s * z k)) ^ 2)))
        = (if j = k then (0 : ℝ) else ((1 + s * z k) + |z j|) ^ 2)
          * (δ ^ 2 / ((D * (1 + s * z k)) ^ 2)) := by
      intro j
      by_cases hj : j = k
      · simp [hj]
      · simp only [hj, ite_false]
    simp_rw [hfactor] at hle
    rw [← Finset.sum_mul] at hle
    have hfac_nn : (0 : ℝ) ≤ δ ^ 2 / ((D * (1 + s * z k)) ^ 2) :=
      div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hle2 : (∑ j, (if j = k then (0 : ℝ) else ((1 + s * z k) + |z j|) ^ 2))
          * (δ ^ 2 / ((D * (1 + s * z k)) ^ 2))
        ≤ (3 * (1 + s * z k) ^ 2 + 4 * (1 + s * z k) + 1) * (δ ^ 2 / ((D * (1 + s * z k)) ^ 2)) := by
      have h1 := mul_le_mul_of_nonneg_left hSumAux hfac_nn
      linear_combination h1
    have hkey : (3 * (1 + s * z k) ^ 2 + 4 * (1 + s * z k) + 1) * (δ ^ 2 / ((D * (1 + s * z k)) ^ 2))
        ≤ 4 * δ ^ 2 := by
      have hmain : 3 * (1 + s * z k) ^ 2 + 4 * (1 + s * z k) + 1
          ≤ 4 * D ^ 2 * (1 + s * z k) ^ 2 := by
        have hD2 : (1.375 : ℝ) ^ 2 ≤ D ^ 2 := by
          have h1 : (0 : ℝ) ≤ D - 1.375 := by linarith [hD1375]
          have h2 : (0 : ℝ) ≤ D + 1.375 := by linarith [hDpos]
          have h3 := mul_nonneg h1 h2
          have he : (D - 1.375) * (D + 1.375) = D ^ 2 - (1.375 : ℝ) ^ 2 := by ring
          linarith [h3, he]
        have hXX : (1.25 : ℝ) * (1 + s * z k) ≤ (1 + s * z k) ^ 2 := by
          have h1 := mul_le_mul_of_nonneg_left hDz125 (le_of_lt hDzpos)
          linear_combination h1
        have e1 : (7.5625 : ℝ) * (1 + s * z k) ^ 2 ≤ 4 * D ^ 2 * (1 + s * z k) ^ 2 := by
          have h1 := mul_le_mul_of_nonneg_left hD2
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg (1 + s * z k)))
          have h2 : (1.375 : ℝ) ^ 2 = 1.890625 := by norm_num
          rw [h2] at h1
          linear_combination h1
        have e2 : 3 * (1 + s * z k) ^ 2 + 4 * (1 + s * z k) + 1
            ≤ (7.5625 : ℝ) * (1 + s * z k) ^ 2 := by
          linarith [hXX, hDz125]
        linarith [e1, e2]
      have h3 : (3 * (1 + s * z k) ^ 2 + 4 * (1 + s * z k) + 1) * (δ ^ 2 / ((D * (1 + s * z k)) ^ 2))
          ≤ (4 * D ^ 2 * (1 + s * z k) ^ 2) * (δ ^ 2 / ((D * (1 + s * z k)) ^ 2)) := by
        have h1 := mul_le_mul_of_nonneg_left hmain hfac_nn
        linear_combination h1
      have h4 : (4 * D ^ 2 * (1 + s * z k) ^ 2) * (δ ^ 2 / ((D * (1 + s * z k)) ^ 2)) = 4 * δ ^ 2 := by
        have hDXne : D * (1 + s * z k) ≠ 0 := ne_of_gt (mul_pos hDpos hDzpos)
        have hne : ((D * (1 + s * z k)) ^ 2) ≠ 0 := by
          rw [pow_two]
          exact mul_ne_zero hDXne hDXne
        field_simp
      rw [h4] at h3
      exact h3
    exact le_trans hle (le_trans hle2 hkey)
  have hAB1 : (1 : ℝ) ≤ (1 + R) * (1 + Rz) := by
    have e : (1 + R) * (1 + Rz) - 1 = R + Rz + R * Rz := by ring
    have hnn : (0 : ℝ) ≤ R + Rz + R * Rz :=
      add_nonneg (add_nonneg hRnn hRznn) (mul_nonneg hRnn hRznn)
    linarith
  have hfin : ‖X - z‖ ≤ 4 * δ := by
    have hSnn : (0 : ℝ) ≤ ∑ i, (T i - P i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h4Snn : (0 : ℝ) ≤ 4 * (∑ i, (T i - P i) ^ 2) := by linarith [hSnn]
    have hle : 4 * (∑ i, (T i - P i) ^ 2) / ((1 + R) * (1 + Rz))
        ≤ 4 * (∑ i, (T i - P i) ^ 2) :=
      div_le_self h4Snn hAB1
    have h9 : 4 * (∑ i, (T i - P i) ^ 2) ≤ (4 * δ) ^ 2 := by
      have m := mul_le_mul_of_nonneg_left hSle4 (show (0 : ℝ) ≤ 4 by norm_num)
      linarith [m]
    have hsq : ‖X - z‖ ^ 2 ≤ (4 * δ) ^ 2 := by
      rw [hchord]
      linarith [hle, h9]
    have habs := sq_le_sq.mp hsq
    have hnn1 : (0 : ℝ) ≤ ‖X - z‖ := by positivity
    have hnn2 : (0 : ℝ) ≤ 4 * δ := by linarith [hδnn]
    rw [abs_of_nonneg hnn1, abs_of_nonneg hnn2] at habs
    exact habs
  rw [dist_eq_norm]
  exact hfin

/-- `S^3` snapping: per-coordinate input error `δ ≤ 1/8` gives distance at most `4 δ`. -/
theorem dist_stereoSnap_le_three_sphere {z : EuclideanSpace ℝ (Fin 4)} (hz : ‖z‖ = 1)
    {w : Fin 4 → ℚ} {δ : ℝ} (hδ : δ ≤ 1 / 8) (hw : ∀ j, |(w j : ℝ) - z j| ≤ δ)
    {k : Fin 4} (hk : ∀ j, |w j| ≤ |w k|) :
    dist (toEuclid (stereoSnap w k)) z ≤ 4 * δ := by
  set sQ : ℚ := if 0 ≤ w k then 1 else -1 with hsQ
  set DQ : ℚ := 1 + sQ * w k with hDQ
  set TQ : Fin 4 → ℚ := fun j => if j = k then 0 else w j / DQ with hTQ
  set RQ : ℚ := ∑ j, (TQ j ^ 2) with hRQ
  have hs2 : sQ ^ 2 = 1 := by
    rw [hsQ]
    by_cases h : (0 : ℚ) ≤ w k
    · rw [ite_eq_left h]; norm_num
    · rw [ite_eq_right h]; norm_num
  have hs : ((sQ : ℚ) : ℝ) ^ 2 = 1 := by
    rw [hsQ]
    by_cases h : (0 : ℚ) ≤ w k
    · simp only [ite_eq_left h]
      push_cast
      norm_num
    · simp only [ite_eq_right h]
      push_cast
      norm_num
  have hsgnQ : sQ * w k = |w k| := by
    rw [hsQ]
    by_cases h : (0 : ℚ) ≤ w k
    · rw [ite_eq_left h, one_mul, abs_of_nonneg h]
    · rw [ite_eq_right h]
      have hneg : w k < 0 := lt_of_not_ge h
      rw [abs_of_neg hneg]
      ring
  have hwk : (0 : ℝ) ≤ ((sQ : ℚ) : ℝ) * ((w k : ℚ) : ℝ) := by
    rw [hsQ]
    by_cases h : (0 : ℚ) ≤ w k
    · simp only [ite_eq_left h]
      have hR : (0 : ℝ) ≤ ((w k : ℚ) : ℝ) := by exact_mod_cast h
      have h1 : (((1 : ℚ)) : ℝ) = 1 := by norm_cast
      rw [h1, one_mul]
      exact hR
    · simp only [ite_eq_right h]
      push_neg at h
      have hR : ((w k : ℚ) : ℝ) < 0 := by exact_mod_cast h
      have hm1 : (((-1 : ℚ)) : ℝ) = -1 := by norm_cast
      rw [hm1]
      have hle : ((w k : ℚ) : ℝ) ≤ 0 := le_of_lt hR
      linarith
  have hkR : ∀ j : Fin 4, |((w j : ℚ) : ℝ)| ≤ |((w k : ℚ) : ℝ)| := by
    intro j
    exact_mod_cast hk j
  have hTj : ∀ j : Fin 4, j ≠ k → (((TQ j : ℚ)) : ℝ) = ((w j : ℚ) : ℝ) / (((DQ : ℚ)) : ℝ) := by
    intro j hj
    rw [hTQ]
    simp only [hj, ite_false]
    exact_mod_cast rfl
  have hX : ∀ j : Fin 4, (toEuclid (stereoSnap w k)) j
      = (if j = k then ((sQ : ℚ) : ℝ) * (1 - ((RQ : ℚ) : ℝ)) / (1 + ((RQ : ℚ) : ℝ))
        else 2 * (((TQ j : ℚ)) : ℝ) / (1 + ((RQ : ℚ) : ℝ))) := by
    intro j
    show ((stereoSnap w k j : ℚ) : ℝ) = _
    by_cases hj : j = k
    · subst hj
      show ((if j = j then sQ * (1 - RQ) / (1 + RQ) else 2 * TQ j / (1 + RQ) : ℚ) : ℝ) = _
      simp only [eq_self_iff_true, ite_true]
      norm_cast
    · show ((if j = k then sQ * (1 - RQ) / (1 + RQ) else 2 * TQ j / (1 + RQ) : ℚ) : ℝ) = _
      simp only [hj, ite_false]
      norm_cast
  exact dist_three_sphere_aux hz (fun j => ((w j : ℚ) : ℝ))
    ((sQ : ℚ) : ℝ) hs
    (((DQ : ℚ)) : ℝ) (by rw [hDQ]; push_cast; ring_nf)
    (fun j => (((TQ j : ℚ)) : ℝ))
    (by rw [hTQ]; simp only [eq_self_iff_true, ite_true]; norm_num) hTj
    (((RQ : ℚ)) : ℝ)
    (by rw [hRQ]; push_cast; simp only [])
    (toEuclid (stereoSnap w k)) hX δ hδ hw hkR hwk

/-- Circle snap inherits the three-delta circle bound. -/
theorem dist_snap_le_circle {z : EuclideanSpace ℝ (Fin 2)} (hz : ‖z‖ = 1) {w : Fin 2 → ℚ}
    {δ : ℝ} (hδ : δ ≤ 1 / 4) (hw : ∀ j, |(w j : ℝ) - z j| ≤ δ) :
    dist (toEuclid (snap w)) z ≤ 3 * δ :=
  dist_stereoSnap_le_circle hz hδ hw (abs_le_abs_poleIndex w)

/-- Three-sphere snap inherits the four-delta sphere bound. -/
theorem dist_snap_le_three_sphere {z : EuclideanSpace ℝ (Fin 4)} (hz : ‖z‖ = 1)
    {w : Fin 4 → ℚ} {δ : ℝ} (hδ : δ ≤ 1 / 8) (hw : ∀ j, |(w j : ℝ) - z j| ≤ δ) :
    dist (toEuclid (snap w)) z ≤ 4 * δ :=
  dist_stereoSnap_le_three_sphere hz hδ hw (abs_le_abs_poleIndex w)

end MathlibExt.Quantum.RationalSnapping
